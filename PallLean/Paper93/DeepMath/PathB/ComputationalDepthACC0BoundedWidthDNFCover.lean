import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TreeDNFFullCover
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ClauseTree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DTreeBridge

/-!
# Syntactic bounded-width DNF compiles to a full switching cover

This file discharges the representation step left by `…TreeDNFFullCover`.  An ordinary syntactic
`Rung4DNF` is a list of conjunctions of signed literals.  Each term is compiled by the existing
proved `DTree.termTree`, then bridged to `BoolDecisionTree`.  Semantics and depth are preserved:

* one residual tree per syntactic DNF term;
* exact OR-of-terms acceptance in both directions;
* residual depth at most the syntactic term width `w`.

Thus an `L`-term width-`w` DNF top gives full-cover work `L*2^w`.  If `L≤2^q` and
`q+w≤(r+k)-s`, this is a genuine active-normalized `s`-bit exponent saving.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BoundedWidthDNFCover

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ACC0OracleControl
open PallLean.Paper93.DeepMath.PathB.ACC0SeparatorPivotBranching
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCoverCashout
open PallLean.Paper93.DeepMath.PathB.ACC0TreeDNFFullCover
open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.ACC0DTreeBridge

variable {r k : ℕ}

/-- Bridge the recursive syntactic term evaluator to the `List.all` semantics used by `termTree`. -/
theorem evalLits_eq_all_local (lits : List (Rung4Literal k)) (y : Fin k → Bool) :
    Rung4DNFTerm.evalLits lits y = lits.all (fun lit => lit.eval y) := by
  induction lits with
  | nil => rfl
  | cons lit rest ih => rw [Rung4DNFTerm.evalLits, List.all_cons, ih]

/-- A list-DNF is true exactly when one indexed term is true. -/
theorem evalTerms_eq_true_iff (ts : List (Rung4DNFTerm k)) (y : Fin k → Bool) :
    Rung4DNF.evalTerms ts y = true ↔
      ∃ i : Fin ts.length, (ts.get i).eval y = true := by
  have hmem : Rung4DNF.evalTerms ts y = true ↔
      ∃ T ∈ ts, T.eval y = true := by
    induction ts with
    | nil => simp [Rung4DNF.evalTerms]
    | cons T rest ih => simp [Rung4DNF.evalTerms, ih]
  rw [hmem]
  exact List.exists_mem_iff_get

/-- Compile a syntactic DNF top into the Tree-DNF full-cover representation, preserving term count
and bounding every residual tree by the syntactic width. -/
def dnfRepresentation (C : OracleControl k) (D : Rung4DNF k) (w : ℕ)
    (hcontrol : ∀ y, controlEval C y = D.eval y)
    (hwidth : ∀ T ∈ D.terms, T.width ≤ w) : TreeDNFRepresentation C where
  termCount := D.terms.length
  depthBound := w
  term := fun i => toBoolDT (DTree.termTree (D.terms.get i).lits)
  eval_iff := by
    intro y
    rw [hcontrol]
    unfold Rung4DNF.eval
    rw [evalTerms_eq_true_iff]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      rw [toBoolDT_eval, DTree.termTree_eval, ← evalLits_eq_all_local]
      simpa [Rung4DNFTerm.eval] using hi
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      rw [toBoolDT_eval, DTree.termTree_eval, ← evalLits_eq_all_local] at hi
      simpa [Rung4DNFTerm.eval] using hi
  termDepth := by
    intro i
    rw [toBoolDT_depth]
    exact (DTree.termTree_depth (D.terms.get i).lits).trans
      (hwidth (D.terms.get i) (List.get_mem D.terms i))

/-- The syntactic DNF produces a concrete full semantic switching cover. -/
def dnfSwitchingCover (C : SeparatorPivotCircuit r k) (D : Rung4DNF k) (w q : ℕ)
    (hcontrol : ∀ y, controlEval C.top y = D.eval y)
    (hwidth : ∀ T ∈ D.terms, T.width ≤ w)
    (hterms : D.terms.length ≤ 2 ^ q) : SwitchingCover C :=
  toSwitchingCover C (dnfRepresentation C.top D w hcontrol hwidth) q hterms

/-- Exact work of the compiled bounded-width DNF cover. -/
theorem dnf_cover_work_eq (C : SeparatorPivotCircuit r k) (D : Rung4DNF k) (w q : ℕ)
    (hcontrol : ∀ y, controlEval C.top y = D.eval y)
    (hwidth : ∀ T ∈ D.terms, T.width ≤ w)
    (hterms : D.terms.length ≤ 2 ^ q) :
    coverWork (dnfSwitchingCover C D w q hcontrol hwidth hterms) =
      D.terms.length * 2 ^ w := rfl

/-- **Active-normalized bounded-width DNF speedup.** -/
theorem boundedWidthDNF_active_speedup (C : SeparatorPivotCircuit r k)
    (D : Rung4DNF k) (w q saving : ℕ)
    (hcontrol : ∀ y, controlEval C.top y = D.eval y)
    (hwidth : ∀ T ∈ D.terms, T.width ≤ w)
    (hterms : D.terms.length ≤ 2 ^ q)
    (hpos : 0 < saving) (hs : saving ≤ r + k)
    (hbudget : q + w ≤ (r + k) - saving) :
    coverWork (dnfSwitchingCover C D w q hcontrol hwidth hterms) < 2 ^ (r + k) :=
  treeDNF_active_speedup C (dnfRepresentation C.top D w hcontrol hwidth)
    q saving hterms hpos hs hbudget

end PallLean.Paper93.DeepMath.PathB.ACC0BoundedWidthDNFCover

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundedWidthDNFCover.evalTerms_eq_true_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundedWidthDNFCover.evalLits_eq_all_local
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundedWidthDNFCover.dnfRepresentation
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundedWidthDNFCover.dnfSwitchingCover
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundedWidthDNFCover.boundedWidthDNF_active_speedup
