import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseAdapter

/-!
# The `canonicalDT` computes `D` bridge

The depth-based switching count (`replay_count_pathLenBad`, `pathLenBadGt_card_le`) controls the
canonical decision tree `canonicalDT cs F σ` built over a list of clauses `cs : List (Clause n)`
with the DNF/`termSat` (AND-of-literals) semantics (`dnfEval cs x = cs.any (evalLits T.lits ·)`).
The collapse target, however, is a `Rung4DNF n` `D` with `D.eval`.  These are *different objects*,
and connecting them was flagged as the remaining gap.

This file closes that gap *semantically*: a `Rung4DNF` term and a switching `Clause` both wrap
`List (Rung4Literal n)`, and both evals are OR-of-AND over the **same** `evalLits`.  So encoding
`D.terms` as clauses makes `dnfEval` agree with `D.eval` on the nose, and `canonicalDT_eval` then
gives a decision tree (over that encoding) that computes `D` on every subcube.

* `clausesOfDNF D` — encode `D : Rung4DNF n` as `List (Clause n)` (each term ↦ a clause, same lits).
* `dnfEval_clausesOfDNF` — `dnfEval (clausesOfDNF D) x = D.eval x` (the semantic identity).
* `canonicalDT_computes_dnf` — `(canonicalDT (clausesOfDNF D) fuel σ).eval x = D.eval x` for `x`
  extending `σ`, `fuel ≥ stars σ`.
* `exists_canonicalDT_computes_dnf` — a decision tree of depth `≤ stars σ` computing `D` on `σ`'s
  subcube.

**Honest scope.**  This gives depth `≤ stars σ` (the *trivial* bound: number of free coordinates).
Getting depth `≤ depthBudget` for a *good* restriction `σ` is the genuine switching content (the
canonical tree's **max-branch** depth is small), tied to the depth-based count via the (still open)
identification of `canonicalDT.depth` with the count's path length `s`.  What is closed here is the
object-mismatch: the count's `canonicalDT` and the collapse target `D` are now provably the same
function.  AC⁰/depth-3 ceiling; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting Rung4DNFTerm

variable {n : ℕ}

/-- Encode a `Rung4DNF` as the switching side's list of clauses: each DNF term becomes a clause with
the same literal list (both wrap `List (Rung4Literal n)`, with the AND-of-literals semantics that
`dnfEval`/`termSat` use). -/
def clausesOfDNF (D : Rung4DNF n) : List (Clause n) :=
  D.terms.map (fun T => { lits := T.lits })

/-- `Rung4DNF.evalTerms` is the disjunction (`any`) of the per-term `evalLits`. -/
theorem evalTerms_eq_any (ts : List (Rung4DNFTerm n)) (x : Fin n → Bool) :
    Rung4DNF.evalTerms ts x = ts.any (fun T => evalLits T.lits x) := by
  induction ts with
  | nil => rfl
  | cons T rest ih =>
    simp only [Rung4DNF.evalTerms, Rung4DNFTerm.eval, List.any_cons, ih]

/-- **The semantic identity.**  Evaluated as a DNF (OR of AND-of-literals), the clause-encoding of
`D` computes exactly `D`. -/
theorem dnfEval_clausesOfDNF (D : Rung4DNF n) (x : Fin n → Bool) :
    dnfEval (clausesOfDNF D) x = D.eval x := by
  unfold dnfEval clausesOfDNF Rung4DNF.eval
  rw [evalTerms_eq_any, List.any_map]
  rfl

/-- **The `canonicalDT` computes `D` bridge.**  The canonical stop-on-satisfied decision tree built
over the clause-encoding of `D` computes `D` on `σ`'s subcube, whenever the fuel covers the free
coordinates. -/
theorem canonicalDT_computes_dnf (D : Rung4DNF n) (fuel : ℕ) (σ : Fin n → Option Bool)
    (x : Fin n → Bool) (hfuel : stars σ ≤ fuel) (hext : Rung4Restriction.Extends σ x) :
    (canonicalDT (clausesOfDNF D) fuel σ).eval x = D.eval x := by
  rw [canonicalDT_eval fuel σ x hfuel hext, dnfEval_clausesOfDNF]

/-- If `D` computes a Boolean function `F`, so does the canonical tree over its clause-encoding. -/
theorem canonicalDT_computes_of_computes {F : BoolFunction n} (D : Rung4DNF n)
    (hF : D.Computes F) (fuel : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool)
    (hfuel : stars σ ≤ fuel) (hext : Rung4Restriction.Extends σ x) :
    (canonicalDT (clausesOfDNF D) fuel σ).eval x = F x := by
  rw [canonicalDT_computes_dnf D fuel σ x hfuel hext, hF x]

/-- **A decision tree of depth `≤ stars σ` computing `D` on `σ`'s subcube.**  Running the canonical
tree with fuel `= stars σ` gives depth `≤ stars σ` (`canonicalDT_depth_le`) and computes `D`
everywhere on the subcube (`canonicalDT_computes_dnf`).  (The deep switching content is improving
`stars σ` to a `depthBudget` for good `σ`; the *object* match is what this delivers.) -/
theorem exists_canonicalDT_computes_dnf (D : Rung4DNF n) (σ : Fin n → Option Bool) :
    ∃ T : BoolDecisionTree n, T.depth ≤ stars σ ∧
      ∀ x : Fin n → Bool, Rung4Restriction.Extends σ x → T.eval x = D.eval x := by
  refine ⟨canonicalDT (clausesOfDNF D) (stars σ) σ, canonicalDT_depth_le _ _ _, ?_⟩
  intro x hext
  exact canonicalDT_computes_dnf D (stars σ) σ x (le_refl _) hext

/-- **Collapse to a depth-`≤budget` tree, given the canonical tree is shallow.**  Once the object
match is closed, the *entire* remaining content of the count → DT-collapse step for the replay route
is the single hypothesis `hdepth`: that the canonical tree over `clausesOfDNF D` has max-branch depth
`≤ budget` (the switching lemma's quantitative conclusion for a good `σ`).  Given it, there is a
depth-`≤budget` decision tree computing `D` on `σ`'s subcube.  This is the honest, precisely-isolated
form: `hdepth` is exactly what the depth-based count must deliver. -/
theorem canonicalDT_collapse_of_depth_le (D : Rung4DNF n) (fuel : ℕ) (σ : Fin n → Option Bool)
    (budget : ℕ) (hfuel : stars σ ≤ fuel)
    (hdepth : (canonicalDT (clausesOfDNF D) fuel σ).depth ≤ budget) :
    ∃ T : BoolDecisionTree n, T.depth ≤ budget ∧
      ∀ x : Fin n → Bool, Rung4Restriction.Extends σ x → T.eval x = D.eval x :=
  ⟨canonicalDT (clausesOfDNF D) fuel σ, hdepth,
    fun x hext => canonicalDT_computes_dnf D fuel σ x hfuel hext⟩

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.canonicalDT_collapse_of_depth_le
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.dnfEval_clausesOfDNF
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.canonicalDT_computes_dnf
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.exists_canonicalDT_computes_dnf
