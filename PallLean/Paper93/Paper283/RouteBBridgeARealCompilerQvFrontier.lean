import PallLean.CookLevinDefs

/-!
# Route B Bridge A: real compiler `Q_v` frontier

This file avoids the square-helper and pocket-family candidates.  The local
polynomial below is built directly from the actual `CompiledTableau.constraints`
field exposed by `cook_levin_compilation`.

For a locality block `b`, we filter the real compiler constraints to those
whose declared support touches `b`, then multiply the corresponding compiler
factors `(1 - c.poly)`.  For a vertex/variable `v`, `Q_v` is the product for
the compiler block containing `v`.

What is checked here:

* the candidate is literally a product over filtered real compiler constraints;
* every filtered constraint is still a member of the compiler's constraint list;
* at the degenerate SPDP profile `(kappa, ell) = (0, 0)`, the candidate has
  blocked multilinear SPDP rank at most `1`.

What remains open:

The nondegenerate Bridge A theorem would need a lower bound on this exact
candidate at the requested `kappa`, e.g.

`kappa <= mlBlockedSpdpRank T.partition kappa kappa (compilerVertexQv T v)`.

The current compiler API exposes the constraint list and supports, but no
kernel-checked independence/minor theorem for these filtered block products.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open PaperFaithfulSeparation
open SPDP
open MultilinearSPDP

attribute [local instance] Classical.dec

/-- A real compiler constraint touches block `b` when one of the variables in
its declared support is assigned to `b` by the compiler partition. -/
def constraintTouchesBlock {M : TuringMachine.DTM} {n : Nat}
    (T : CompiledTableau M n) (b : Fin T.partition.numBlocks)
    (c : LocalConstraint T.numVars) : Prop :=
  exists x, x ∈ c.support ∧ T.partition.assign x = b

/-- The real compiler constraints touching a compiler locality block. -/
noncomputable def compilerBlockConstraints {M : TuringMachine.DTM} {n : Nat}
    (T : CompiledTableau M n) (b : Fin T.partition.numBlocks) :
    List (LocalConstraint T.numVars) := by
  classical
  exact T.constraints.filter (fun c => constraintTouchesBlock T b c)

/-- The Route B / Bridge A candidate attached to a locality block:
the product of the real compiler factors touching that block. -/
noncomputable def compilerBlockQ {M : TuringMachine.DTM} {n : Nat}
    (T : CompiledTableau M n) (b : Fin T.partition.numBlocks) :
    MvPolynomial (Fin T.numVars) Rat :=
  ((compilerBlockConstraints T b).map
    (fun c => (1 : MvPolynomial (Fin T.numVars) Rat) - c.poly)).prod

/-- The per-vertex/locality-block candidate `Q_v`, built from the real
compiler constraints in the block containing `v`. -/
noncomputable def compilerVertexQv {M : TuringMachine.DTM} {n : Nat}
    (T : CompiledTableau M n) (v : Fin T.numVars) :
    MvPolynomial (Fin T.numVars) Rat :=
  compilerBlockQ T (T.partition.assign v)

/-- Filtered block constraints are not synthetic gadgets: they are members of
the actual compiler constraint list. -/
theorem compilerBlockConstraints_mem_constraints {M : TuringMachine.DTM}
    {n : Nat} (T : CompiledTableau M n) (b : Fin T.partition.numBlocks)
    {c : LocalConstraint T.numVars} :
    c ∈ compilerBlockConstraints T b -> c ∈ T.constraints := by
  classical
  intro hc
  unfold compilerBlockConstraints at hc
  exact (List.mem_filter.mp hc).1

/-- A filtered constraint really touches the block it was filtered for. -/
theorem compilerBlockConstraints_touches {M : TuringMachine.DTM}
    {n : Nat} (T : CompiledTableau M n) (b : Fin T.partition.numBlocks)
    {c : LocalConstraint T.numVars} :
    c ∈ compilerBlockConstraints T b -> constraintTouchesBlock T b c := by
  classical
  intro hc
  unfold compilerBlockConstraints at hc
  exact of_decide_eq_true (List.mem_filter.mp hc).2

/-- At `(kappa, ell) = (0, 0)`, every polynomial has blocked multilinear SPDP
rank at most one: all rows are scalar multiples of `mlProj p`. -/
theorem mlBlockedSpdpRank_zero_zero_le_one {N : Nat}
    (B : BlockPartition N) (p : MvPolynomial (Fin N) Rat) :
    mlBlockedSpdpRank B 0 0 p ≤ 1 := by
  classical
  unfold mlBlockedSpdpRank
  let G : Finset (MvPolynomial (Fin N) Rat) := {mlProj p}
  have hspan :
      mlBlockedSpdpSubspace B 0 0 p ≤
        Submodule.span Rat (↑G : Set (MvPolynomial (Fin N) Rat)) := by
    unfold mlBlockedSpdpSubspace
    apply Submodule.span_le.mpr
    rintro q ⟨S, m, hlen, hdeg, _hvars, _hadm, hq⟩
    have hSnil : S = [] := List.length_eq_zero_iff.mp hlen
    have hdeg0 : m.totalDegree = 0 := Nat.le_zero.mp hdeg
    have hmC : m = MvPolynomial.C (m.coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg0
    subst S
    rw [hq, hmC]
    simp only [SPDP.iterDerivList, List.foldl_nil]
    rw [← MvPolynomial.smul_eq_C_mul p (m.coeff 0), mlProj_smul]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    simp [G]
  calc
    Module.finrank Rat (mlBlockedSpdpSubspace B 0 0 p)
        ≤ Module.finrank Rat
            (Submodule.span Rat (↑G : Set (MvPolynomial (Fin N) Rat))) :=
      Submodule.finrank_mono hspan
    _ ≤ G.card := finrank_span_finset_le_card G
    _ ≤ 1 := by simp [G]

/-- The real compiler-local candidate has the checked degenerate rank bound. -/
theorem compilerVertexQv_rank_zero_zero_le_one {M : TuringMachine.DTM}
    {n : Nat} (T : CompiledTableau M n) (v : Fin T.numVars) :
    mlBlockedSpdpRank T.partition 0 0 (compilerVertexQv T v) ≤ 1 :=
  mlBlockedSpdpRank_zero_zero_le_one T.partition (compilerVertexQv T v)

/-- Specialization of `Q_v` to the actual `cook_levin_compilation`. -/
noncomputable def cookLevinCompilerVertexQv
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (v : Fin (cook_levin_compilation M n hn htb hns).numVars) :
    MvPolynomial
      (Fin (cook_levin_compilation M n hn htb hns).numVars) Rat :=
  compilerVertexQv (cook_levin_compilation M n hn htb hns) v

/-- The actual Cook-Levin specialization inherits the degenerate rank bound. -/
theorem cookLevinCompilerVertexQv_rank_zero_zero_le_one
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (v : Fin (cook_levin_compilation M n hn htb hns).numVars) :
    mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        0 0 (cookLevinCompilerVertexQv M n hn htb hns v) ≤ 1 :=
  compilerVertexQv_rank_zero_zero_le_one
    (cook_levin_compilation M n hn htb hns) v

/-- The exact nondegenerate theorem still needed for paper-faithful Bridge A
with this candidate.  This is intentionally a `Prop`, not an axiom. -/
def CompilerVertexQvBridgeARankTarget {M : TuringMachine.DTM} {n : Nat}
    (T : CompiledTableau M n) (v : Fin T.numVars) (kappa : Nat) : Prop :=
  kappa ≤ mlBlockedSpdpRank T.partition kappa kappa (compilerVertexQv T v)

/-- Normalized exact-rank variant sometimes needed by downstream Route B
interfaces.  The current compiler does not prove this for the filtered
constraint-product candidate. -/
def CompilerVertexQvExactRankTarget {M : TuringMachine.DTM} {n : Nat}
    (T : CompiledTableau M n) (v : Fin T.numVars)
    (kappa gadgetN : Nat) : Prop :=
  mlBlockedSpdpRank T.partition kappa kappa (compilerVertexQv T v) =
    kappa * gadgetN

#print axioms compilerBlockConstraints_mem_constraints
#print axioms compilerBlockConstraints_touches
#print axioms mlBlockedSpdpRank_zero_zero_le_one
#print axioms compilerVertexQv_rank_zero_zero_le_one
#print axioms cookLevinCompilerVertexQv_rank_zero_zero_le_one

end PallLean.Paper93.Paper283
