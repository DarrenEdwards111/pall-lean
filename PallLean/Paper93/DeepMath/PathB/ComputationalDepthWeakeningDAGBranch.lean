import PallLean.Paper93.DeepMath.PathB.ComputationalDepthWeakeningDAGLift
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthWeakeningDAGCombine

/-!
# The variable-branching width recursion

Assembling `lift` and `combine` gives the classical branching half of the
size–width method:
\[
  W(F) \;\le\; \max\bigl(W(F|_{x=1}),\,W(F|_{x=0})\bigr) + 1 .
\]

Given a width-`w` refutation of `F|_{ℓ}` and a width-`w` refutation of
`F|_{¬ℓ}`, lift the first by `ℓ` (deriving `{ℓ}`) and the second by `¬ℓ`
(deriving `{¬ℓ}`), then `combine` the two units into a refutation of the original
`F`, of width `≤ w + 1`.  The axiom side-conditions compose into a disjunction of
the two `ℓ`/`¬ℓ`-inserted axiom sets (handled by `weakenAxiom`).
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.TseitinResolution

variable {Lit : Type*} [DecidableEq Lit] {compl : Lit → Lit} {n : ℕ}

/-- A weakening-DAG over a smaller axiom predicate `P` is one over any larger `Q`. -/
def WeakeningDAG.weakenAxiom {P Q : ResolutionClause Lit → Prop} (h : ∀ C, P C → Q C)
    (D : WeakeningDAG compl P n) : WeakeningDAG compl Q n where
  clause := D.clause
  valid i := by
    rcases D.valid i with hax | hr | hw
    · exact Or.inl (h _ hax)
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr hw)

@[simp] theorem WeakeningDAG.weakenAxiom_clause {P Q : ResolutionClause Lit → Prop}
    (h : ∀ C, P C → Q C) (D : WeakeningDAG compl P n) (i : Fin n) :
    (D.weakenAxiom h).clause i = D.clause i := rfl

variable {Edge : Type*} [DecidableEq Edge]

/-- The composite axiom predicate of a branch: an `ℓ`-inserted `A1`-axiom or a
`¬ℓ`-inserted `A2`-axiom. -/
def branchAxiom (A1 A2 : ResolutionClause (TLit Edge) → Prop) (ℓ : TLit Edge) :
    ResolutionClause (TLit Edge) → Prop :=
  fun C' => (∃ C, A1 C ∧ insert ℓ C = C') ∨ (∃ C, A2 C ∧ insert (tcompl ℓ) C = C')

/-- **Branching recursion.**  Refutations of `F|_{ℓ}` and `F|_{¬ℓ}` combine into a
refutation of `F` (over the composite branch axioms). -/
def WeakeningDAG.branch {A1 A2 : ResolutionClause (TLit Edge) → Prop} (ℓ : TLit Edge)
    {n1 n2 : ℕ}
    (D1 : WeakeningDAG tcompl A1 n1) (i1 : Fin n1)
    (h1 : D1.clause i1 = (∅ : ResolutionClause (TLit Edge)))
    (D2 : WeakeningDAG tcompl A2 n2) (i2 : Fin n2)
    (h2 : D2.clause i2 = (∅ : ResolutionClause (TLit Edge))) :
    WeakeningDAG tcompl (branchAxiom A1 A2 ℓ) (n1 + n2 + 1) :=
  WeakeningDAG.combine ℓ
    ((D1.lift ℓ).weakenAxiom (fun _ hC => Or.inl hC))
    ((D2.lift (tcompl ℓ)).weakenAxiom (fun _ hC => Or.inr hC))
    i1 (WeakeningDAG.lift_root ℓ D1 i1 h1)
    i2 (WeakeningDAG.lift_root (tcompl ℓ) D2 i2 h2)

/-- The branch derivation refutes `∅`. -/
theorem WeakeningDAG.branch_root {A1 A2 : ResolutionClause (TLit Edge) → Prop} (ℓ : TLit Edge)
    {n1 n2 : ℕ} (D1 : WeakeningDAG tcompl A1 n1) (i1 : Fin n1)
    (h1 : D1.clause i1 = (∅ : ResolutionClause (TLit Edge)))
    (D2 : WeakeningDAG tcompl A2 n2) (i2 : Fin n2)
    (h2 : D2.clause i2 = (∅ : ResolutionClause (TLit Edge))) :
    (WeakeningDAG.branch ℓ D1 i1 h1 D2 i2 h2).clause ⟨n1 + n2, by omega⟩
      = (∅ : ResolutionClause (TLit Edge)) :=
  WeakeningDAG.combine_root ℓ _ _ i1 _ i2 _

/-- **Width of the branch:** if both sub-refutations have width `≤ w`, the branch
has width `≤ w + 1`. -/
theorem WeakeningDAG.branch_width_le {A1 A2 : ResolutionClause (TLit Edge) → Prop}
    (ℓ : TLit Edge) {n1 n2 : ℕ} (D1 : WeakeningDAG tcompl A1 n1) (i1 : Fin n1)
    (h1 : D1.clause i1 = (∅ : ResolutionClause (TLit Edge)))
    (D2 : WeakeningDAG tcompl A2 n2) (i2 : Fin n2)
    (h2 : D2.clause i2 = (∅ : ResolutionClause (TLit Edge))) {w : ℕ}
    (hw1 : ∀ j, ResolutionClause.width (D1.clause j) ≤ w)
    (hw2 : ∀ j, ResolutionClause.width (D2.clause j) ≤ w)
    (i : Fin (n1 + n2 + 1)) :
    ResolutionClause.width ((WeakeningDAG.branch ℓ D1 i1 h1 D2 i2 h2).clause i) ≤ w + 1 := by
  refine WeakeningDAG.combine_width_le ℓ _ _ i1 _ i2 _ ?_ ?_ i
  · intro j
    rw [WeakeningDAG.weakenAxiom_clause]
    calc ResolutionClause.width ((D1.lift ℓ).clause j)
        ≤ ResolutionClause.width (D1.clause j) + 1 := WeakeningDAG.lift_width_le ℓ D1 j
      _ ≤ w + 1 := Nat.add_le_add_right (hw1 j) 1
  · intro j
    rw [WeakeningDAG.weakenAxiom_clause]
    calc ResolutionClause.width ((D2.lift (tcompl ℓ)).clause j)
        ≤ ResolutionClause.width (D2.clause j) + 1 := WeakeningDAG.lift_width_le (tcompl ℓ) D2 j
      _ ≤ w + 1 := Nat.add_le_add_right (hw2 j) 1

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.WeakeningDAG.branch
#print axioms PallLean.Paper93.DeepMath.PathB.WeakeningDAG.branch_root
#print axioms PallLean.Paper93.DeepMath.PathB.WeakeningDAG.branch_width_le
