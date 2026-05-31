import PallLean.Paper93.DeepMath.PathB.ComputationalDepthWeakeningDAG
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinRestrictDerivation

/-!
# Lift (un-restriction) on weakening-DAGs

The un-restriction step of the fat-clause recursion: adding a literal `ℓ` to every
clause of a weakening-DAG maps it to a weakening-DAG over the inserted axioms, with
width increased by at most one.  Validity is preserved because inserting a literal
commutes with the resolvent for *every* pivot (`insert_resolvent`) and is monotone
for weakening (`Finset.insert_subset_insert`).  No re-indexing is needed — every
clause survives, just enlarged by `ℓ`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.TseitinResolution
open PallLean.Paper93.DeepMath.PathB.TseitinRestriction

variable {Edge : Type*} [DecidableEq Edge]
  {Axiom : ResolutionClause (TLit Edge) → Prop} {n : ℕ}

/-- **Lift on weakening-DAGs.**  Inserting `ℓ` into every clause maps a weakening-DAG
over `Axiom` to one over the `ℓ`-inserted axioms (same length, same structure). -/
def WeakeningDAG.lift (ℓ : TLit Edge) (D : WeakeningDAG tcompl Axiom n) :
    WeakeningDAG tcompl (fun C' => ∃ C, Axiom C ∧ insert ℓ C = C') n where
  clause i := insert ℓ (D.clause i)
  valid i := by
    rcases D.valid i with hax | ⟨j, k, p, hj, hk, heq⟩ | ⟨j, hj, hsub⟩
    · exact Or.inl ⟨D.clause i, hax, rfl⟩
    · refine Or.inr (Or.inl ⟨j, k, p, hj, hk, ?_⟩)
      rw [heq]
      exact (insert_resolvent (D.clause j) (D.clause k) (ne_tcompl p)).symm
    · exact Or.inr (Or.inr ⟨j, hj, Finset.insert_subset_insert _ hsub⟩)

@[simp] theorem WeakeningDAG.lift_clause (ℓ : TLit Edge) (D : WeakeningDAG tcompl Axiom n)
    (i : Fin n) : (D.lift ℓ).clause i = insert ℓ (D.clause i) := rfl

/-- The lift increases each clause's width by at most one. -/
theorem WeakeningDAG.lift_width_le (ℓ : TLit Edge) (D : WeakeningDAG tcompl Axiom n)
    (i : Fin n) :
    ResolutionClause.width ((D.lift ℓ).clause i) ≤ ResolutionClause.width (D.clause i) + 1 := by
  rw [WeakeningDAG.lift_clause]
  exact Finset.card_insert_le _ _

/-- The lift turns a refutation of `∅` into a derivation of the unit clause `{ℓ}`. -/
theorem WeakeningDAG.lift_root (ℓ : TLit Edge) (D : WeakeningDAG tcompl Axiom n)
    (i₀ : Fin n) (hi₀ : D.clause i₀ = (∅ : ResolutionClause (TLit Edge))) :
    (D.lift ℓ).clause i₀ = {ℓ} := by
  rw [WeakeningDAG.lift_clause, hi₀]
  rfl

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.WeakeningDAG.lift
#print axioms PallLean.Paper93.DeepMath.PathB.WeakeningDAG.lift_width_le
