import PallLean.Paper93.DeepMath.PathB.ComputationalDepthWeakeningDAG
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRestrictionClauseAlgebra
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinRestrictDerivation

/-!
# Restriction of a weakening-DAG (the derivation-level restriction map)

The restriction step of the fat-clause recursion, at the level of derivation
objects.  Setting a literal `ℓ` to true acts on every clause by dropping the
now-false literal `compl ℓ` (`restrictClause`).  Because `restrictClause` is the
purely syntactic `erase (compl ℓ)` and commutes with the resolvent
*unconditionally* (`restrictClause_resolvent`), applying it to **every** clause of
a weakening-DAG yields a weakening-DAG over the restricted axioms — with **no
re-indexing**, exactly dual to `WeakeningDAG.lift`:

* an axiom maps to a restricted axiom;
* a resolvent maps to the exact resolvent of the restricted parents;
* a weakening maps to a weakening (`erase` is monotone).

Width never increases, and a refutation (`∅`) maps to a refutation (`∅.erase = ∅`).
This establishes that restriction maps a refutation of `Axiom` to a refutation of
`Axiom|ℓ` of the same length and no larger width; the fat-clause *counting*
(which surviving clauses to drop, and the round recursion) is the separate
combinatorial argument carried by `fat_count_decreases` / `exists_decay_zero`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.TseitinResolution
open PallLean.Paper93.DeepMath.PathB.RestrictionClauseAlgebra

variable {Edge : Type*} [DecidableEq Edge]
  {Axiom : ResolutionClause (TLit Edge) → Prop} {n : ℕ}

/-- **Restriction on weakening-DAGs.**  Dropping `compl ℓ` from every clause maps a
weakening-DAG over `Axiom` to one over the restricted axioms (same length, same
structure). -/
def WeakeningDAG.restrict (ℓ : TLit Edge) (D : WeakeningDAG tcompl Axiom n) :
    WeakeningDAG tcompl (fun C' => ∃ C, Axiom C ∧ restrictClause tcompl ℓ C = C') n where
  clause i := restrictClause tcompl ℓ (D.clause i)
  valid i := by
    rcases D.valid i with hax | ⟨j, k, p, hj, hk, heq⟩ | ⟨j, hj, hsub⟩
    · exact Or.inl ⟨D.clause i, hax, rfl⟩
    · refine Or.inr (Or.inl ⟨j, k, p, hj, hk, ?_⟩)
      rw [heq, restrictClause_resolvent]
    · exact Or.inr (Or.inr ⟨j, hj, Finset.erase_subset_erase _ hsub⟩)

@[simp] theorem WeakeningDAG.restrict_clause (ℓ : TLit Edge) (D : WeakeningDAG tcompl Axiom n)
    (i : Fin n) : (D.restrict ℓ).clause i = restrictClause tcompl ℓ (D.clause i) := rfl

/-- Restriction never increases any clause's width. -/
theorem WeakeningDAG.restrict_width_le (ℓ : TLit Edge) (D : WeakeningDAG tcompl Axiom n)
    (i : Fin n) :
    ResolutionClause.width ((D.restrict ℓ).clause i) ≤ ResolutionClause.width (D.clause i) := by
  rw [WeakeningDAG.restrict_clause]
  exact restrictClause_width_le tcompl ℓ (D.clause i)

/-- Restriction maps a refutation of `∅` to a refutation of `∅`. -/
theorem WeakeningDAG.restrict_root (ℓ : TLit Edge) (D : WeakeningDAG tcompl Axiom n)
    (i₀ : Fin n) (hi₀ : D.clause i₀ = (∅ : ResolutionClause (TLit Edge))) :
    (D.restrict ℓ).clause i₀ = (∅ : ResolutionClause (TLit Edge)) := by
  rw [WeakeningDAG.restrict_clause, hi₀, restrictClause]
  exact Finset.erase_empty _

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.WeakeningDAG.restrict
#print axioms PallLean.Paper93.DeepMath.PathB.WeakeningDAG.restrict_width_le
#print axioms PallLean.Paper93.DeepMath.PathB.WeakeningDAG.restrict_root
