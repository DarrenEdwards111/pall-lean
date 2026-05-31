import PallLean.Paper93.DeepMath.PathB.ComputationalDepthListDerivation
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinRestrictDerivation

/-!
# Lift (un-restriction) for list derivations

The lift dual to `LDeriv.restrict`: inserting a literal `ℓ` into every clause maps
a list derivation over `Axiom` to one over the `ℓ`-inserted axioms (every clause
survives — no removal).  Validity is preserved because `insert ℓ` commutes with the
resolvent for *every* pivot (`insert_resolvent`) and is monotone for weakening.
Width grows by at most one, and a refutation of `∅` lifts to a derivation of the
unit `{ℓ}` — the lifting branch of the asymmetric recombination.

Stated for the Tseitin complement `tcompl`, where `insert_resolvent` applies.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.TseitinResolution

variable {Edge : Type*} [DecidableEq Edge]
  {Axiom : ResolutionClause (TLit Edge) → Prop}

/-- **Lift on list derivations.**  Inserting `ℓ` into every clause maps a derivation
over `Axiom` to one over the `ℓ`-inserted axioms. -/
theorem LDeriv.lift (ℓ : TLit Edge) {L : List (ResolutionClause (TLit Edge))}
    (h : LDeriv tcompl Axiom L) :
    LDeriv tcompl (fun C' => ∃ C, Axiom C ∧ insert ℓ C = C') (L.map (insert ℓ)) := by
  induction h with
  | nil => exact LDeriv.nil
  | @cons C L just h ih =>
    refine LDeriv.cons ?_ ih
    rcases just with hax | ⟨D, E, p, hD, hE, heq⟩ | ⟨D, hD, hsub⟩
    · exact Or.inl ⟨C, hax, rfl⟩
    · refine Or.inr (Or.inl ⟨insert ℓ D, insert ℓ E, p,
        List.mem_map_of_mem hD, List.mem_map_of_mem hE, ?_⟩)
      rw [heq]
      exact (TseitinRestriction.insert_resolvent D E (TseitinRestriction.ne_tcompl p)).symm
    · exact Or.inr (Or.inr ⟨insert ℓ D, List.mem_map_of_mem hD,
        Finset.insert_subset_insert _ hsub⟩)

/-- The lift increases each clause's width by at most one. -/
theorem LDeriv.lift_width_le (ℓ : TLit Edge) {L : List (ResolutionClause (TLit Edge))} {W : ℕ}
    (hW : ∀ C ∈ L, ResolutionClause.width C ≤ W) :
    ∀ X ∈ L.map (insert ℓ), ResolutionClause.width X ≤ W + 1 := by
  intro X hX
  obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hX
  exact le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right (hW C hC) 1)

/-- The lift turns a refutation of `∅` into a derivation of the unit clause `{ℓ}`. -/
theorem LDeriv.lift_unit_mem (ℓ : TLit Edge) {L : List (ResolutionClause (TLit Edge))}
    (h : (∅ : ResolutionClause (TLit Edge)) ∈ L) :
    ({ℓ} : ResolutionClause (TLit Edge)) ∈ L.map (insert ℓ) := by
  have : (insert ℓ (∅ : ResolutionClause (TLit Edge))) = {ℓ} := by simp
  rw [← this]
  exact List.mem_map_of_mem h

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.lift
#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.lift_width_le
#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.lift_unit_mem
