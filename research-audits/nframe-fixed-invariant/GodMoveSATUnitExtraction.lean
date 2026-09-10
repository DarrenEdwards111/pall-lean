import GodMoveMachineSourceMinor

/-!
# A concrete linear extraction of the unit-query monomial from a SAT machine

This packages the existing Boolean face and injective coordinate restriction
as one algebra map. Its definition uses only the fixed unit-query template.
Faithful SAT correctness derives its output; no satisfying assignment,
coefficient advice, or rank-transport hypothesis is provided to the map.

The source remains the normalized output polynomial on all encoded-length
words. Its runtime-derived polynomial SPDP bound has not been established.
-/

namespace GodMoveSATUnitExtraction

open MvPolynomial MultilinearSPDP SPDP PiStarConcrete
open GodMoveBooleanInterpolation GodMoveMachineFaceExtraction
open GodMoveSymbolicPinnedInput GodMovePinnedFaceLayout GodMoveUnitCharacteristic
open GodMoveFaithfulHandshake GodMoveMachineSourceMinor
open GodMoveMonomialMinor (fullMonomial discreteBlocks)
open PallLean.Paper93.DeepMath.PathB ComposableMachine SeparationTarget

abbrev unitInputLength (m : ℕ) := (inputTemplate (unitFormula m) m).length

/-- Fix the encoded formula constants and read the distinct assignment positions. -/
noncomputable def unitExtraction (m : ℕ) :
    Poly (unitInputLength m) →ₐ[ℚ] Poly m := by
  classical
  exact (restrictPoly ℚ (variablePosition (unitFormula m) m)
    (variablePosition_injective (unitFormula m) m)).comp
      (substAlgHom (pinnedKeep (unitFormula m) m)
        (fun j => bit (pinnedFixed (unitFormula m) m j)))

theorem unitExtraction_eq_restricted_face (m : ℕ) (p : Poly (unitInputLength m)) :
    unitExtraction m p =
      restrictPoly ℚ (variablePosition (unitFormula m) m)
        (variablePosition_injective (unitFormula m) m)
        (pinnedGauge (unitFormula m) m p) := by
  rfl

/-- The exact monomial is obtained from actual SAT-machine behavior on the
encoded pinned unit formulas. -/
theorem unitExtraction_of_decides
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) (m : ℕ) :
    unitExtraction m (machineSource M T (unitFormula m) m) = fullMonomial m := by
  rw [unitExtraction_eq_restricted_face,
    pinnedGauge_extracts_verifier M T hD _ m (unitFormula_variablesBelow m),
    restrictPoly_rename, unitFormula_characteristic]

/-- Rank transport on this concrete machine source is already derived by
the face theorem and exact injective parameter transport. -/
theorem unitExtraction_rank_le_source
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) (m k ell : ℕ) :
    mlBlockedSpdpRank (discreteBlocks m) k ell
        (unitExtraction m (machineSource M T (unitFormula m) m)) ≤
      mlBlockedSpdpRank (discreteBlocks (unitInputLength m)) k ell
        (machineSource M T (unitFormula m) m) := by
  rw [unitExtraction_of_decides M T hD m, ← unitFormula_characteristic m]
  exact verifier_strict_rank_le_source M T hD _ m (unitFormula_variablesBelow m) k ell

end GodMoveSATUnitExtraction

#print axioms GodMoveSATUnitExtraction.unitExtraction_eq_restricted_face
#print axioms GodMoveSATUnitExtraction.unitExtraction_of_decides
#print axioms GodMoveSATUnitExtraction.unitExtraction_rank_le_source
