import GodMoveConstructedProjection
import GodMoveCircuitRankObstruction

/-!
A finite obstruction for the newly constructed projection, independent of
sample selection and inverse weights. Six-input conjunction has thirteen
compiled gates but at least fifteen second-derivative directions. Therefore
no map with range in its computed wires can fix the entire derivative space.
This does not refute SAT-specific preservation for a SAT decider's own circuit.
-/
namespace GodMoveConstructedDerivativeObstruction

open GodMoveBooleanInterpolation GodMoveComputedWireRank GodMoveCircuitConnection
open GodMoveCircuitRankObstruction GodMoveMonomialMinor MultilinearSPDP
open GodMoveConstructedProjection GodMoveSampledWireGauge
open PallLean.Paper93.DeepMath.PathB ComposableMachine SeparationTarget

noncomputable def testRows :=
  mlBlockedSpdpSubspace (discreteBlocks 6) 2 0 (circuitTarget (unitCircuit 6))

theorem testRows_rank_ge : 15 ≤ Module.finrank ℚ testRows := by
  have h := choose_le_unitCircuit_strict_rank 6 2 0
  change 15 ≤ mlBlockedSpdpRank (discreteBlocks 6) 2 0 (circuitTarget (unitCircuit 6))
  rw [circuitTarget_eq_interpolate]
  have hc : Nat.choose 6 2 = 15 := by decide
  rw [hc] at h
  exact h

theorem testWire_rank_le : wireRank (unitCircuit 6) ≤ 13 := by
  have h := wireRank_le_length (unitCircuit 6)
  simpa [unitCircuit_length] using h

theorem testRows_not_in_wires : ¬ testRows ≤ wireSpace (unitCircuit 6) := by
  intro h
  have hdim : Module.finrank ℚ testRows ≤ wireRank (unitCircuit 6) :=
    Submodule.finrank_mono h
  have hlo := testRows_rank_ge
  have hhi := testWire_rank_le
  omega

/-- No choice of weights repairs the dimension mismatch. -/
theorem any_wire_map_loses_row (P : GodMoveBooleanInterpolation.Poly 6 →ₗ[ℚ] GodMoveBooleanInterpolation.Poly 6)
    (hP : LinearMap.range P ≤ wireSpace (unitCircuit 6)) :
    ∃ p ∈ testRows, P p ≠ p := by
  classical
  by_contra h
  push_neg at h
  apply testRows_not_in_wires
  intro p hp
  apply hP
  exact ⟨p, h p hp⟩

/-- Applies to the actual new descriptor for every correct supplied SAT machine,
not just a hypothetical algebraic projection or an arbitrary inverse. -/
theorem constructed_projection_loses_row (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) :
    ∃ p ∈ testRows,
      (sampledGauge (machineCertificate M T hD (unitCircuit 6)).data).projection p ≠ p := by
  apply any_wire_map_loses_row
  rw [machineCertificate_range]

end GodMoveConstructedDerivativeObstruction

#print axioms GodMoveConstructedDerivativeObstruction.testRows_rank_ge
#print axioms GodMoveConstructedDerivativeObstruction.testWire_rank_le
#print axioms GodMoveConstructedDerivativeObstruction.testRows_not_in_wires
#print axioms GodMoveConstructedDerivativeObstruction.any_wire_map_loses_row
#print axioms GodMoveConstructedDerivativeObstruction.constructed_projection_loses_row
