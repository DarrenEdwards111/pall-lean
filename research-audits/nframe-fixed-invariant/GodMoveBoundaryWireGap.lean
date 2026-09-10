import GodMoveConstrainedBoundaryMinimum
import GodMoveProductionGaugeBridge
import GodMoveCircuitRankObstruction

/-!
# Output preservation and exact extraction do not imply derivative-row closure

The existing production wire gauge for an explicit conjunction circuit has
rank at most 2m+1 and fixes its output, the full monomial. The explicit
quadratic lift recovers the actual designated product from that fixed output.
Nevertheless, this very same wire gauge cannot fix all designated projected
derivative rows when choose(m,k) > 2m+1.

At m=16,k=4 the graph window 4k≤m holds, the circuit has 33 gates, and the
designated row gauge has rank 1820. This is an easy-circuit calibration of the
missing preservation implication. It neither concerns a general SAT decider
nor rules out an additional SAT-specific theorem. The algebraically defined
wire gauge itself still uses the earlier choice of a linear complement; no
efficient gauge-discovery assertion is introduced.
-/

namespace GodMoveBoundaryWireGap

open GodMoveMonomialMinor GodMoveQuadraticSheetLift
open GodMoveCircuitRankObstruction GodMoveCircuitConnection GodMoveProductionGaugeBridge
open GodMoveBoundaryNFrameGauge GodMoveConstrainedBoundaryMinimum
open SymmetricPower
open Step4Compiler.Step252

theorem unitWireGauge_rank_le (m : ℕ) :
    Module.finrank ℚ (LinearMap.range (wireGauge (unitCircuit m)).projection) ≤ 2 * m + 1 := by
  simpa only [unitCircuit_length] using wireGauge_rank_le_length (unitCircuit m)

/-- Actual verified circuit output, rather than a stipulated polynomial. -/
theorem unitCircuit_target (m : ℕ) : circuitTarget (unitCircuit m) = fullMonomial m := by
  rw [circuitTarget_eq_interpolate, unitCircuit_characteristic_eq_fullMonomial]

theorem unitWireGauge_fixes_output (m : ℕ) :
    (wireGauge (unitCircuit m)).projection (fullMonomial m) = fullMonomial m := by
  have h := wireGauge_fixes_target (unitCircuit m)
  rwa [unitCircuit_target] at h

/-- Exact quadratic extraction still succeeds on the fixed circuit output. -/
theorem unitWireGauge_quadratic_extraction (m : ℕ) :
    quadraticLift m ((wireGauge (unitCircuit m)).projection (fullMonomial m)) =
      boolFactorFullProd m := by
  rw [unitWireGauge_fixes_output, quadraticLift_fullMonomial]

/-- The extraction is also equality with the unchanged production target. -/
theorem unitWireGauge_designated_extraction
    (D : TuringMachine.DTM) (n : ℕ) (hn2 : 2 ≤ n)
    (htb : D.timeBound ≤ 4) (hns : D.numStates ≤ n)
    (B : SPDP.BlockPartition (PaperFaithfulCompilation.cookLevinUVSplit D n).total) :
    quadraticLift (n / 3)
        ((wireGauge (unitCircuit (n / 3))).projection (fullMonomial (n / 3))) =
      (cookLevinStrictFOBTarget D n hn2 htb hns B).coupledPoly := by
  rw [unitWireGauge_quadratic_extraction, designated_sheet_eq_boolFactorFullProd]

/-- A gate-count-controlled output-preserving production gauge need not be
closed under the designated projected derivative family. -/
theorem unitWireGauge_not_preserves_rows (m k : ℕ)
    (hlarge : 2 * m + 1 < Nat.choose m k) :
    ¬ PreservesDesignatedRows k (wireGauge (unitCircuit m)) := by
  intro h
  exact (Nat.not_le_of_lt hlarge)
    ((preserved_rank_lower _ h).trans (unitWireGauge_rank_le m))

/-- Both gauges are actual production gauges in the same polynomial ambient
space, and the derivative order satisfies the expander-screen window. -/
theorem concrete_production_gauge_gap :
    4 * 4 ≤ 16 ∧
    (unitCircuit 16).length = 33 ∧
    Module.finrank ℚ (LinearMap.range (wireGauge (unitCircuit 16)).projection) ≤ 33 ∧
    Module.finrank ℚ (LinearMap.range (boundaryGauge 16 4).projection) = 1820 ∧
    ¬ PreservesDesignatedRows 4 (wireGauge (unitCircuit 16)) := by
  refine ⟨by decide, by rw [unitCircuit_length], unitWireGauge_rank_le 16, ?_, ?_⟩
  · rw [boundaryGauge_rank]
    decide
  · exact unitWireGauge_not_preserves_rows 16 4 (by decide)

/-- The concrete failure persists alongside both output fixation and exact
designated-product extraction; those two successes do not supply closure. -/
theorem output_and_extraction_without_row_preservation :
    (wireGauge (unitCircuit 16)).projection (fullMonomial 16) = fullMonomial 16 ∧
    quadraticLift 16 ((wireGauge (unitCircuit 16)).projection (fullMonomial 16)) =
      boolFactorFullProd 16 ∧
    ¬ PreservesDesignatedRows 4 (wireGauge (unitCircuit 16)) :=
  ⟨unitWireGauge_fixes_output 16, unitWireGauge_quadratic_extraction 16,
    unitWireGauge_not_preserves_rows 16 4 (by decide)⟩

end GodMoveBoundaryWireGap

#print axioms GodMoveBoundaryWireGap.unitWireGauge_rank_le
#print axioms GodMoveBoundaryWireGap.unitCircuit_target
#print axioms GodMoveBoundaryWireGap.unitWireGauge_fixes_output
#print axioms GodMoveBoundaryWireGap.unitWireGauge_quadratic_extraction
#print axioms GodMoveBoundaryWireGap.unitWireGauge_designated_extraction
#print axioms GodMoveBoundaryWireGap.unitWireGauge_not_preserves_rows
#print axioms GodMoveBoundaryWireGap.concrete_production_gauge_gap
#print axioms GodMoveBoundaryWireGap.output_and_extraction_without_row_preservation
