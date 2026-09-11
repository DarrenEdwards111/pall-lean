import GodMoveRuntimeSnapshotRank
import GodMoveLinearTimeRankObstruction

/-!
# Actual snapshot capture does not capture the derivative space

The existing four-state scanner halts on every length-16 input within 17
steps. Its actual snapshot-coordinate space has dimension at most 1296 and
contains its decision polynomial. The same polynomial has at least 1820
independent fourth-derivative directions, already with shift degree zero.
Consequently the derivative space is not contained in the snapshot space.

This tests the precise gap between the runtime-derived snapshot bound and
the normalized source's SPDP rank. The example decides the existing easy
scanner language, not SAT, and asserts no SAT separation.
-/

namespace GodMoveSnapshotDerivativeObstruction

open GodMoveBooleanInterpolation GodMoveCircuitConnection
open GodMoveRuntimeSnapshotRank GodMoveLinearTimeRankObstruction
open MultilinearSPDP
open GodMoveMonomialMinor (discreteBlocks)
open PallLean.Paper93.DeepMath.PathB.ComposableStepCircuit

/-- The snapshot output and unrolled circuit output describe the same actual
scanner run on every input. -/
theorem scannerDecision_eq_source (L : ℕ) :
    decisionPolynomial scanner L (L + 1) = scannerSource L := by
  unfold decisionPolynomial scannerSource
  rw [circuitTarget_eq_interpolate]
  apply interpolate_congr
  intro x
  exact (circuitFor_output scanner L (L + 1) x).symm

/-- The concrete output is the previously verified alternating prefix
polynomial, identified through the scanner's actual circuit semantics. -/
theorem scannerDecision_eq_prefixPolynomial (L : ℕ) :
    decisionPolynomial scanner L (L + 1) = prefixPolynomial L := by
  rw [scannerDecision_eq_source, scannerSource_eq_prefixPolynomial]

/-- Count every tape, head, and control coordinate at all 18 snapshot times. -/
theorem scanner_snapshot_rank_le_1296 :
    Module.finrank ℚ (snapshotSpace scanner 16 17) ≤ 1296 := by
  simpa [QM, scanner] using snapshotRank_le_clock scanner 16 17

/-- The full-degree coefficient gives the existing 1820-dimensional minor,
without using shifts or a derivative-closure hypothesis. -/
theorem scanner_derivative_rank_ge_1820 :
    1820 ≤ mlBlockedSpdpRank (discreteBlocks 16) 4 0
      (decisionPolynomial scanner 16 17) := by
  rw [scannerDecision_eq_source]
  have hchoose : Nat.choose 16 4 = 1820 := by decide
  simpa only [hchoose] using choose_le_scannerSource_rank 16 4 0

/-- The actual runtime-bounded snapshot space fails to contain the actual
fourth-derivative space of the output it captures. -/
theorem scanner_derivative_space_not_le_snapshotSpace :
    ¬ mlBlockedSpdpSubspace (discreteBlocks 16) 4 0
        (decisionPolynomial scanner 16 17) ≤ snapshotSpace scanner 16 17 := by
  intro h
  have hbad : (1820 : ℕ) ≤ 1296 :=
    scanner_derivative_rank_ge_1820.trans
      ((Submodule.finrank_mono h).trans scanner_snapshot_rank_le_1296)
  omega

/-- Output capture and failed derivative capture hold for the same machine,
input length, clock, and snapshot space. The parameter also satisfies 4k≤L. -/
theorem output_capture_without_derivative_capture :
    4 * 4 ≤ 16 ∧
      decisionPolynomial scanner 16 17 ∈ snapshotSpace scanner 16 17 ∧
      ¬ mlBlockedSpdpSubspace (discreteBlocks 16) 4 0
          (decisionPolynomial scanner 16 17) ≤ snapshotSpace scanner 16 17 :=
  ⟨by decide, decisionPolynomial_mem_snapshotSpace scanner 16 17,
    scanner_derivative_space_not_le_snapshotSpace⟩

end GodMoveSnapshotDerivativeObstruction

#print axioms GodMoveSnapshotDerivativeObstruction.scannerDecision_eq_source
#print axioms GodMoveSnapshotDerivativeObstruction.scannerDecision_eq_prefixPolynomial
#print axioms GodMoveSnapshotDerivativeObstruction.scanner_snapshot_rank_le_1296
#print axioms GodMoveSnapshotDerivativeObstruction.scanner_derivative_rank_ge_1820
#print axioms GodMoveSnapshotDerivativeObstruction.scanner_derivative_space_not_le_snapshotSpace
#print axioms GodMoveSnapshotDerivativeObstruction.output_capture_without_derivative_capture
