import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPCounterCopyScratchMachine
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPComparatorRoutingMachine

/-!
# MCSP verifier: stage both copied counters for the comparator

This file connects the two finalized counter values to the suffix-safe scratch
copy theorem.  The real fixed copy machine is run once for `table.length` and
once for `2^n`.  Their exact output tapes are then split only at proved unary
counter lengths and oriented as

    tableLength, 2^n, 2^n, tableLength, payload.

The result is definitionally the comparator layout already consumed by the
finite-control router.  This closes the two component-copy and layout algebra.
The final operational weld is a positioned finite-control controller which
performs these two phases on one physical tape.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPComparatorScratchStaging

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.MCSPCounterCopyScratchMachine
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorReadyLayout
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorRoutingMachine

def tableScratchInput (table payload : List Bool) : List Bool :=
  unaryD table.length ++
    List.replicate (2 * table.length + 2) false ++ payload

def powScratchInput (n : ℕ) : List Bool :=
  unaryD (2 ^ n) ++
    List.replicate (2 * (2 ^ n) + 2) false

def tableCopyRun (table payload : List Bool) :=
  run copyMachine (cpyClock table.length)
    (init copyMachine (tableScratchInput table payload))

def powCopyRun (n : ℕ) :=
  run copyMachine (cpyClock (2 ^ n))
    (init copyMachine (powScratchInput n))

theorem tableCopyRun_eq (table payload : List Bool) :
    tableCopyRun table payload =
      ⟨(10, false), 4 * table.length + 3,
        unaryD table.length ++ unaryD table.length ++ payload⟩ := by
  unfold tableCopyRun tableScratchInput
  exact copy_run_scratch table.length payload

theorem powCopyRun_eq (n : ℕ) :
    powCopyRun n =
      ⟨(10, false), 4 * (2 ^ n) + 3,
        unaryD (2 ^ n) ++ unaryD (2 ^ n)⟩ := by
  unfold powCopyRun powScratchInput
  simpa using copy_run_scratch (2 ^ n) []

/-- Recover the first table-length block from the real table-copy run. -/
theorem tableCopyRun_first (table payload : List Bool) :
    (tableCopyRun table payload).tp.take
        (2 * table.length + 2) =
      unaryD table.length := by
  rw [tableCopyRun_eq]
  rw [show 2 * table.length + 2 =
    (unaryD table.length).length by
      exact (unaryD_length table.length).symm]
  simp

/-- Recover the preserved second table-length block and payload. -/
theorem tableCopyRun_second_payload (table payload : List Bool) :
    (tableCopyRun table payload).tp.drop
        (2 * table.length + 2) =
      unaryD table.length ++ payload := by
  rw [tableCopyRun_eq]
  rw [show 2 * table.length + 2 =
    (unaryD table.length).length by
      exact (unaryD_length table.length).symm]
  simp

/-- The power-copy run is already exactly the two middle blocks. -/
theorem powCopyRun_tape (n : ℕ) :
    (powCopyRun n).tp =
      unaryD (2 ^ n) ++ unaryD (2 ^ n) := by
  rw [powCopyRun_eq]

/-- Assemble the two real copy outputs in the orientation consumed by the
reverse and forward comparisons. -/
def stagedLayoutFromRuns (n : ℕ) (table payload : List Bool) : List Bool :=
  (tableCopyRun table payload).tp.take (2 * table.length + 2) ++
    (powCopyRun n).tp ++
      (tableCopyRun table payload).tp.drop (2 * table.length + 2)

theorem stagedLayoutFromRuns_eq (n : ℕ) (table payload : List Bool) :
    stagedLayoutFromRuns n table payload =
      comparatorLayout n table payload := by
  simp only [stagedLayoutFromRuns, tableCopyRun_first,
    powCopyRun_tape, tableCopyRun_second_payload]
  simp [comparatorLayout, List.append_assoc]

theorem stagedLayout_routes_to_payload (n : ℕ)
    (table payload : List Bool) :
    run routeMachine (routeClock n table.length)
      (init routeMachine (stagedLayoutFromRuns n table payload)) =
      ⟨.accept, routeClock n table.length,
        comparatorLayout n table payload⟩ := by
  rw [stagedLayoutFromRuns_eq]
  exact machine_run_comparatorLayout n table payload

/-- Total time of the two physical copy phases. -/
def stagingCopyClock (n tableLength : ℕ) : ℕ :=
  cpyClock tableLength + cpyClock (2 ^ n)

theorem stagingCopyClock_le (n tableLength : ℕ) :
    stagingCopyClock n tableLength ≤
      3 * (tableLength + 2) * (tableLength + 2) +
        3 * (2 ^ n + 2) * (2 ^ n + 2) := by
  unfold stagingCopyClock
  exact Nat.add_le_add (cpyClock_le tableLength) (cpyClock_le (2 ^ n))

/-- Copy phases plus the proved linear four-block router retain an explicit
polynomial expression in the two counter magnitudes. -/
def stagingClock (n tableLength : ℕ) : ℕ :=
  stagingCopyClock n tableLength + routeClock n tableLength

theorem stagingClock_le (n tableLength : ℕ) :
    stagingClock n tableLength ≤
      3 * (tableLength + 2) * (tableLength + 2) +
        3 * (2 ^ n + 2) * (2 ^ n + 2) +
          (4 * tableLength + 4 * (2 ^ n) + 8) := by
  unfold stagingClock routeClock
  exact Nat.add_le_add (stagingCopyClock_le n tableLength) (le_refl _)

end PallLean.Paper93.DeepMath.PathB.MCSPComparatorScratchStaging

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorScratchStaging.stagedLayoutFromRuns_eq
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorScratchStaging.stagedLayout_routes_to_payload
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorScratchStaging.stagingClock_le
