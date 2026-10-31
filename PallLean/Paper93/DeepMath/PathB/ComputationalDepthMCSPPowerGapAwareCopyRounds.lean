import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPPowerGapAwareCopyRound

/-!
# MCSP verifier: all physical gap-aware bridge-copy rounds

The complete one-round theorem is iterated over the table-length counter.
Every round returns the fixed `gapCopyMachine` to the true table home with
both one-round gap flags cleared, while the retained internal `00`, both
power counters, reserved scratch, and arbitrary suffix remain physical tape.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyRounds

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyLift
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRound
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyMachine
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopySeek
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyRound
open GapCopyState

/-- Accumulated exact clock for the first `k` gapped table-copy rounds. -/
def gappedRoundsClock (n a : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => gappedRoundsClock n a k + gappedRoundClock n a k

theorem gappedRoundsClock_eq (n a k : ℕ) :
    gappedRoundsClock n a k =
      4 * a * k + 4 * bridgePairs n * k + 2 * k * k + 16 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [gappedRoundsClock, ih, gappedRoundClock_eq]
      ring

/-- The first `k ≤ a` physical rounds mark and copy precisely the first
`k` table pairs, returning to the true outer home after every round. -/
theorem run_gapped_rounds (pre suffix : List Bool)
    (n a k : ℕ) (hk : k ≤ a) (s : Bool) :
    let q := localOffset pre
    run gapCopyMachine (gappedRoundsClock n a k)
      ⟨.copy (0, s) false, q,
        localTape pre (gappedBridgeCpyS n a 0 0 suffix)⟩ =
      ⟨.copy (0, if k = 0 then s else false) false, q,
        localTape pre (gappedBridgeCpyS n a k k suffix)⟩ := by
  intro q
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [gappedRoundsClock, run_add, ih (by omega),
        run_gapped_round pre suffix n a k (by omega)
          (if k = 0 then s else false)]
      simp [q]

def gappedAllRoundsClock (n a : ℕ) : ℕ :=
  gappedRoundsClock n a a

theorem gappedAllRoundsClock_eq (n a : ℕ) :
    gappedAllRoundsClock n a =
      6 * a * a + 4 * bridgePairs n * a + 16 * a := by
  rw [gappedAllRoundsClock, gappedRoundsClock_eq]
  ring

/-- After all physical rounds, the table source is fully marked, the table
target is complete beyond both power counters, the internal gap is retained,
and control is back at the genuine table home. -/
theorem run_gapped_allRounds (pre suffix : List Bool)
    (n a : ℕ) (s : Bool) :
    let q := localOffset pre
    run gapCopyMachine (gappedAllRoundsClock n a)
      ⟨.copy (0, s) false, q,
        localTape pre (gappedBridgeCpyS n a 0 0 suffix)⟩ =
      ⟨.copy (0, if a = 0 then s else false) false, q,
        localTape pre (gappedBridgeCpyS n a a a suffix)⟩ := by
  intro q
  exact run_gapped_rounds pre suffix n a a (le_refl a) s

theorem run_gapped_allRounds_pos (pre suffix : List Bool)
    (n a : ℕ) (ha : 0 < a) (s : Bool) :
    let q := localOffset pre
    run gapCopyMachine (gappedAllRoundsClock n a)
      ⟨.copy (0, s) false, q,
        localTape pre (gappedBridgeCpyS n a 0 0 suffix)⟩ =
      ⟨.copy (0, false) false, q,
        localTape pre (gappedBridgeCpyS n a a a suffix)⟩ := by
  intro q
  simpa [if_neg (Nat.ne_of_gt ha)] using
    run_gapped_allRounds pre suffix n a s

end PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyRounds

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyRounds.run_gapped_rounds
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyRounds.run_gapped_allRounds
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyRounds.gappedAllRoundsClock_eq
