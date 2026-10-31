import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPComparatorBridgeCopyRound

/-!
# MCSP verifier: all operational table-copy rounds across the power bridge

The one-round bridge theorem is iterated over the complete table-length
counter.  After every round the fixed `localCopyMachine` returns to the same
local home, while the two finalized power counters and arbitrary payload are
preserved byte-for-byte.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRounds

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyLift
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyLayout
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRound

/-- Accumulated clock for the first `k` table-copy rounds across the bridge. -/
def bridgeRoundsClock (n a : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => bridgeRoundsClock n a k + bridgeRoundClock n a k

theorem bridgeRoundsClock_eq (n a k : ℕ) :
    bridgeRoundsClock n a k =
      4 * a * k + 4 * bridgePairs n * k + 2 * k * k + 12 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [bridgeRoundsClock, ih, bridgeRoundClock_eq]
      ring

/-- The first `k ≤ a` physical rounds mark and copy exactly the first `k`
table-counter pairs across both power counters. -/
theorem run_bridge_rounds (pre suffix : List Bool)
    (n a k : ℕ) (hk : k ≤ a) (s : Bool) :
    run localCopyMachine (bridgeRoundsClock n a k)
      (liftCopyCfg pre
        ⟨(0, s), 0, bridgeCpyS n a 0 0 suffix⟩) =
      liftCopyCfg pre
        ⟨(0, if k = 0 then s else false), 0,
          bridgeCpyS n a k k suffix⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [bridgeRoundsClock, run_add,
        ih (by omega),
        run_bridge_round pre suffix n a k (by omega)
          (if k = 0 then s else false)]
      simp

/-- Exact clock for every table-copy round. -/
def bridgeAllRoundsClock (n a : ℕ) : ℕ := bridgeRoundsClock n a a

theorem bridgeAllRoundsClock_eq (n a : ℕ) :
    bridgeAllRoundsClock n a =
      6 * a * a + 4 * bridgePairs n * a + 12 * a := by
  rw [bridgeAllRoundsClock, bridgeRoundsClock_eq]
  ring

/-- After all rounds the table source is fully marked, the trailing table
target is complete, and control is back at the table counter's local home. -/
theorem run_bridge_allRounds (pre suffix : List Bool)
    (n a : ℕ) (s : Bool) :
    run localCopyMachine (bridgeAllRoundsClock n a)
      (liftCopyCfg pre
        ⟨(0, s), 0, bridgeCpyS n a 0 0 suffix⟩) =
      liftCopyCfg pre
        ⟨(0, if a = 0 then s else false), 0,
          bridgeCpyS n a a a suffix⟩ := by
  exact run_bridge_rounds pre suffix n a a (le_refl a) s

/-- For a positive table counter, the stored control bit after all rounds is
canonically false. -/
theorem run_bridge_allRounds_pos (pre suffix : List Bool)
    (n a : ℕ) (ha : 0 < a) (s : Bool) :
    run localCopyMachine (bridgeAllRoundsClock n a)
      (liftCopyCfg pre
        ⟨(0, s), 0, bridgeCpyS n a 0 0 suffix⟩) =
      liftCopyCfg pre
        ⟨(0, false), 0, bridgeCpyS n a a a suffix⟩ := by
  simpa [if_neg (Nat.ne_of_gt ha)] using
    run_bridge_allRounds pre suffix n a s

end PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRounds

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRounds.run_bridge_rounds
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRounds.run_bridge_allRounds
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRounds.bridgeAllRoundsClock_eq
