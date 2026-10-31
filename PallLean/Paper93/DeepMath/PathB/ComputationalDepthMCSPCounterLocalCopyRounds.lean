import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPCounterLocalCopyRound

/-!
# MCSP verifier: all delimited local-copy rounds

The previous file proves one complete round of the physical local-copy
controller.  Here that theorem is iterated over the first `k ≤ n` source
pairs.  After every round the controller is again at local counter home in
copy state `0`, so the next round's hypotheses match exactly.

At `k = n`, the source is fully marked, the target contains all `n` copied
pairs, the arbitrary live prefix and suffix are unchanged, and the exact
round clock closes to `6n² + 12n`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRounds

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.MCSPCounterCopyScratchMachine
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyLift
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRound

/-- Accumulated clock for the first `k` local-copy rounds. -/
def localRoundsClock (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => localRoundsClock n k + localRoundClock n k

theorem localRoundsClock_eq (n k : ℕ) :
    localRoundsClock n k = 4 * n * k + 2 * k * k + 12 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [localRoundsClock, ih, localRoundClock_eq]
      ring

/-- `k` complete local rounds process and copy the first `k` source pairs. -/
theorem run_localCopy_rounds (pre suffix : List Bool)
    (n k : ℕ) (hk : k ≤ n) (s : Bool) :
    run localCopyMachine (localRoundsClock n k)
      (liftCopyCfg pre ⟨(0, s), 0, cpyS n 0 0 suffix⟩) =
      liftCopyCfg pre
        ⟨(0, if k = 0 then s else false), 0, cpyS n k k suffix⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [localRoundsClock, run_add,
        ih (by omega),
        run_localCopy_round pre suffix n k (by omega)
          (if k = 0 then s else false)]
      simp

/-- Exact clock for all `n` local-copy rounds. -/
def localAllRoundsClock (n : ℕ) : ℕ := localRoundsClock n n

theorem localAllRoundsClock_eq (n : ℕ) :
    localAllRoundsClock n = 6 * n * n + 12 * n := by
  rw [localAllRoundsClock, localRoundsClock_eq]
  ring

/-- After every copy round, source and target are both complete; control has
returned to the embedded counter origin ready for the restore handoff. -/
theorem run_localCopy_allRounds (pre suffix : List Bool)
    (n : ℕ) (s : Bool) :
    run localCopyMachine (localAllRoundsClock n)
      (liftCopyCfg pre ⟨(0, s), 0, cpyS n 0 0 suffix⟩) =
      liftCopyCfg pre
        ⟨(0, if n = 0 then s else false), 0, cpyS n n n suffix⟩ := by
  exact run_localCopy_rounds pre suffix n n (le_refl n) s

/-- For positive counters the post-round stored bit is canonically false. -/
theorem run_localCopy_allRounds_pos (pre suffix : List Bool)
    (n : ℕ) (hn : 0 < n) (s : Bool) :
    run localCopyMachine (localAllRoundsClock n)
      (liftCopyCfg pre ⟨(0, s), 0, cpyS n 0 0 suffix⟩) =
      liftCopyCfg pre ⟨(0, false), 0, cpyS n n n suffix⟩ := by
  simpa [if_neg (Nat.ne_of_gt hn)] using
    run_localCopy_allRounds pre suffix n s

end PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRounds

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRounds.run_localCopy_rounds
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRounds.run_localCopy_allRounds
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRounds.localAllRoundsClock_eq
