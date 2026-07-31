import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPCounterLocalCopyRounds

/-!
# MCSP verifier: prefix-lifted source restore pass

After all copy rounds, every source pair is marked `10`.  The verified copy
algorithm restores those pairs to `11` in states `6/7`.  This file transports
that mutating pass through the arbitrary live prefix and `00` local-home
delimiter, then proves the complete restore invariant on the suffix-safe
`resS` descriptors.

The real `localCopyMachine` heals exactly one high cell per pair, preserves
the copied target and arbitrary suffix, and retains the original exact
two-steps-per-pair clock.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRestore

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.MCSPCounterCopyScratchMachine
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyLift

theorem step_c6_local (pre : List Bool) {s : Bool} {p : ℕ}
    {T : List Bool} :
    step localCopyMachine
      (liftCopyCfg pre ⟨(6, s), p, T⟩) =
      liftCopyCfg pre ⟨(7, T.getD p false), p + 1, T⟩ := by
  have h := step_localCopy_lift pre
    (⟨(6, s), p, T⟩ : Cfg copyMachine)
    (by simp [copyMachine])
    (by simp [copyMachine])
    (by simp [copyMachine])
    (by simp [copyMachine])
  rw [h, step_c6]

theorem step_c7_heal_local (pre : List Bool) {p : ℕ}
    {T : List Bool} (hread : T.getD p false = false)
    (hp : p < T.length) :
    step localCopyMachine
      (liftCopyCfg pre ⟨(7, true), p, T⟩) =
      liftCopyCfg pre
        ⟨(6, true), p + 1, writeAt T p true⟩ := by
  have hread' := hread
  rw [List.getD_eq_getElem?_getD] at hread'
  have h := step_localCopy_lift pre
    (⟨(7, true), p, T⟩ : Cfg copyMachine)
    (by simp [copyMachine])
    (by simp [copyMachine, hread'])
    (by simp [copyMachine, hread'])
    (by
      intro w hw
      simp [copyMachine, hread'] at hw
      subst w
      exact hp)
  rw [h, step_c7_heal hread]

/-- Heal one processed `10` source pair under the arbitrary prefix. -/
theorem run_two_heal_local (pre : List Bool) {s : Bool} {p : ℕ}
    {T : List Bool}
    (hlo : T.getD p false = true)
    (hhi : T.getD (p + 1) false = false)
    (hp : p + 1 < T.length) :
    run localCopyMachine 2
      (liftCopyCfg pre ⟨(6, s), p, T⟩) =
      liftCopyCfg pre
        ⟨(6, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero,
    step_c6_local, hlo,
    step_c7_heal_local pre hhi hp]

/-- Complete prefix-lifted restore invariant on the evolving `resS` tape. -/
theorem run_restore_resS_local (pre suffix : List Bool)
    (n : ℕ) (s : Bool) (i : ℕ) (hi : i ≤ n) :
    run localCopyMachine (2 * i)
      (liftCopyCfg pre ⟨(6, s), 0, resS n 0 suffix⟩) =
      liftCopyCfg pre
        ⟨(6, if i = 0 then s else true), 2 * i,
          resS n i suffix⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [show 2 * (i + 1) = 2 * i + 2 by omega,
        run_add,
        ih (by omega)]
      have h := run_two_heal_local (pre := pre)
        (s := if i = 0 then s else true)
        (p := 2 * i) (T := resS n i suffix)
        (resS_getD_pair_lo n i suffix (by omega))
        (resS_getD_pair_hi n i suffix (by omega))
        (by rw [resS_length n i suffix (by omega)]; omega)
      rw [resS_heal n i suffix (by omega)] at h
      simpa [Nat.succ_ne_zero] using h

/-- All `n` marked source pairs are healed; copied target and suffix remain
byte-for-byte intact. -/
theorem run_restore_resS_all (pre suffix : List Bool)
    (n : ℕ) (s : Bool) :
    run localCopyMachine (2 * n)
      (liftCopyCfg pre ⟨(6, s), 0, resS n 0 suffix⟩) =
      liftCopyCfg pre
        ⟨(6, if n = 0 then s else true), 2 * n,
          resS n n suffix⟩ := by
  exact run_restore_resS_local pre suffix n s n (le_refl n)

end PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRestore

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRestore.run_restore_resS_local
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRestore.run_restore_resS_all
