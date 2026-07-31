import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPCounterLocalCopyScans

/-!
# MCSP verifier: prefix-lifted mark and grow passes

This file supplies the mutating half of one local unary-copy round.  Under an
arbitrary live prefix and `00` local-home delimiter, the real
`localCopyMachine`:

* marks the next source `11` pair as `10`;
* detects the target's blank `00` pair;
* writes the new target `11` pair inside reserved scratch; and
* intercepts the original absolute reset, entering local-home control while
  remembering copy state `0`.

The specialized top theorem lands on the exact evolved `cpyS` descriptor.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyGrow

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.MCSPCounterCopyScratchMachine
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyLift
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyScans
open LocalHomeState
open LocalCopyState

theorem step_c1_mark_local (pre : List Bool) {p : ℕ} {T : List Bool}
    (hread : T.getD p false = true) (hp : p < T.length) :
    step localCopyMachine
      (liftCopyCfg pre ⟨(1, true), p, T⟩) =
      liftCopyCfg pre
        ⟨(2, true), p + 1, writeAt T p false⟩ := by
  have hread' := hread
  rw [List.getD_eq_getElem?_getD] at hread'
  have h := step_localCopy_lift pre
    (⟨(1, true), p, T⟩ : Cfg copyMachine)
    (by simp [copyMachine])
    (by simp [copyMachine, hread'])
    (by simp [copyMachine, hread'])
    (by
      intro w hw
      simp [copyMachine, hread'] at hw
      subst w
      exact hp)
  rw [h, step_c1_mark hread]

theorem step_c3_endW_local (pre : List Bool) {p : ℕ} {T : List Bool}
    (hread : T.getD p false = false) (hp : 0 < p) :
    step localCopyMachine
      (liftCopyCfg pre ⟨(3, false), p, T⟩) =
      liftCopyCfg pre ⟨(4, false), p - 1, T⟩ := by
  have hread' := hread
  rw [List.getD_eq_getElem?_getD] at hread'
  have h := step_localCopy_lift pre
    (⟨(3, false), p, T⟩ : Cfg copyMachine)
    (by simp [copyMachine])
    (by simp [copyMachine, hread'])
    (by simpa [copyMachine, hread'] using hp)
    (by simp [copyMachine, hread'])
  rw [h, step_c3_endW hread]

theorem step_c4_local (pre : List Bool) {s : Bool} {p : ℕ}
    {T : List Bool} (hp : p < T.length) :
    step localCopyMachine
      (liftCopyCfg pre ⟨(4, s), p, T⟩) =
      liftCopyCfg pre ⟨(5, s), p + 1, writeAt T p true⟩ := by
  have h := step_localCopy_lift pre
    (⟨(4, s), p, T⟩ : Cfg copyMachine)
    (by simp [copyMachine])
    (by simp [copyMachine])
    (by simp [copyMachine])
    (by
      intro w hw
      simp [copyMachine] at hw
      subst w
      exact hp)
  rw [h, step_c4]

/-- State `5` performs its original high-cell write but enters local-home
control instead of resetting to absolute cell `0`. -/
theorem step_c5_enterHome_local (pre : List Bool) {s : Bool} {p : ℕ}
    {T : List Bool} (hp : p < T.length) :
    step localCopyMachine
      (liftCopyCfg pre ⟨(5, s), p, T⟩) =
      ⟨.home (0, s) scanHi, localOffset pre + p,
        localTape pre (writeAt T p true)⟩ := by
  let c : Cfg copyMachine :=
    ⟨(5, s), localOffset pre + p, localTape pre T⟩
  have h := step_localCopy_reset c
    (by simp [c, copyMachine])
    (by simp [c, copyMachine])
  have hδ : copyMachine.δ c.st (c.tp.getD c.hd false) =
      ((0, s), some true, 3) := by
    simp [c, copyMachine]
  rw [hδ] at h
  rw [show liftCopyCfg pre (⟨(5, s), p, T⟩ : Cfg copyMachine) =
      copyCfg c by rfl,
    h]
  simp only
  rw [localTape_writeAt pre T p true hp]

/-- Mark one source data pair under the arbitrary prefix. -/
theorem run_two_mark_local (pre : List Bool) {s : Bool} {p : ℕ}
    {T : List Bool}
    (hlo : T.getD p false = true)
    (hhi : T.getD (p + 1) false = true)
    (hp : p + 1 < T.length) :
    run localCopyMachine 2
      (liftCopyCfg pre ⟨(0, s), p, T⟩) =
      liftCopyCfg pre
        ⟨(2, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero, step_c0_local, hlo,
    step_c1_mark_local pre hhi hp]

/-- Detect a blank target pair, write `11`, and enter local-home control. -/
theorem run_four_grow_enterHome_local (pre : List Bool)
    {p : ℕ} {T : List Bool}
    (hlo : T.getD p false = false)
    (hhi : T.getD (p + 1) false = false)
    (hp : p + 1 < T.length) :
    run localCopyMachine 4
      (liftCopyCfg pre ⟨(2, true), p, T⟩) =
      ⟨.home (0, false) scanHi, localOffset pre + p + 1,
        localTape pre
          (writeAt (writeAt T p true) (p + 1) true)⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero,
    step_c2_local, hlo,
    step_c3_endW_local pre hhi (by omega),
    show p + 1 - 1 = p by omega,
    step_c4_local pre (by omega),
    step_c5_enterHome_local pre (by
      rw [writeAt_length]
      omega)]
  rfl

/-- The actual round-growth pass lands on the exact next `cpyS` tape and has
entered local-home control at the new target pair's high cell. -/
theorem run_grow_cpyS_enterHome (pre suffix : List Bool)
    (n j : ℕ) (hj : j < n) :
    run localCopyMachine 4
      (liftCopyCfg pre
        ⟨(2, true), 2 * n + 2 * j + 2,
          cpyS n (j + 1) j suffix⟩) =
      ⟨.home (0, false) scanHi,
        localOffset pre + (2 * n + 2 * j + 3),
        localTape pre (cpyS n (j + 1) (j + 1) suffix)⟩ := by
  have h := run_four_grow_enterHome_local pre
    (p := 2 * n + 2 * j + 2)
    (T := cpyS n (j + 1) j suffix)
    (cpyS_getD_blank_lo n (j + 1) j suffix (by omega) (by omega))
    (by simpa [show 2 * n + 2 * j + 2 + 1 =
        2 * n + 2 * j + 3 by omega] using
      cpyS_getD_blank_hi n (j + 1) j suffix (by omega) (by omega))
    (by rw [cpyS_length n (j + 1) j suffix (by omega) (by omega)]; omega)
  rw [show 2 * n + 2 * j + 2 + 1 = 2 * n + 2 * j + 3 by omega,
    cpyS_grow n j suffix hj] at h
  simpa [Nat.add_assoc] using h

end PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyGrow

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyGrow.run_two_mark_local
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyGrow.run_grow_cpyS_enterHome
