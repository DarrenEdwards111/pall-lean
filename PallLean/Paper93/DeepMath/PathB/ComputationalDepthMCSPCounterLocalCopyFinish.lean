import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPCounterLocalCopyRestore

/-!
# MCSP verifier: complete delimited local-copy endgame

This file closes the physical local-copy controller after all copy rounds.
It proves the boundary-triggered local reset into restore state, heals the
marked source, crosses its `01` boundary, seeks across the copied data, writes
the copied `01` terminator inside reserved scratch, and halts.

The final theorem is one run of the real fixed `localCopyMachine` on the
single live tape following an arbitrary prefix and `00` local-home delimiter.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyFinish

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.MCSPCounterCopyScratchMachine
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRun
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyLift
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyScans
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRound
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRounds
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRestore
open LocalHomeState
open LocalCopyState

/-- The fully marked source boundary triggers local-home control while
remembering restore state `6`. -/
theorem step_c1_restore_enterHome_local (pre : List Bool) {p : ℕ}
    {T : List Bool} (hread : T.getD p false = true) :
    step localCopyMachine
      (liftCopyCfg pre ⟨(1, false), p, T⟩) =
      ⟨.home (6, false) scanHi,
        localOffset pre + p, localTape pre T⟩ := by
  have hread' : (localTape pre T).getD (localOffset pre + p) false = true := by
    rw [localTape_getD]
    exact hread
  rw [List.getD_eq_getElem?_getD] at hread'
  simp [step, localCopyMachine, liftCopyCfg, copyMachine, moveHead, hread']

/-- Starting on the fully marked source boundary, local reset returns exactly
to the embedded counter origin in restore state.  The scan crosses `n` source
pairs plus the source `01` boundary itself. -/
theorem run_toRestore_local (pre suffix : List Bool) (n : ℕ) (s : Bool) :
    run localCopyMachine (2 * n + 8)
      (liftCopyCfg pre ⟨(0, s), 2 * n, cpyS n n n suffix⟩) =
      liftCopyCfg pre ⟨(6, false), 0, cpyS n n n suffix⟩ := by
  have h0 :
      run localCopyMachine 1
        (liftCopyCfg pre ⟨(0, s), 2 * n, cpyS n n n suffix⟩) =
      liftCopyCfg pre
        ⟨(1, false), 2 * n + 1, cpyS n n n suffix⟩ := by
    rw [run_succ, run_zero, step_c0_local,
      cpyS_getD_marker_lo n n n suffix (le_refl n) (le_refl n)]
  have h1 :
      run localCopyMachine 1
        (liftCopyCfg pre
          ⟨(1, false), 2 * n + 1, cpyS n n n suffix⟩) =
      ⟨.home (6, false) scanHi,
        localOffset pre + (2 * n + 1),
        localTape pre (cpyS n n n suffix)⟩ := by
    rw [run_succ, run_zero,
      step_c1_restore_enterHome_local pre
        (cpyS_getD_marker_hi n n n suffix (le_refl n) (le_refl n))]
  have hhome := run_localCopy_home_resume (6, false)
    (localTape pre (cpyS n n n suffix)) pre.length (n + 1)
    (localTape_home_lo pre _)
    (localTape_home_hi pre _)
    (fun i hi =>
      localTape_cpyS_active_pair pre suffix n n i (le_refl n) (by omega))
  have hhead : localOffset pre + (2 * n + 1) =
      pre.length + 1 + 2 * (n + 1) := by
    simp [localOffset]
    ring
  rw [show 2 * n + 8 = 1 + (1 + (2 * (n + 1) + 4)) by omega,
    run_add, h0, run_add, h1, hhead]
  simpa [liftCopyCfg, localOffset] using hhome

theorem step_c7_cross_local (pre : List Bool) {p : ℕ}
    {T : List Bool} (hread : T.getD p false = true) :
    step localCopyMachine
      (liftCopyCfg pre ⟨(7, false), p, T⟩) =
      liftCopyCfg pre ⟨(8, false), p + 1, T⟩ := by
  have hread' := hread
  rw [List.getD_eq_getElem?_getD] at hread'
  have h := step_localCopy_lift pre
    (⟨(7, false), p, T⟩ : Cfg copyMachine)
    (by simp [copyMachine])
    (by simp [copyMachine, hread'])
    (by simp [copyMachine, hread'])
    (by simp [copyMachine, hread'])
  rw [h, step_c7_cross hread]

theorem run_two_cross67_local (pre : List Bool) {s : Bool} {p : ℕ}
    {T : List Bool}
    (hlo : T.getD p false = false)
    (hhi : T.getD (p + 1) false = true) :
    run localCopyMachine 2
      (liftCopyCfg pre ⟨(6, s), p, T⟩) =
      liftCopyCfg pre ⟨(8, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_c6_local, hlo,
    step_c7_cross_local pre hhi]

theorem step_c8_local (pre : List Bool) {s : Bool} {p : ℕ}
    {T : List Bool} :
    step localCopyMachine
      (liftCopyCfg pre ⟨(8, s), p, T⟩) =
      liftCopyCfg pre ⟨(9, T.getD p false), p + 1, T⟩ := by
  have h := step_localCopy_lift pre
    (⟨(8, s), p, T⟩ : Cfg copyMachine)
    (by simp [copyMachine])
    (by simp [copyMachine])
    (by simp [copyMachine])
    (by simp [copyMachine])
  rw [h, step_c8]

theorem step_c9_skip_local (pre : List Bool) {p : ℕ}
    {T : List Bool} (hread : T.getD p false = true) :
    step localCopyMachine
      (liftCopyCfg pre ⟨(9, true), p, T⟩) =
      liftCopyCfg pre ⟨(8, true), p + 1, T⟩ := by
  have hread' := hread
  rw [List.getD_eq_getElem?_getD] at hread'
  have h := step_localCopy_lift pre
    (⟨(9, true), p, T⟩ : Cfg copyMachine)
    (by simp [copyMachine])
    (by simp [copyMachine, hread'])
    (by simp [copyMachine, hread'])
    (by simp [copyMachine, hread'])
  rw [h, step_c9_skip hread]

theorem step_c9_finish_local (pre : List Bool) {p : ℕ}
    {T : List Bool} (hread : T.getD p false = false)
    (hp : p < T.length) :
    step localCopyMachine
      (liftCopyCfg pre ⟨(9, false), p, T⟩) =
      liftCopyCfg pre ⟨(10, false), p, writeAt T p true⟩ := by
  have hread' := hread
  rw [List.getD_eq_getElem?_getD] at hread'
  have h := step_localCopy_lift pre
    (⟨(9, false), p, T⟩ : Cfg copyMachine)
    (by simp [copyMachine])
    (by simp [copyMachine, hread'])
    (by simp [copyMachine, hread'])
    (by
      intro w hw
      simp [copyMachine, hread'] at hw
      subst w
      exact hp)
  rw [h, step_c9_finish hread]

theorem run_two_seekC_local (pre : List Bool) {s : Bool} {p : ℕ}
    {T : List Bool}
    (hlo : T.getD p false = true)
    (hhi : T.getD (p + 1) false = true) :
    run localCopyMachine 2
      (liftCopyCfg pre ⟨(8, s), p, T⟩) =
      liftCopyCfg pre ⟨(8, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_c8_local, hlo,
    step_c9_skip_local pre hhi]

theorem run_seekCs_local (pre T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k →
      T.getD (q + 2 * i) false = true ∧
        T.getD (q + 2 * i + 1) false = true) :
    run localCopyMachine (2 * k)
      (liftCopyCfg pre ⟨(8, s), q, T⟩) =
      liftCopyCfg pre
        ⟨(8, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hk := h k (by omega)
      rw [show 2 * (k + 1) = 2 * k + 2 by omega,
        run_add, ih (fun i hi => h i (by omega))]
      simpa [Nat.succ_ne_zero, Nat.mul_succ, Nat.add_assoc] using
        run_two_seekC_local (pre := pre)
          (s := if k = 0 then s else true)
          (p := q + 2 * k) hk.1 hk.2

theorem run_two_finish_local (pre : List Bool) {s : Bool} {p : ℕ}
    {T : List Bool}
    (hlo : T.getD p false = false)
    (hhi : T.getD (p + 1) false = false)
    (hp : p + 1 < T.length) :
    run localCopyMachine 2
      (liftCopyCfg pre ⟨(8, s), p, T⟩) =
      liftCopyCfg pre
        ⟨(10, false), p + 1, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero, step_c8_local, hlo,
    step_c9_finish_local pre hhi hp]

/-- Exact endgame clock after the copy rounds. -/
def localFinishClock (n : ℕ) : ℕ :=
  2 * n + (2 * n + 8) + 2 * n + 2 + 2 * n + 2

theorem localFinishClock_eq (n : ℕ) :
    localFinishClock n = 8 * n + 12 := by
  unfold localFinishClock
  omega

/-- From the completed rounds tape, perform local reset, restore, seek, write
the copied terminator, and halt with the exact two-counter output. -/
theorem run_localCopy_finish (pre suffix : List Bool) (n : ℕ) (s : Bool) :
    run localCopyMachine (localFinishClock n)
      (liftCopyCfg pre ⟨(0, s), 0, cpyS n n n suffix⟩) =
      liftCopyCfg pre
        ⟨(10, false), 4 * n + 3,
          unaryD n ++ unaryD n ++ suffix⟩ := by
  have hseek := run_seekCs_local pre (resS n n suffix)
    (2 * n + 2) n false (fun i hi =>
      ⟨resS_getD_C n (2 * n + 2 + 2 * i) suffix
          (by omega) (by omega),
       resS_getD_C n (2 * n + 2 + 2 * i + 1) suffix
          (by omega) (by omega)⟩)
  have hfinish := run_two_finish_local (pre := pre)
    (s := if n = 0 then false else true)
    (p := 4 * n + 2) (T := resS n n suffix)
    (resS_getD_blank_lo n suffix)
    (resS_getD_blank_hi n suffix)
    (by rw [resS_length n n suffix (le_refl n)]; omega)
  rw [show 2 * n + 2 + 2 * n = 4 * n + 2 by ring] at hseek
  rw [show 4 * n + 2 + 1 = 4 * n + 3 by omega,
    resS_finish n suffix] at hfinish
  rw [localFinishClock,
    show 2 * n + (2 * n + 8) + 2 * n + 2 + 2 * n + 2 =
      2 * n + ((2 * n + 8) + (2 * n + (2 + (2 * n + 2)))) by omega,
    run_add,
    run_findSkip_cpyS_local pre suffix n n (le_refl n) s,
    run_add,
    run_toRestore_local pre suffix n (if n = 0 then s else true),
    ← resS_zero,
    run_add, run_restore_resS_all pre suffix n false,
    run_add,
    run_two_cross67_local pre
      (resS_getD_marker_lo n suffix)
      (resS_getD_marker_hi n suffix),
    run_add, hseek, hfinish]

/-- Total exact clock from the reserved-scratch input through every local
copy round and the complete endgame. -/
def localCopyClock (n : ℕ) : ℕ :=
  localAllRoundsClock n + localFinishClock n

theorem localCopyClock_eq (n : ℕ) :
    localCopyClock n = 6 * n * n + 20 * n + 12 := by
  rw [localCopyClock, localAllRoundsClock_eq, localFinishClock_eq]
  ring

/-- Complete physical delimited copy theorem on one live tape. -/
theorem run_localCopy_complete (pre suffix : List Bool)
    (n : ℕ) (s : Bool) :
    run localCopyMachine (localCopyClock n)
      (liftCopyCfg pre ⟨(0, s), 0, cpyS n 0 0 suffix⟩) =
      liftCopyCfg pre
        ⟨(10, false), 4 * n + 3,
          unaryD n ++ unaryD n ++ suffix⟩ := by
  rw [localCopyClock, run_add,
    run_localCopy_allRounds pre suffix n s,
    run_localCopy_finish pre suffix n (if n = 0 then s else false)]

theorem localCopy_complete_halts (pre suffix : List Bool)
    (n : ℕ) (s : Bool) :
    localCopyMachine.halt
      (run localCopyMachine (localCopyClock n)
        (liftCopyCfg pre ⟨(0, s), 0, cpyS n 0 0 suffix⟩)).st = true := by
  rw [run_localCopy_complete]
  rfl

end PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyFinish

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyFinish.run_toRestore_local
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyFinish.run_localCopy_finish
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyFinish.run_localCopy_complete
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyFinish.localCopy_complete_halts
