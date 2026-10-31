import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPComparatorBridgeFinishMachine

/-!
# MCSP verifier: bridge-copy restore and finish handoff

This file closes the source-side endgame of the physical table copy.  After
all bridge-copy rounds, the real `localCopyMachine` enters its delimiter-aware
restore phase, heals every marked table-source pair, crosses the restored
source marker, and stops at the first power-bridge cell.  That exact tape and
head position are then consumed by the verified bridge-aware finish machine.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRestore

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRun
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyLift
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyScans
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRound
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRestore
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyFinish
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorReadyLayout
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyLayout
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRound
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRounds
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeFinishMachine
open LocalHomeState
open LocalCopyState
open BridgeFinishState

theorem bridgeResS_getD_pair_lo (n a i : ℕ) (suffix : List Bool)
    (hi : i < a) :
    (bridgeResS n a i suffix).getD (2 * i) false = true := by
  rw [bridgeResS, getD_append_length' _ _ List.length_replicate false,
    show a - i = (a - i - 1) + 1 by omega]
  rfl

theorem bridgeResS_getD_pair_hi (n a i : ℕ) (suffix : List Bool)
    (hi : i < a) :
    (bridgeResS n a i suffix).getD (2 * i + 1) false = false := by
  rw [bridgeResS,
    getD_append_left_length' _ _ List.length_replicate,
    show a - i = (a - i - 1) + 1 by omega]
  rfl

theorem bridgeResS_getD_marker_lo (n a : ℕ) (suffix : List Bool) :
    (bridgeResS n a a suffix).getD (2 * a) false = false := by
  rw [bridgeResS, Nat.sub_self,
    getD_append_length' _ _ List.length_replicate false]
  rfl

theorem bridgeResS_getD_marker_hi (n a : ℕ) (suffix : List Bool) :
    (bridgeResS n a a suffix).getD (2 * a + 1) false = true := by
  rw [bridgeResS, Nat.sub_self,
    getD_append_left_length' _ _ List.length_replicate]
  rfl

/-- Restore the first `i` marked table-source pairs while preserving both
power counters, the copied table target, and the payload. -/
theorem run_restore_bridge_local (pre suffix : List Bool)
    (n a : ℕ) (s : Bool) (i : ℕ) (hi : i ≤ a) :
    run localCopyMachine (2 * i)
      (liftCopyCfg pre ⟨(6, s), 0, bridgeResS n a 0 suffix⟩) =
      liftCopyCfg pre
        ⟨(6, if i = 0 then s else true), 2 * i,
          bridgeResS n a i suffix⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [show 2 * (i + 1) = 2 * i + 2 by omega,
        run_add, ih (by omega)]
      have h := run_two_heal_local (pre := pre)
        (s := if i = 0 then s else true)
        (p := 2 * i) (T := bridgeResS n a i suffix)
        (bridgeResS_getD_pair_lo n a i suffix (by omega))
        (bridgeResS_getD_pair_hi n a i suffix (by omega))
        (by rw [bridgeResS_length n a i suffix (by omega)]; omega)
      rw [bridgeResS_heal n a i suffix (by omega)] at h
      simpa [Nat.succ_ne_zero] using h

theorem run_restore_bridge_all (pre suffix : List Bool)
    (n a : ℕ) (s : Bool) :
    run localCopyMachine (2 * a)
      (liftCopyCfg pre ⟨(6, s), 0, bridgeResS n a 0 suffix⟩) =
      liftCopyCfg pre
        ⟨(6, if a = 0 then s else true), 2 * a,
          bridgeResS n a a suffix⟩ := by
  exact run_restore_bridge_local pre suffix n a s a (le_refl a)

/-- The completed copy rounds' find pass reaches the table-source marker. -/
theorem run_find_bridge_all_local (pre suffix : List Bool)
    (n a : ℕ) (s : Bool) :
    run localCopyMachine (2 * a)
      (liftCopyCfg pre
        ⟨(0, s), 0, bridgeCpyS n a a a suffix⟩) =
      liftCopyCfg pre
        ⟨(0, if a = 0 then s else true), 2 * a,
          bridgeCpyS n a a a suffix⟩ := by
  simpa using run_findSkip_local pre (bridgeCpyS n a a a suffix)
    0 a s (fun i hi =>
      ⟨by simpa using
          bridgeCpyS_getD_Amark_lo n a a a i suffix (le_refl a) hi,
       by simpa using
          bridgeCpyS_getD_Amark_hi n a a a i suffix (le_refl a) hi⟩)

/-- From the fully marked source marker, enter local-home control and return
to table-counter origin in restore state `6`. -/
theorem run_toRestore_bridge_local (pre suffix : List Bool)
    (n a : ℕ) (s : Bool) :
    run localCopyMachine (2 * a + 8)
      (liftCopyCfg pre
        ⟨(0, s), 2 * a, bridgeCpyS n a a a suffix⟩) =
      liftCopyCfg pre
        ⟨(6, false), 0, bridgeCpyS n a a a suffix⟩ := by
  have h0 :
      run localCopyMachine 1
        (liftCopyCfg pre
          ⟨(0, s), 2 * a, bridgeCpyS n a a a suffix⟩) =
      liftCopyCfg pre
        ⟨(1, false), 2 * a + 1, bridgeCpyS n a a a suffix⟩ := by
    rw [run_succ, run_zero, step_c0_local,
      bridgeCpyS_getD_marker_lo n a a a suffix (le_refl a)]
  have h1 :
      run localCopyMachine 1
        (liftCopyCfg pre
          ⟨(1, false), 2 * a + 1, bridgeCpyS n a a a suffix⟩) =
      ⟨.home (6, false) scanHi,
        localOffset pre + (2 * a + 1),
        localTape pre (bridgeCpyS n a a a suffix)⟩ := by
    rw [run_succ, run_zero,
      step_c1_restore_enterHome_local pre
        (bridgeCpyS_getD_marker_hi n a a a suffix (le_refl a))]
  have hhome := run_localCopy_home_resume (6, false)
    (localTape pre (bridgeCpyS n a a a suffix)) pre.length (a + 1)
    (localTape_home_lo pre _)
    (localTape_home_hi pre _)
    (fun i hi => localTape_bridge_active_pair pre suffix n a a i
      (le_refl a) (by omega))
  have hhead : localOffset pre + (2 * a + 1) =
      pre.length + 1 + 2 * (a + 1) := by
    simp [localOffset]
    ring
  rw [show 2 * a + 8 = 1 + (1 + (2 * (a + 1) + 4)) by omega,
    run_add, h0, run_add, h1, hhead]
  simpa [liftCopyCfg, localOffset] using hhome

/-- Clock from the post-round configuration through source restoration and
the handoff at the first power-bridge cell. -/
def bridgeRestoreHandoffClock (a : ℕ) : ℕ :=
  2 * a + (2 * a + 8) + 2 * a + 2

theorem bridgeRestoreHandoffClock_eq (a : ℕ) :
    bridgeRestoreHandoffClock a = 6 * a + 10 := by
  unfold bridgeRestoreHandoffClock
  omega

/-- Restore the table source and stop in old copy state `8` at the first
power-counter cell, ready for the bridge-aware finish scanner. -/
theorem run_bridge_restore_handoff (pre suffix : List Bool)
    (n a : ℕ) (s : Bool) :
    run localCopyMachine (bridgeRestoreHandoffClock a)
      (liftCopyCfg pre
        ⟨(0, s), 0, bridgeCpyS n a a a suffix⟩) =
      liftCopyCfg pre
        ⟨(8, false), 2 * a + 2, bridgeResS n a a suffix⟩ := by
  rw [bridgeRestoreHandoffClock,
    show 2 * a + (2 * a + 8) + 2 * a + 2 =
      2 * a + ((2 * a + 8) + (2 * a + 2)) by omega,
    run_add, run_find_bridge_all_local pre suffix n a s,
    run_add,
    run_toRestore_bridge_local pre suffix n a
      (if a = 0 then s else true),
    ← bridgeResS_zero,
    run_add, run_restore_bridge_all pre suffix n a false,
    run_two_cross67_local pre
      (bridgeResS_getD_marker_lo n a suffix)
      (bridgeResS_getD_marker_hi n a suffix)]

/-- Total local-copy clock from untouched bridge scratch through every copy
round, restoration, and the physical finish handoff. -/
def bridgeCopyToFinishClock (n a : ℕ) : ℕ :=
  bridgeAllRoundsClock n a + bridgeRestoreHandoffClock a

theorem bridgeCopyToFinishClock_eq (n a : ℕ) :
    bridgeCopyToFinishClock n a =
      6 * a * a + 4 * bridgePairs n * a + 18 * a + 10 := by
  rw [bridgeCopyToFinishClock, bridgeAllRoundsClock_eq,
    bridgeRestoreHandoffClock_eq]
  ring

/-- Clock for the two physically connected phases before they are folded
into one tagged controller. -/
def bridgeCopyPipelineClock (n a : ℕ) : ℕ :=
  bridgeCopyToFinishClock n a + bridgeFinishClock n a

theorem bridgeCopyPipelineClock_eq (n a : ℕ) :
    bridgeCopyPipelineClock n a =
      6 * a * a + 4 * bridgePairs n * a + 20 * a +
        2 * bridgePairs n + 12 := by
  rw [bridgeCopyPipelineClock, bridgeCopyToFinishClock_eq,
    bridgeFinishClock]
  ring

theorem run_bridge_copy_to_finish (pre suffix : List Bool)
    (n a : ℕ) (s : Bool) :
    run localCopyMachine (bridgeCopyToFinishClock n a)
      (liftCopyCfg pre
        ⟨(0, s), 0, bridgeCpyS n a 0 0 suffix⟩) =
      liftCopyCfg pre
        ⟨(8, false), 2 * a + 2, bridgeResS n a a suffix⟩ := by
  rw [bridgeCopyToFinishClock, run_add,
    run_bridge_allRounds pre suffix n a s,
    run_bridge_restore_handoff pre suffix n a
      (if a = 0 then s else false)]

/-- The exact handoff tape/head produced by the local-copy phase is accepted
by the bridge-aware finish machine and becomes the comparator layout. -/
theorem run_bridge_finish_after_handoff (pre : List Bool)
    (n : ℕ) (table payload : List Bool) :
    let localPre := pre ++ [false, false]
    let handoff := run localCopyMachine
      (bridgeCopyToFinishClock n table.length)
      (liftCopyCfg pre
        ⟨(0, false), 0,
          bridgeCpyS n table.length 0 0 payload⟩)
    run bridgeFinishMachine
        (bridgeFinishClock n table.length)
        ⟨scanLo, handoff.hd, handoff.tp⟩ =
      ⟨done,
        localPre.length + 4 * table.length + 4 * (2 ^ n) + 7,
        localPre ++ comparatorLayout n table payload⟩ := by
  intro localPre handoff
  rw [show handoff = liftCopyCfg pre
      ⟨(8, false), 2 * table.length + 2,
        bridgeResS n table.length table.length payload⟩ by
      exact run_bridge_copy_to_finish pre payload n table.length false]
  simpa [liftCopyCfg, localTape, homePrefix, localOffset, localPre,
    List.append_assoc] using
    run_bridgeFinish_comparatorLayout localPre n table payload

end PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRestore

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRestore.run_restore_bridge_all
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRestore.run_bridge_restore_handoff
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRestore.run_bridge_copy_to_finish
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRestore.run_bridge_finish_after_handoff
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRestore.bridgeCopyPipelineClock_eq
