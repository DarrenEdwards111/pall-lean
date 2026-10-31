import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPComparatorBridgeCopyRestore
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitRange

/-!
# MCSP verifier: one tagged machine for bridge copy and finish

The previously proved copy/restore phase and bridge-aware finish phase are
folded into one finite state set.  Correct executions remain in the embedded
`localCopyMachine` until its ordinary end scan reaches the first power-counter
marker.  The tagged controller then backs up one cell, switches to the
bridge-aware scanner, and finishes on the same tape without an external run.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCombinedMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyLift
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyFinish
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorReadyLayout
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyLayout
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRound
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeFinishMachine
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRestore
open LocalCopyState
open BridgeFinishState

inductive BridgeCombinedState
  | copying (s : localCopyMachine.State)
  | finishing (s : bridgeFinishMachine.State)
  deriving DecidableEq, Fintype

open BridgeCombinedState

/-- One fixed controller containing both verified finite-control phases.  A
normal phase-one halt with stored bit false is the unique finish handoff;
other phase-one halts enter bridge rejection. -/
def bridgeCombinedMachine : Machine where
  State := BridgeCombinedState
  fin := inferInstance
  dec := inferInstance
  start := .copying localCopyMachine.start
  halt
    | .copying _ => false
    | .finishing s => bridgeFinishMachine.halt s
  δ
    | .copying s, b =>
        if localCopyMachine.halt s then
          if s = .copy (10, false) then
            (.finishing scanLo, none, 0)
          else
            (.finishing reject, none, 2)
        else
          let tr := localCopyMachine.δ s b
          (.copying tr.1, tr.2.1, tr.2.2)
    | .finishing s, b =>
        let tr := bridgeFinishMachine.δ s b
        (.finishing tr.1, tr.2.1, tr.2.2)
  accept
    | .copying _ => false
    | .finishing s => bridgeFinishMachine.accept s

def embedCopyCfg (c : Cfg localCopyMachine) : Cfg bridgeCombinedMachine :=
  ⟨.copying c.st, c.hd, c.tp⟩

def embedFinishCfg (c : Cfg bridgeFinishMachine) :
    Cfg bridgeCombinedMachine :=
  ⟨.finishing c.st, c.hd, c.tp⟩

theorem step_embedCopy_of_running (c : Cfg localCopyMachine)
    (h : localCopyMachine.halt c.st = false) :
    step bridgeCombinedMachine (embedCopyCfg c) =
      embedCopyCfg (step localCopyMachine c) := by
  simp [step, bridgeCombinedMachine, embedCopyCfg, h]

theorem step_embedFinish (c : Cfg bridgeFinishMachine) :
    step bridgeCombinedMachine (embedFinishCfg c) =
      embedFinishCfg (step bridgeFinishMachine c) := by
  by_cases h : bridgeFinishMachine.halt c.st = true
  · rw [step_of_halted bridgeFinishMachine h,
      step_of_halted bridgeCombinedMachine (by
        simpa [bridgeCombinedMachine, embedFinishCfg] using h)]
  · have hf : bridgeFinishMachine.halt c.st = false := by
      simpa using h
    simp [step, bridgeCombinedMachine, embedFinishCfg, hf]

theorem run_embedFinish (t : ℕ) (c : Cfg bridgeFinishMachine) :
    run bridgeCombinedMachine t (embedFinishCfg c) =
      embedFinishCfg (run bridgeFinishMachine t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, run_succ, ih, step_embedFinish]

/-- If the phase-one endpoint is still running, it could not have halted at
an earlier prefix; hence the entire run embeds in the tagged controller. -/
theorem run_embedCopy_of_final_running (t : ℕ)
    (c : Cfg localCopyMachine)
    (hfinal : localCopyMachine.halt
      (run localCopyMachine t c).st = false) :
    run bridgeCombinedMachine t (embedCopyCfg c) =
      embedCopyCfg (run localCopyMachine t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hprev : localCopyMachine.halt
          (run localCopyMachine t c).st = false := by
        by_contra h
        have ht : localCopyMachine.halt
            (run localCopyMachine t c).st = true := by
          simpa using h
        rw [run_succ, step_of_halted localCopyMachine ht] at hfinal
        simp [ht] at hfinal
      rw [run_succ, run_succ, ih hprev,
        step_embedCopy_of_running _ hprev]

theorem bridgeResS_firstPower_getD (n a c : ℕ) (suffix : List Bool)
    (hc : c < 2 * (2 ^ n)) :
    (bridgeResS n a a suffix).getD (2 * a + 2 + c) false = true := by
  rw [bridgeResS_all_eq]
  simp only [List.append_assoc]
  rw [
    show 2 * a + 2 + c = (unaryD a).length + c by
      rw [unaryD_length],
    getD_append_left_length' _ _ rfl]
  rw [List.getD_append (h := by rw [powBridge_length]; omega),
    powBridge, List.getD_append (h := by rw [unaryD_length]; omega)]
  exact unaryD_getD_data (2 ^ n) c hc

theorem bridgeResS_firstPower_marker_lo (n a : ℕ)
    (suffix : List Bool) :
    (bridgeResS n a a suffix).getD
      (2 * a + 2 + 2 * (2 ^ n)) false = false := by
  rw [bridgeResS_all_eq]
  simp only [List.append_assoc]
  rw [
    show 2 * a + 2 + 2 * (2 ^ n) =
      (unaryD a).length + 2 * (2 ^ n) by rw [unaryD_length],
    getD_append_left_length' _ _ rfl]
  rw [List.getD_append (h := by rw [powBridge_length]; omega),
    powBridge, List.getD_append (h := by rw [unaryD_length]; omega)]
  exact unaryD_getD_markLo (2 ^ n)

/-- Old states `8/9` cross the first power counter's `11` data and stop on
its `01` marker high cell in nonhalting state `9,false`. -/
theorem run_local_to_firstPower_markerHi (pre suffix : List Bool)
    (n a : ℕ) :
    run localCopyMachine (2 * (2 ^ n) + 1)
      (liftCopyCfg pre
        ⟨(8, false), 2 * a + 2, bridgeResS n a a suffix⟩) =
      liftCopyCfg pre
        ⟨(9, false), 2 * a + 2 + 2 * (2 ^ n) + 1,
          bridgeResS n a a suffix⟩ := by
  have hseek := run_seekCs_local pre (bridgeResS n a a suffix)
    (2 * a + 2) (2 ^ n) false (fun i hi =>
      ⟨bridgeResS_firstPower_getD n a (2 * i) suffix (by omega),
       bridgeResS_firstPower_getD n a (2 * i + 1) suffix (by omega)⟩)
  rw [show 2 * (2 ^ n) + 1 = 2 * (2 ^ n) + 1 by rfl,
    run_add, hseek, run_succ, run_zero, step_c8_local,
    bridgeResS_firstPower_marker_lo]

theorem step_local_marker_to_halt (pre suffix : List Bool)
    (n a : ℕ) :
    step localCopyMachine
      (liftCopyCfg pre
        ⟨(9, false), 2 * a + 2 + 2 * (2 ^ n) + 1,
          bridgeResS n a a suffix⟩) =
      liftCopyCfg pre
        ⟨(10, false), 2 * a + 2 + 2 * (2 ^ n) + 1,
          bridgeResS n a a suffix⟩ := by
  have hread := bridgeResS_all_getD_high n a (2 ^ n) suffix (by
    simp [bridgePairs]
    omega)
  have hread' : (localTape pre (bridgeResS n a a suffix)).getD
      (localOffset pre + (2 * a + 2 + 2 * (2 ^ n) + 1)) false = true := by
    rw [localTape_getD]
    exact hread
  rw [List.getD_eq_getElem?_getD] at hread'
  simp [step, localCopyMachine, liftCopyCfg, copyMachine,
    moveHead, hread']

theorem step_combined_handoff (pre suffix : List Bool)
    (n a : ℕ) :
    step bridgeCombinedMachine
      (embedCopyCfg (liftCopyCfg pre
        ⟨(10, false), 2 * a + 2 + 2 * (2 ^ n) + 1,
          bridgeResS n a a suffix⟩)) =
      embedFinishCfg
        ⟨scanLo, localOffset pre + 2 * a + 2 + 2 * (2 ^ n),
          localTape pre (bridgeResS n a a suffix)⟩ := by
  simp [step, bridgeCombinedMachine, embedCopyCfg, embedFinishCfg,
    liftCopyCfg, localCopyMachine, copyMachine, moveHead]
  omega

/-- Remaining finish span when the first power counter's data have already
been crossed and its marker is scanned again by the bridge-aware phase. -/
def bridgeFinishTailPairs (n a : ℕ) : ℕ :=
  bridgePairs n + a - 2 ^ n

theorem bridgeFinishTailPairs_eq (n a : ℕ) :
    bridgeFinishTailPairs n a = 2 ^ n + a + 2 := by
  simp [bridgeFinishTailPairs, bridgePairs]
  omega

theorem run_bridgeFinish_tail (pre : List Bool)
    (n : ℕ) (table payload : List Bool) :
    let a := table.length
    let localPre := pre ++ [false, false]
    let q := localPre.length + 2 * a + 2 + 2 * (2 ^ n)
    run bridgeFinishMachine (2 * bridgeFinishTailPairs n a + 2)
      ⟨scanLo, q, localPre ++ bridgeResS n a a payload⟩ =
      ⟨done, localPre.length + 4 * a + 4 * (2 ^ n) + 7,
        localPre ++ comparatorLayout n table payload⟩ := by
  intro a localPre q
  have hhigh := run_high_pairs (localPre ++ bridgeResS n a a payload)
    q (bridgeFinishTailPairs n a) (fun i hi => by
      rw [show q + 2 * i + 1 = localPre.length +
          (2 * a + 2 + 2 * (2 ^ n + i) + 1) by simp [q]; omega,
        getD_append_left_length' _ _ rfl]
      exact bridgeResS_all_getD_high n a (2 ^ n + i) payload (by
        simp [bridgeFinishTailPairs, bridgePairs] at hi ⊢
        omega))
  have hlo : (localPre ++ bridgeResS n a a payload).getD
      (q + 2 * bridgeFinishTailPairs n a) false = false := by
    rw [show q + 2 * bridgeFinishTailPairs n a = localPre.length +
        (2 * a + 2 + 2 * (bridgePairs n + a)) by
          simp [q, bridgeFinishTailPairs, bridgePairs]
          omega,
      getD_append_left_length' _ _ rfl]
    exact bridgeResS_all_getD_blank_lo n a payload
  have hhi : (localPre ++ bridgeResS n a a payload).getD
      (q + 2 * bridgeFinishTailPairs n a + 1) false = false := by
    rw [show q + 2 * bridgeFinishTailPairs n a + 1 = localPre.length +
        (2 * a + 2 + 2 * (bridgePairs n + a) + 1) by
          simp [q, bridgeFinishTailPairs, bridgePairs]
          omega,
      getD_append_left_length' _ _ rfl]
    exact bridgeResS_all_getD_blank_hi n a payload
  rw [show 2 * bridgeFinishTailPairs n a + 2 =
      2 * bridgeFinishTailPairs n a + 2 by rfl,
    run_add, hhigh,
    run_two_blank (q + 2 * bridgeFinishTailPairs n a)
      (localPre ++ bridgeResS n a a payload) hlo hhi]
  have hpos : q + 2 * bridgeFinishTailPairs n a + 1 =
      localPre.length + 4 * a + 4 * (2 ^ n) + 7 := by
    simp [q, bridgeFinishTailPairs, bridgePairs]
    omega
  rw [hpos]
  rw [show localPre.length + 4 * a + 4 * (2 ^ n) + 7 =
      localPre.length + (4 * a + 4 * (2 ^ n) + 7) by omega,
    writeAt_append_right localPre (bridgeResS n a a payload)
    localPre.length (4 * a + 4 * (2 ^ n) + 7) true rfl (by
      rw [bridgeResS_length n a a payload (le_refl a)]
      omega), bridgeResS_finish_comparatorLayout]

/-- Exact clock of the single tagged bridge-copy machine. -/
def bridgeCombinedClock (n a : ℕ) : ℕ :=
  bridgeCopyToFinishClock n a +
    (2 * (2 ^ n) + 1) + 1 + 1 +
      (2 * bridgeFinishTailPairs n a + 2)

theorem bridgeCombinedClock_eq (n a : ℕ) :
    bridgeCombinedClock n a =
      6 * a * a + 4 * bridgePairs n * a + 20 * a +
        2 * bridgePairs n + 15 := by
  rw [bridgeCombinedClock, bridgeCopyToFinishClock_eq]
  rw [bridgeFinishTailPairs_eq]
  simp [bridgePairs]
  ring

/-- One run of one fixed finite-control machine produces the exact four
counter comparator layout. -/
theorem run_bridgeCombined (pre : List Bool)
    (n : ℕ) (table payload : List Bool) :
    let a := table.length
    run bridgeCombinedMachine (bridgeCombinedClock n a)
      (embedCopyCfg (liftCopyCfg pre
        ⟨(0, false), 0, bridgeCpyS n a 0 0 payload⟩)) =
      embedFinishCfg
        ⟨done,
          (pre ++ [false, false]).length + 4 * a + 4 * (2 ^ n) + 7,
          (pre ++ [false, false]) ++ comparatorLayout n table payload⟩ := by
  intro a
  let c0 := liftCopyCfg pre
    ⟨(0, false), 0, bridgeCpyS n a 0 0 payload⟩
  have hcopy := run_bridge_copy_to_finish pre payload n a false
  have hsim := run_embedCopy_of_final_running
    (bridgeCopyToFinishClock n a) c0 (by rw [hcopy]; rfl)
  have hmarker := run_local_to_firstPower_markerHi pre payload n a
  have hsimMarker := run_embedCopy_of_final_running
    (2 * (2 ^ n) + 1)
    (liftCopyCfg pre
      ⟨(8, false), 2 * a + 2, bridgeResS n a a payload⟩)
    (by rw [hmarker]; rfl)
  have htohalt : run bridgeCombinedMachine 1
      (embedCopyCfg (liftCopyCfg pre
        ⟨(9, false), 2 * a + 2 + 2 * (2 ^ n) + 1,
          bridgeResS n a a payload⟩)) =
      embedCopyCfg (liftCopyCfg pre
        ⟨(10, false), 2 * a + 2 + 2 * (2 ^ n) + 1,
          bridgeResS n a a payload⟩) := by
    rw [run_succ, run_zero,
      step_embedCopy_of_running _ (by rfl),
      step_local_marker_to_halt pre payload n a]
  have hswitch : run bridgeCombinedMachine 1
      (embedCopyCfg (liftCopyCfg pre
        ⟨(10, false), 2 * a + 2 + 2 * (2 ^ n) + 1,
          bridgeResS n a a payload⟩)) =
      embedFinishCfg
        ⟨scanLo, localOffset pre + 2 * a + 2 + 2 * (2 ^ n),
          localTape pre (bridgeResS n a a payload)⟩ := by
    rw [run_succ, run_zero, step_combined_handoff]
  rw [bridgeCombinedClock,
    show bridgeCopyToFinishClock n a + (2 * 2 ^ n + 1) + 1 + 1 +
        (2 * bridgeFinishTailPairs n a + 2) =
      bridgeCopyToFinishClock n a +
        ((2 * 2 ^ n + 1) + (1 + (1 +
          (2 * bridgeFinishTailPairs n a + 2)))) by omega,
    run_add, hsim, hcopy, run_add, hsimMarker, hmarker,
    run_add, htohalt, run_add, hswitch,
    run_embedFinish]
  simpa [localTape, homePrefix, localOffset,
    List.append_assoc] using congrArg embedFinishCfg
      (run_bridgeFinish_tail pre n table payload)

theorem bridgeCombined_halts (pre : List Bool)
    (n : ℕ) (table payload : List Bool) :
    bridgeCombinedMachine.halt
      (run bridgeCombinedMachine
        (bridgeCombinedClock n table.length)
        (embedCopyCfg (liftCopyCfg pre
          ⟨(0, false), 0,
            bridgeCpyS n table.length 0 0 payload⟩))).st = true := by
  rw [run_bridgeCombined]
  rfl

end PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCombinedMachine

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCombinedMachine.run_embedCopy_of_final_running
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCombinedMachine.bridgeCombinedClock_eq
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCombinedMachine.run_bridgeCombined
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCombinedMachine.bridgeCombined_halts
