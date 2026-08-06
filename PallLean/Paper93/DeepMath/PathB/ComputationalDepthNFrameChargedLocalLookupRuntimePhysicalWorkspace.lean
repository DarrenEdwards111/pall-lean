import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeWorkspaceLocator

/-!
# Physical post-cashout workspace discovery

The output/source locator halts at the source origin.  The consumed-prefix
locator must begin at that exact head rather than reset to physical origin.
This file proves arbitrary-prefix execution for the latter and joins the two
fixed controllers with head-preserving sequential composition.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalWorkspace

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativeOutput
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTailPreservation
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeOutputSourceLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceLocator

/-- The consumed-prefix locator executes unchanged behind any physical prefix.
Its clock remains source-relative: no scan of the physical prefix is needed. -/
theorem runtimeWorkspaceLocator_run_prefixed (phys : List Bool) (d : Nat)
    (preBlocks : List (List Bool)) (workspace : List Bool)
    (h0 : workspace.getD 0 false = true)
    (h1 : workspace.getD 1 false = false) :
    let pre := selectedPrefix d preBlocks
    let T := phys ++ pre ++ workspace
    run runtimeWorkspaceLocatorMachine (pre.length + 2)
        ⟨RuntimeWorkspaceLocatorState.countLo, phys.length, T⟩ =
      ⟨RuntimeWorkspaceLocatorState.done, phys.length + pre.length, T⟩ := by
  dsimp only
  let n := preBlocks.length + d
  let cnt := List.replicate n (true, true)
  let archive := preBlocks.flatMap passedSourceBlock
  let pre := selectedPrefix d preBlocks
  let T := phys ++ pre ++ workspace
  have hpre : pre = flattenPairs cnt ++ [false, true] ++
      flattenPairs archive := by
    dsimp [pre, cnt, archive]
    rw [selectedPrefix, selectedPrefixPairs, ← List.replicate_add,
      flattenPairs_append, flattenPairs_append]
    rfl
  have hcnt : run runtimeWorkspaceLocatorMachine (2 * n)
      ⟨RuntimeWorkspaceLocatorState.countLo, phys.length, T⟩ =
      ⟨RuntimeWorkspaceLocatorState.countLo, phys.length + 2 * n, T⟩ := by
    apply workspace_run_countPairs
    intro i hi
    have hT : T = (phys ++ flattenPairs cnt) ++
        ([false, true] ++ flattenPairs archive ++ workspace) := by
      simp [T, hpre, List.append_assoc]
    constructor
    · rw [hT, List.getD_append (h := by simp [cnt]; omega)]
      rw [show phys.length + 2 * i = phys.length + 2 * i by rfl]
      rw [List.getD_append_right (h := by omega)]
      rw [show phys.length + 2 * i - phys.length = 2 * i by omega,
        flattenPairs_getD_lo cnt i (by simpa [cnt] using hi)]
      simp [cnt, hi]
    · rw [hT, List.getD_append (h := by simp [cnt]; omega)]
      rw [List.getD_append_right (h := by omega)]
      rw [show phys.length + 2 * i + 1 - phys.length = 2 * i + 1 by omega,
        flattenPairs_getD_hi cnt i (by simpa [cnt] using hi)]
      simp [cnt, hi]
  have hboundary : run runtimeWorkspaceLocatorMachine 2
      ⟨RuntimeWorkspaceLocatorState.countLo, phys.length + 2 * n, T⟩ =
      ⟨RuntimeWorkspaceLocatorState.blockLo, phys.length + 2 * n + 2, T⟩ := by
    apply workspace_run_countBoundary
    · have hm := getD_append_middle (phys ++ flattenPairs cnt)
        [false, true] (flattenPairs archive ++ workspace) 0 (by simp)
      simp only [List.length_append, flattenPairs_length] at hm
      rw [show T = (phys ++ flattenPairs cnt) ++ [false, true] ++
          (flattenPairs archive ++ workspace) by
        simp [T, hpre, List.append_assoc],
        show phys.length + 2 * n =
          (phys.length + 2 * cnt.length) + 0 by simp [cnt], hm]
      rfl
    · have hm := getD_append_middle (phys ++ flattenPairs cnt)
        [false, true] (flattenPairs archive ++ workspace) 1 (by simp)
      simp only [List.length_append, flattenPairs_length] at hm
      rw [show T = (phys ++ flattenPairs cnt) ++ [false, true] ++
          (flattenPairs archive ++ workspace) by
        simp [T, hpre, List.append_assoc],
        show phys.length + 2 * n + 1 =
          (phys.length + 2 * cnt.length) + 1 by simp [cnt], hm]
      rfl
  have harchive := workspace_run_passedBlocks
    (phys ++ flattenPairs cnt ++ [false, true]) workspace preBlocks
  have harchive' : run runtimeWorkspaceLocatorMachine
      (passedBlocksClock preBlocks)
      ⟨RuntimeWorkspaceLocatorState.blockLo, phys.length + 2 * n + 2, T⟩ =
      ⟨RuntimeWorkspaceLocatorState.blockLo, phys.length + pre.length, T⟩ := by
    have hcntlen : (phys ++ flattenPairs cnt ++ [false, true]).length =
        phys.length + 2 * n + 2 := by
      simp [cnt, flattenPairs_length]
      omega
    have hplen : phys.length + pre.length =
        phys.length + 2 * n + 2 + (flattenPairs archive).length := by
      rw [hpre]
      simp only [List.length_append, List.length_cons, List.length_nil,
        flattenPairs_length]
      simp only [cnt, List.length_replicate]
      omega
    have hT : T = (phys ++ flattenPairs cnt ++ [false, true]) ++
        flattenPairs archive ++ workspace := by
      simp [T, hpre, List.append_assoc]
    have harchive2 := harchive
    dsimp only at harchive2
    rw [hcntlen] at harchive2
    have hplen' : phys.length + pre.length = phys.length + 2 * n + 2 +
        (flattenPairs (preBlocks.flatMap passedSourceBlock)).length := by
      simpa [archive] using hplen
    rw [← hplen'] at harchive2
    rw [hT]
    simpa [List.append_assoc] using harchive2
  have hstart : run runtimeWorkspaceLocatorMachine 2
      ⟨RuntimeWorkspaceLocatorState.blockLo, phys.length + pre.length, T⟩ =
      ⟨RuntimeWorkspaceLocatorState.done, phys.length + pre.length, T⟩ := by
    apply workspace_run_startToken
    · rw [show T = (phys ++ pre) ++ workspace by
        simp [T, List.append_assoc]]
      rw [List.getD_append_right (h := by simp)]
      simpa using h0
    · rw [show T = (phys ++ pre) ++ workspace by
        simp [T, List.append_assoc]]
      rw [List.getD_append_right (h := by simp)]
      simpa using h1
  have hclock : pre.length + 2 =
      2 * n + (2 + (passedBlocksClock preBlocks + 2)) := by
    rw [hpre, passedBlocksClock_eq]
    simp [cnt, archive, flattenPairs_length]
    omega
  rw [hclock, run_add, hcnt, run_add, hboundary, run_add, harchive', hstart]

/-- Both structural boundary parsers form one fixed head-preserving machine. -/
def outputWorkspaceLocatorMachine : Machine :=
  headSeqMachine outputSourceLocatorMachine runtimeWorkspaceLocatorMachine

theorem outputWorkspaceLocator_run (T phys workspace : List Bool) (d : Nat)
    (preBlocks : List (List Bool)) (clock1 : Nat)
    (hT : T = phys ++ selectedPrefix d preBlocks ++ workspace)
    (hsource : run outputSourceLocatorMachine clock1
        (init outputSourceLocatorMachine T) =
      ⟨OutputSourceLocatorState.done, phys.length, T⟩)
    (h0 : workspace.getD 0 false = true)
    (h1 : workspace.getD 1 false = false) :
    run outputWorkspaceLocatorMachine
        (clock1 + 1 + ((selectedPrefix d preBlocks).length + 2))
        (init outputWorkspaceLocatorMachine T) =
      ⟨Sum.inr RuntimeWorkspaceLocatorState.done,
        phys.length + (selectedPrefix d preBlocks).length, T⟩ := by
  have hwork : run runtimeWorkspaceLocatorMachine
      ((selectedPrefix d preBlocks).length + 2)
      ⟨RuntimeWorkspaceLocatorState.countLo, phys.length, T⟩ =
      ⟨RuntimeWorkspaceLocatorState.done,
        phys.length + (selectedPrefix d preBlocks).length, T⟩ := by
    rw [hT]
    simpa using runtimeWorkspaceLocator_run_prefixed phys d preBlocks workspace
      h0 h1
  exact headSeq_run outputSourceLocatorMachine runtimeWorkspaceLocatorMachine
    T T T clock1 ((selectedPrefix d preBlocks).length + 2)
    phys.length (phys.length + (selectedPrefix d preBlocks).length)
    OutputSourceLocatorState.done RuntimeWorkspaceLocatorState.done
    hsource rfl hwork rfl

/-- Starting on the genuine post-cashout tape, the joined fixed locator
discovers both boundaries and halts at the actual completed lookup workspace. -/
theorem scheduledRuntimeRelativeOutput_physicalWorkspaceLocate
    (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length)
    (htnext : t + 1 < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let preBlocks := schedule.take t
    let l := scheduledLiteral x t
    let out := (scheduledTruths x w).take t
    let out' := (scheduledTruths x w).take (t + 1)
    let T := sourceSelectorInput B t schedule
    let n := sourceRuntimeLookupClock (B - t) preBlocks w l
    let M := runtimeRelativeOutputSourceMachine B
    let routeClock := runtimeRelativeOutputRouteClock B out T n
    let rcf := run (acceptRouteMachine M) routeClock
      (init (acceptRouteMachine M) (outputCap B out ++ T))
    let locateClock := outputSourceLocatorClock B out' + 1 +
      ((selectedPrefix (B - t) preBlocks).length + 2)
    run outputWorkspaceLocatorMachine locateClock
        (init outputWorkspaceLocatorMachine rcf.tp) =
      ⟨Sum.inr RuntimeWorkspaceLocatorState.done,
        2 * B + 2 + (selectedPrefix (B - t) preBlocks).length, rcf.tp⟩ := by
  dsimp only
  let B := (decodedLiterals x).length
  let schedule := literalTapeSchedule x w
  let preBlocks := schedule.take t
  let l := scheduledLiteral x t
  let out := (scheduledTruths x w).take t
  let out' := (scheduledTruths x w).take (t + 1)
  let T := sourceSelectorInput B t schedule
  let n := sourceRuntimeLookupClock (B - t) preBlocks w l
  let cf := run sourceRuntimeLookupCore n (init sourceRuntimeLookupCore T)
  let M := runtimeRelativeOutputSourceMachine B
  let routeClock := runtimeRelativeOutputRouteClock B out T n
  let rcf := run (acceptRouteMachine M) routeClock
    (init (acceptRouteMachine M) (outputCap B out ++ T))
  let bits := literalLookupTape w l
  let rest := schedule.drop (t + 1)
  let pre := selectedPrefix (B - t) preBlocks
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ selectedTail rest
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  have hslen : schedule.length = B := by
    simp [schedule, B, literalTapeSchedule]
  have hts : t < schedule.length := by simpa [hslen] using ht
  have hget : schedule.getD t [] = bits := by
    dsimp [schedule, bits, l]
    exact literalTapeSchedule_getD x w ht
  have hbit : schedule[t] = bits := by
    rw [← hget, List.getD_eq_getElem schedule [] hts]
  have hsplit : schedule = preBlocks ++ bits :: rest := by
    dsimp [preBlocks, rest]
    conv_lhs => rw [← List.take_append_drop t schedule]
    rw [List.drop_eq_getElem_cons hts, hbit]
  have hprelen : preBlocks.length = t := by
    dsimp [preBlocks]
    rw [List.length_take, Nat.min_eq_left hts.le]
  have hinput : T =
      flattenPairs (progressPairs (B - t) [] preBlocks (bits :: rest)) := by
    dsimp [T]
    rw [sourceSelectorInput, progressPairs, sourceArchive, hsplit]
    simp [hprelen, List.append_assoc]
  have hcf : cf.tp = pre ++ mcf.tp := by
    have hr := sourceRuntimeLookup_run_shape (B - t) preBlocks w l rest
    dsimp [cf, n]
    rw [hinput]
    simpa [bits, pre, trailer, mcf] using congrArg Cfg.tp hr
  have hout : out'.length = t + 1 := by
    dsimp [out']
    rw [List.length_take, scheduledTruths_length,
      Nat.min_eq_left (by simpa [B] using htnext.le)]
  have houtle : out'.length ≤ B := by
    rw [hout]
    exact htnext.le
  have hroute := scheduledRuntimeRelativeOutputSourceRoute x w ht
  have htp : rcf.tp = outputCap B out' ++ cf.tp := by
    have hs := scheduledTruths_take_succ x w ht
    simpa [B, schedule, preBlocks, l, out, out', T, n, cf, M, routeClock,
      rcf, hs] using hroute.2
  have hphysical : rcf.tp = outputCap B out' ++ pre ++ mcf.tp := by
    rw [htp, hcf]
    simp [List.append_assoc]
  have hsource := scheduledRuntimeRelativeOutput_sourceOriginLocate
    x w ht htnext
  have hsource' : run outputSourceLocatorMachine
      (outputSourceLocatorClock B out')
      (init outputSourceLocatorMachine rcf.tp) =
      ⟨OutputSourceLocatorState.done, (outputCap B out').length, rcf.tp⟩ := by
    rw [outputCap_length B out' houtle]
    simpa [B, schedule, preBlocks, l, out, out', T, n, M, routeClock, rcf]
      using hsource
  have htoken : mcf.tp.getD 0 false = true ∧
      mcf.tp.getD 1 false = false := by
    simpa [bits, trailer, mcf] using masterM_literal_startToken w l trailer
  have hr := outputWorkspaceLocator_run rcf.tp (outputCap B out') mcf.tp
    (B - t) preBlocks (outputSourceLocatorClock B out') hphysical hsource'
    htoken.1 htoken.2
  rw [outputCap_length B out' houtle] at hr
  simpa [B, schedule, preBlocks, l, out, out', T, n, M, routeClock, rcf,
    pre] using hr

/-- Cashout and both structural boundary discoveries are one physical machine:
the only handoff that resets is the intended cashout-to-origin transition;
the source-to-workspace handoff preserves the discovered head. -/
theorem scheduledRuntimeRelativeOutput_physicalWorkspaceCombined
    (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length)
    (htnext : t + 1 < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let preBlocks := schedule.take t
    let l := scheduledLiteral x t
    let out := (scheduledTruths x w).take t
    let out' := (scheduledTruths x w).take (t + 1)
    let T := sourceSelectorInput B t schedule
    let n := sourceRuntimeLookupClock (B - t) preBlocks w l
    let M1 := acceptRouteMachine (runtimeRelativeOutputSourceMachine B)
    let routeClock := runtimeRelativeOutputRouteClock B out T n
    let rcf := run M1 routeClock (init M1 (outputCap B out ++ T))
    let locateClock := outputSourceLocatorClock B out' + 1 +
      ((selectedPrefix (B - t) preBlocks).length + 2)
    let M := seqMachine M1 outputWorkspaceLocatorMachine
    run M (routeClock + 1 + locateClock)
        (init M (outputCap B out ++ T)) =
      ⟨Sum.inr (Sum.inr RuntimeWorkspaceLocatorState.done),
        2 * B + 2 + (selectedPrefix (B - t) preBlocks).length, rcf.tp⟩ := by
  dsimp only
  let B := (decodedLiterals x).length
  let schedule := literalTapeSchedule x w
  let preBlocks := schedule.take t
  let l := scheduledLiteral x t
  let out := (scheduledTruths x w).take t
  let out' := (scheduledTruths x w).take (t + 1)
  let T := sourceSelectorInput B t schedule
  let n := sourceRuntimeLookupClock (B - t) preBlocks w l
  let M1 := acceptRouteMachine (runtimeRelativeOutputSourceMachine B)
  let routeClock := runtimeRelativeOutputRouteClock B out T n
  let rcf := run M1 routeClock (init M1 (outputCap B out ++ T))
  let locateClock := outputSourceLocatorClock B out' + 1 +
    ((selectedPrefix (B - t) preBlocks).length + 2)
  have h1 : run M1 routeClock (init M1 (outputCap B out ++ T)) = rcf := rfl
  have hh1 : M1.halt rcf.st = true := by
    have hr := scheduledRuntimeRelativeOutputSourceRoute x w ht
    simpa [B, schedule, preBlocks, l, out, T, n, M1, routeClock, rcf]
      using hr.1
  have h2 : run outputWorkspaceLocatorMachine locateClock
      (init outputWorkspaceLocatorMachine rcf.tp) =
      ⟨Sum.inr RuntimeWorkspaceLocatorState.done,
        2 * B + 2 + (selectedPrefix (B - t) preBlocks).length, rcf.tp⟩ := by
    simpa [B, schedule, preBlocks, l, out, out', T, n, M1, routeClock, rcf,
      locateClock] using scheduledRuntimeRelativeOutput_physicalWorkspaceLocate
        x w ht htnext
  exact seq_run M1 outputWorkspaceLocatorMachine
    (outputCap B out ++ T) rcf.tp rcf.tp routeClock locateClock rcf.st rcf.hd
    (Sum.inr RuntimeWorkspaceLocatorState.done)
    (2 * B + 2 + (selectedPrefix (B - t) preBlocks).length)
    h1 hh1 h2 rfl

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalWorkspace

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalWorkspace.runtimeWorkspaceLocator_run_prefixed
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalWorkspace.outputWorkspaceLocator_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalWorkspace.scheduledRuntimeRelativeOutput_physicalWorkspaceLocate
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalWorkspace.scheduledRuntimeRelativeOutput_physicalWorkspaceCombined
