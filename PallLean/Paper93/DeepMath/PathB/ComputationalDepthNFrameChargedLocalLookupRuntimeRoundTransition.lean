import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimePhysicalLeftSafety
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeRoundEntryAdapter
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeRepeatAdapter
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeFrontOutput
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeContinuationDispatch

/-!
# Charged local lookup: certified concrete round transition

This downstream layer synchronizes the independently useful physical-safety
and marker-pair views of the scheduled nonterminal controller.  Equal-length
prefixes of the same routed tape are equal, so the exact run and `LeftSafeRun`
certificate can be consumed with the classifier's concrete safe pair list.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeLeftSafety
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeOutputSourceLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeUnaryRebaseWriter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativeOutput
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalUnaryRebase
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryAdapter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFrontOutput
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeContinuationDispatch

set_option maxHeartbeats 1000000

/-- Full-configuration form of the marked-front cashout theorem.  In
particular, the exact tape handed to the continuation dispatcher is carried
by the same halted witness; it is not recovered from a second existential
run. -/
theorem runtimeMarkedFrontOutput_exact
    (B : Nat) (out residue : List Bool)
    (pairs : List (Bool × Bool)) (w : List Bool) (l : Lit)
    (rest : List (List Bool))
    (hout : out.length < B)
    (hpairs : outputCap B out ++ residue = flattenPairs pairs)
    (hsafe : RuntimeNoDoubleSepFrom false pairs) :
    let bits := literalLookupTape w l
    let d := (bits :: rest).length
    let source := sourceSelectorInput d 0 (bits :: rest)
    let marker := [false, true, false, true]
    let sourcePre := flattenPairs (List.replicate d (true, true)) ++
      [false, true]
    let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ archiveTail
    let mcf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    let bv := evalLit (fun k => w.getD k false) l
    let T := outputCap B out ++ residue ++ marker ++ source
    let T' := outputCap B (out ++ [bv]) ++ residue ++ marker ++
      sourcePre ++ mcf.tp
    let clock := runtimeMarkedFrontOutputClock pairs d w l out
    ∃ sf pf,
      run runtimeMarkedFrontOutputMachine clock
          (init runtimeMarkedFrontOutputMachine T) = ⟨sf, pf, T'⟩ ∧
      runtimeMarkedFrontOutputMachine.halt sf = true := by
  dsimp only
  let bits := literalLookupTape w l
  let d := (bits :: rest).length
  let source := sourceSelectorInput d 0 (bits :: rest)
  let marker := [false, true, false, true]
  let sourcePre := flattenPairs (List.replicate d (true, true)) ++
    [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let bv := evalLit (fun k => w.getD k false) l
  let T := outputCap B out ++ residue ++ marker ++ source
  let T' := outputCap B (out ++ [bv]) ++ residue ++ marker ++
    sourcePre ++ mcf.tp
  let clock := runtimeMarkedFrontOutputClock pairs d w l out
  have h := runtimeMarkedFrontOutput_run B out residue pairs w l rest
    hout hpairs hsafe
  have hhalt : runtimeMarkedFrontOutputMachine.halt
      (run runtimeMarkedFrontOutputMachine clock
        (init runtimeMarkedFrontOutputMachine T)).st = true := by
    simpa [bits, d, source, marker, sourcePre, archiveTail, trailer, mcf,
      bv, T, T', clock] using h.1
  have htape : (run runtimeMarkedFrontOutputMachine clock
      (init runtimeMarkedFrontOutputMachine T)).tp = T' := by
    simpa [bits, d, source, marker, sourcePre, archiveTail, trailer, mcf,
      bv, T, T', clock, List.append_assoc] using h.2
  cases hrun : run runtimeMarkedFrontOutputMachine clock
      (init runtimeMarkedFrontOutputMachine T) with
  | mk sf pf tp =>
      have htape' : tp = T' := by simpa [hrun] using htape
      subst tp
      refine ⟨sf, pf, ?_, ?_⟩
      · rfl
      · simpa [hrun] using hhalt

theorem scheduled_physicalUnaryRebase_pairSafeRun
    (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length)
    (htnext : t + 1 < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let preBlocks := schedule.take t
    let l := scheduledLiteral x t
    let bits := literalLookupTape w l
    let rest := schedule.drop (t + 1)
    let pre := selectedPrefix (B - t) preBlocks
    let out := (scheduledTruths x w).take t
    let out' := (scheduledTruths x w).take (t + 1)
    let T := sourceSelectorInput B t schedule
    let lookupClock := sourceRuntimeLookupClock (B - t) preBlocks w l
    let M := runtimeRelativeOutputSourceMachine B
    let routeClock := runtimeRelativeOutputRouteClock B out T lookupClock
    let rcf := run (acceptRouteMachine M) routeClock
      (init (acceptRouteMachine M) (outputCap B out ++ T))
    let locateClock := outputSourceLocatorClock B out' + 1 + (pre.length + 2)
    let tailClock := 8 * l.1 + 22
    let prefixClock := locateClock + 1 + tailClock
    let seedClock := runtimeArchiveReturnSeedClock rest
    let R := 2 * B + 2 + pre.length + 2 * bits.length + 4
    ∃ residue unaryClock pairs,
      outputCap B out' ++ residue = flattenPairs pairs ∧
      RuntimeNoDoubleSepFrom false pairs ∧
      run outputWorkspaceArchiveReturnUnaryRebaseMachine
          ((prefixClock + 1 + seedClock) + 1 + unaryClock)
          (init outputWorkspaceArchiveReturnUnaryRebaseMachine rcf.tp) =
        ⟨outputWorkspaceArchiveReturnUnaryRebaseDone,
          R + (selectedTail rest).length,
          flattenPairs pairs ++ [false, true, false, true] ++
            sourceSelectorInput rest.length 0 rest⟩ ∧
      LeftSafeRun outputWorkspaceArchiveReturnUnaryRebaseMachine
        (init outputWorkspaceArchiveReturnUnaryRebaseMachine rcf.tp)
        ((prefixClock + 1 + seedClock) + 1 + unaryClock) := by
  dsimp only
  let B := (decodedLiterals x).length
  let schedule := literalTapeSchedule x w
  let preBlocks := schedule.take t
  let l := scheduledLiteral x t
  let bits := literalLookupTape w l
  let rest := schedule.drop (t + 1)
  let pre := selectedPrefix (B - t) preBlocks
  let out := (scheduledTruths x w).take t
  let out' := (scheduledTruths x w).take (t + 1)
  let T := sourceSelectorInput B t schedule
  let lookupClock := sourceRuntimeLookupClock (B - t) preBlocks w l
  let M := runtimeRelativeOutputSourceMachine B
  let routeClock := runtimeRelativeOutputRouteClock B out T lookupClock
  let rcf := run (acceptRouteMachine M) routeClock
    (init (acceptRouteMachine M) (outputCap B out ++ T))
  let locateClock := outputSourceLocatorClock B out' + 1 + (pre.length + 2)
  let tailClock := 8 * l.1 + 22
  let prefixClock := locateClock + 1 + tailClock
  let seedClock := runtimeArchiveReturnSeedClock rest
  let R := 2 * B + 2 + pre.length + 2 * bits.length + 4
  obtain ⟨residue, unaryClock, hpref, hlen, hrun, hleft⟩ :=
    scheduled_outputWorkspaceArchiveReturnUnaryRebase_safeRun x w ht htnext
  obtain ⟨residue', unaryClock', pairs, hpref', hlen', hpairs,
      hsafe, hentry⟩ :=
    scheduledRuntimeRelativeOutput_physicalUnaryRebaseEntry x w ht htnext
  have hprefix : outputCap B out' ++ residue =
      outputCap B out' ++ residue' := by
    rw [List.prefix_iff_eq_take] at hpref hpref'
    calc
      outputCap B out' ++ residue =
          rcf.tp.take (outputCap B out' ++ residue).length := hpref
      _ = rcf.tp.take (outputCap B out' ++ residue').length := by
        rw [hlen, hlen']
      _ = outputCap B out' ++ residue' := hpref'.symm
  have hpairs' : outputCap B out' ++ residue = flattenPairs pairs :=
    hprefix.trans hpairs
  refine ⟨residue, unaryClock, pairs, hpairs', hsafe, ?_, ?_⟩
  · simpa [B, schedule, preBlocks, l, bits, rest, pre, out, out', T,
      lookupClock, M, routeClock, rcf, locateClock, tailClock,
      prefixClock, seedClock, R, hpairs'] using hrun
  · simpa [B, schedule, preBlocks, l, bits, rest, pre, out, out', T,
      lookupClock, M, routeClock, rcf, locateClock, tailClock,
      prefixClock, seedClock, R] using hleft

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.scheduled_physicalUnaryRebase_pairSafeRun
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeMarkedFrontOutput_exact
