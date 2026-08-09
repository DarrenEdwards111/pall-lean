import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimePhysicalLeftSafety
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeRoundEntryAdapter
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeRepeatAdapter
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeFrontOutput
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeContinuationDispatch
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeTailPreservation

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
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAppendBlock
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr (unaryD)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice (cntT)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRep (repMachine repRounds)
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputRouter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeLeftSafety
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTailPreservation
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceTailLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalWorkspace
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalArchive
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
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeMarkedEntry
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFrontLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFrontOutput
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeContinuationLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeContinuationDispatch
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRepeatAdapter

set_option maxHeartbeats 1000000

/-- Advancing the scheduled source archive by one block extends the selected
prefix by exactly that block's completed representation.  The leading unary
regions merely exchange one cell, so their concatenation is unchanged. -/
theorem selectedPrefix_succ (d : Nat) (preBlocks : List (List Bool))
    (bits : List Bool) (hd : 0 < d) :
    selectedPrefix (d - 1) (preBlocks ++ [bits]) =
      selectedPrefix d preBlocks ++ flattenPairs (passedSourceBlock bits) := by
  have hrepl :
      List.replicate (preBlocks.length + 1) (true, true) ++
          List.replicate (d - 1) (true, true) =
        List.replicate preBlocks.length (true, true) ++
          List.replicate d (true, true) := by
    rw [← List.replicate_add, ← List.replicate_add]
    congr 1
    omega
  simp only [selectedPrefix, selectedPrefixPairs, List.length_append,
    List.length_singleton, List.flatMap_append, List.flatMap_singleton]
  rw [hrepl]
  rw [← List.append_assoc]
  exact flattenPairs_append _ _

/-- Scheduled specialization of `selectedPrefix_succ`: the prefix expected
by round `t + 1` is the round-`t` prefix extended by the block just
completed. -/
theorem scheduled_selectedPrefix_succ (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let bits := literalLookupTape w (scheduledLiteral x t)
    selectedPrefix (B - (t + 1)) (schedule.take (t + 1)) =
      selectedPrefix (B - t) (schedule.take t) ++
        flattenPairs (passedSourceBlock bits) := by
  dsimp only
  let B := (decodedLiterals x).length
  let schedule := literalTapeSchedule x w
  let bits := literalLookupTape w (scheduledLiteral x t)
  have hslen : schedule.length = B := by
    simp [schedule, B, literalTapeSchedule]
  have hts : t < schedule.length := by simpa [hslen] using ht
  have hbit : schedule[t] = bits := by
    rw [← List.getD_eq_getElem schedule [] hts]
    exact literalTapeSchedule_getD x w ht
  have hd : 0 < B - t := by omega
  rw [List.take_add_one, List.getElem?_eq_getElem hts, hbit]
  simpa [B] using selectedPrefix_succ (B - t) (schedule.take t) bits hd

/-! ## Concrete scheduled-chain base -/

/-- Physical tape presented to the fixed marked-front body at round zero. -/
def runtimeRoundZeroTape (B : Nat) (schedule : List (List Bool)) : List Bool :=
  outputCap B [] ++ [false, true, false, true] ++
    sourceSelectorInput B 0 schedule

/-- The round-zero output region has the exact aligned pair decomposition
and separator safety required by the marked cashout theorem. -/
theorem runtimeRoundZeroTape_pairSafe (B : Nat)
    (schedule : List (List Bool)) (hB : 0 < B) :
    let pairs := runtimeOutputCapPairs B []
    runtimeRoundZeroTape B schedule =
        flattenPairs pairs ++ [false, true, false, true] ++
          sourceSelectorInput B 0 schedule ∧
      RuntimeNoDoubleSepFrom false pairs := by
  dsimp only
  let pairs := runtimeOutputCapPairs B []
  have hflat : flattenPairs pairs = outputCap B [] := by
    simpa [pairs] using runtimeOutputCapPairs_flatten B []
  have hsafe := (runtimeOutputCapPairs_safe B [] (by simpa using hB)).1
  constructor
  · simpa [runtimeRoundZeroTape, pairs, List.append_assoc] using
      congrArg (fun z => z ++ [false, true, false, true] ++
        sourceSelectorInput B 0 schedule) hflat.symm
  · simpa [pairs] using hsafe

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

/-- The complete marker-relative lookup phase of cashout is left-safe on the
same concrete pair decomposition used by the exact run theorem. -/
theorem runtimeMarkedFrontLookup_leftSafe
    (pairs : List (Bool × Bool)) (w : List Bool) (l : Lit)
    (rest : List (List Bool))
    (hsafe : RuntimeNoDoubleSepFrom false pairs) :
    let bits := literalLookupTape w l
    let d := (bits :: rest).length
    let source := sourceSelectorInput d 0 (bits :: rest)
    let markerPre := flattenPairs pairs ++ [false, true, false, true]
    let T := markerPre ++ source
    LeftSafeRun runtimeMarkedFrontLookupMachine
      (init runtimeMarkedFrontLookupMachine T)
      (runtimeMarkedFrontLookupClock pairs d w l) := by
  dsimp only
  let bits := literalLookupTape w l
  let d := (bits :: rest).length
  let source := sourceSelectorInput d 0 (bits :: rest)
  let markerPre := flattenPairs pairs ++ [false, true, false, true]
  let T := markerPre ++ source
  let locatorClock := 2 * pairs.length + 7
  let bodyClock := runtimeFrontLookupClock d w l
  have htail : source = true :: true :: source.drop 2 := by
    change sourceSelectorInput (bits :: rest).length 0 (bits :: rest) =
      true :: true ::
        (sourceSelectorInput (bits :: rest).length 0 (bits :: rest)).drop 2
    rw [sourceSelectorInput_front]
    simp [runtimeFrontSelectorInput, List.replicate_succ, flattenPairs,
      List.append_assoc]
  have hloc0 := runtimeRoundEntryLocator_run pairs source true true
    hsafe htail (by simp [runtimePairIsSep])
  have hloc : run runtimeRoundEntryLocatorMachine locatorClock
      (init runtimeRoundEntryLocatorMachine T) =
      ⟨RuntimeRoundEntryState.done, markerPre.length, T⟩ := by
    simpa [locatorClock, T, markerPre, flattenPairs_length,
      List.append_assoc] using hloc0
  have hbody0 := runtimeFrontLookup_run w l rest
  have hbodyPrefix := runtimeFrontLookup_prefixSafe w l rest
  have hbodyLeft : LeftSafeRun runtimeFrontLookupCore
      (init runtimeFrontLookupCore source) bodyClock := by
    simpa [bodyClock, bits, d, source] using
      runtimeFrontLookup_leftSafe w l rest
  have hbodyShift : LeftSafeRun runtimeFrontLookupCore
      ⟨runtimeFrontLookupCore.start, markerPre.length, T⟩ bodyClock := by
    have hs := leftSafeRun_shiftCfg runtimeFrontLookupCore markerPre
      (init runtimeFrontLookupCore source) bodyClock hbodyPrefix hbodyLeft
    simpa [shiftCfg, T, init] using hs
  have hlocLeft := runtimeRoundEntryLocator_leftSafe T locatorClock
  have hbodyHalt : runtimeFrontLookupCore.halt
      (run runtimeFrontLookupCore bodyClock
        ⟨runtimeFrontLookupCore.start, markerPre.length, T⟩).st = true := by
    have hshift := run_shiftCfg runtimeFrontLookupCore markerPre
      (init runtimeFrontLookupCore source) bodyClock hbodyPrefix
    have hstart : shiftCfg runtimeFrontLookupCore markerPre
        (init runtimeFrontLookupCore source) =
      (⟨runtimeFrontLookupCore.start, markerPre.length, T⟩ :
        Cfg runtimeFrontLookupCore) := by
      simp [shiftCfg, T, init]
    rw [← hstart, hshift]
    exact (runtimeFrontLookup_halt_accept w l rest).1
  have hs := headSeqAccept_leftSafe runtimeRoundEntryLocatorMachine
    runtimeFrontLookupCore T T locatorClock bodyClock markerPre.length
    RuntimeRoundEntryState.done hloc rfl hlocLeft hbodyShift hbodyHalt
  simpa [runtimeMarkedFrontLookupMachine, runtimeMarkedFrontLookupClock,
    runtimeMarkedAcceptBody, runtimeMarkedAcceptClock, locatorClock,
    bodyClock, bits, d, source, markerPre, T, Nat.add_assoc] using hs

/-! ## Singleton output-router safety -/

theorem appendPair_leftSafe (bv : Bool)
    (idx : Fin ([bv].length + 1)) (s : Bool) (p : Nat) (T : List Bool) :
    LeftSafeRun (appendMachine [bv]) ⟨(0, idx, s), p, T⟩ 2 := by
  have hs0 : LeftSafeRun (appendMachine [bv]) ⟨(0, idx, s), p, T⟩ 1 := by
    apply leftSafeRun_one_of_not_left
    simp [appendMachine]
  have hs1 : LeftSafeRun (appendMachine [bv])
      (run (appendMachine [bv]) 1 ⟨(0, idx, s), p, T⟩) 1 := by
    rw [run_succ, run_zero, step_a0]
    exact leftSafeRun_one_of_positive (by simpa using Nat.succ_pos p)
  exact leftSafeRun_add hs0 hs1

theorem appendScan_leftSafe (bv : Bool) (T : List Bool)
    (idx : Fin ([bv].length + 1)) (s : Bool) (m : Nat)
    (h : ∀ i, i < m → T.getD (2 * i) false = T.getD (2 * i + 1) false) :
    LeftSafeRun (appendMachine [bv]) ⟨(0, idx, s), 0, T⟩ (2 * m) := by
  induction m with
  | zero => simp [LeftSafeRun]
  | succ m ih =>
      have hpre := ih (fun i hi => h i (by omega))
      have hrun := run_scan [bv] T 0 idx s m
        (by intro i hi; simpa using h i (by omega))
      have hpair : LeftSafeRun (appendMachine [bv])
          (run (appendMachine [bv]) (2 * m) ⟨(0, idx, s), 0, T⟩) 2 := by
        rw [hrun]
        simpa using appendPair_leftSafe bv idx (storedD T 0 s m) (2 * m) T
      have hall := leftSafeRun_add hpre hpair
      convert hall using 1 <;> omega

theorem appendSingletonWrite_leftSafe (bv s : Bool) (p : Nat) (T : List Bool) :
    LeftSafeRun (appendMachine [bv])
      ⟨(2, ⟨0, by simp⟩, s), p, T⟩ 4 := by
  intro i hi _ hmove
  interval_cases i <;>
    simp [run_succ, step, appendMachine, moveHead] at hmove

theorem outputRouter_leftSafe (bv : Bool) (B : Nat)
    (out payload : List Bool) (_hout : out.length < B) :
    LeftSafeRun (appendMachine [bv])
      (init (appendMachine [bv]) (outputCap B out ++ payload))
      (outputRouteClock out) := by
  let T := outputCap B out ++ payload
  let idx : Fin ([bv].length + 1) := ⟨0, by simp⟩
  have hscanEq : ∀ i, i < out.length →
      T.getD (2 * i) false = T.getD (2 * i + 1) false := by
    intro i hi
    simpa [T] using outputCap_payload_data_eq B out payload hi
  have hsScan : LeftSafeRun (appendMachine [bv])
      (init (appendMachine [bv]) T) (2 * out.length) := by
    simpa [init, idx] using appendScan_leftSafe bv T idx false out.length hscanEq
  have hrScan := run_scan [bv] T 0 idx false out.length
    (by simpa using hscanEq)
  have hsDetect : LeftSafeRun (appendMachine [bv])
      (run (appendMachine [bv]) (2 * out.length)
        (init (appendMachine [bv]) T)) 2 := by
    rw [show init (appendMachine [bv]) T = ⟨(0, idx, false), 0, T⟩ by rfl,
      hrScan]
    simpa using appendPair_leftSafe bv idx (storedD T 0 false out.length)
      (2 * out.length) T
  have hrDetect := run_two_detect (bits := [bv]) (idx := idx)
    (s := storedD T 0 false out.length)
    (by simpa [T] using outputCap_payload_mark_lo B out payload)
    (by simpa [T] using outputCap_payload_mark_hi B out payload)
  have hrDetect' : run (appendMachine [bv]) 2
      ⟨(0, idx, storedD T 0 false out.length), 0 + 2 * out.length, T⟩ =
      ⟨(2, idx, false), 2 * out.length, T⟩ := by
    simpa [T] using hrDetect
  have hsWrite : LeftSafeRun (appendMachine [bv])
      (run (appendMachine [bv]) (2 * out.length + 2)
        (init (appendMachine [bv]) T)) 4 := by
    rw [run_add, show init (appendMachine [bv]) T =
      ⟨(0, idx, false), 0, T⟩ by rfl, hrScan, hrDetect']
    exact appendSingletonWrite_leftSafe bv false (2 * out.length) T
  have hs := leftSafeRun_add (leftSafeRun_add hsScan hsDetect) hsWrite
  simpa [outputRouteClock, T, Nat.add_assoc] using hs

theorem acceptRoute_leftSafe_body (M : Machine) (c : Cfg M)
    (t : Nat) (hno : ∀ i < t, M.halt (run M i c).st = false)
    (hsafe : LeftSafeRun M c t) :
    LeftSafeRun (acceptRouteMachine M) (embedAcceptBody M c) t := by
  intro i hi hhalt hmove
  have hr := acceptRoute_run_body M c i
    (fun j hj => hno j (by omega))
  rw [hr] at hhalt hmove ⊢
  have hh := hno i hi
  have hm : (M.δ (run M i c).st
      ((run M i c).tp.getD (run M i c).hd false)).2.2 = 0 := by
    simpa [acceptRouteMachine, embedAcceptBody, hh] using hmove
  exact hsafe i hi hh hm

theorem acceptRoute_leftSafe_handoff (M : Machine) (c : Cfg M)
    (hh : M.halt c.st = true) :
    LeftSafeRun (acceptRouteMachine M) (embedAcceptBody M c) 1 := by
  apply leftSafeRun_one_of_not_left
  by_cases ha : M.accept c.st = true <;>
    simp [acceptRouteMachine, embedAcceptBody, hh, ha]

theorem acceptRoute_leftSafe_falseRouter (M : Machine)
    (c : Cfg (appendMachine [false])) (t : Nat)
    (hsafe : LeftSafeRun (appendMachine [false]) c t) :
    LeftSafeRun (acceptRouteMachine M) (embedFalseRouter M c) t := by
  intro i hi hhalt hmove
  rw [acceptRoute_run_falseRouter M c i] at hhalt hmove ⊢
  have hh : (appendMachine [false]).halt
      (run (appendMachine [false]) i c).st = false := by
    simpa [acceptRouteMachine, embedFalseRouter] using hhalt
  have hm : ((appendMachine [false]).δ
      (run (appendMachine [false]) i c).st
      ((run (appendMachine [false]) i c).tp.getD
        (run (appendMachine [false]) i c).hd false)).2.2 = 0 := by
    simpa [acceptRouteMachine, embedFalseRouter] using hmove
  exact hsafe i hi hh hm

theorem acceptRoute_leftSafe_trueRouter (M : Machine)
    (c : Cfg (appendMachine [true])) (t : Nat)
    (hsafe : LeftSafeRun (appendMachine [true]) c t) :
    LeftSafeRun (acceptRouteMachine M) (embedTrueRouter M c) t := by
  intro i hi hhalt hmove
  rw [acceptRoute_run_trueRouter M c i] at hhalt hmove ⊢
  have hh : (appendMachine [true]).halt
      (run (appendMachine [true]) i c).st = false := by
    simpa [acceptRouteMachine, embedTrueRouter] using hhalt
  have hm : ((appendMachine [true]).δ
      (run (appendMachine [true]) i c).st
      ((run (appendMachine [true]) i c).tp.getD
        (run (appendMachine [true]) i c).hd false)).2.2 = 0 := by
    simpa [acceptRouteMachine, embedTrueRouter] using hmove
  exact hsafe i hi hh hm

theorem acceptRoute_leftSafe_false (M : Machine)
    (T0 T1 : List Bool) (t1 t2 p1 : Nat) (s1 : M.State)
    (h1 : run M t1 (init M T0) = ⟨s1, p1, T1⟩)
    (hh1 : M.halt s1 = true) (ha1 : M.accept s1 = false)
    (hsafe1 : LeftSafeRun M (init M T0) t1)
    (hsafe2 : LeftSafeRun (appendMachine [false])
      (init (appendMachine [false]) T1) t2)
    (hh2 : (appendMachine [false]).halt
      (run (appendMachine [false]) t2
        (init (appendMachine [false]) T1)).st = true) :
    LeftSafeRun (acceptRouteMachine M)
      (init (acceptRouteMachine M) T0) (t1 + 1 + t2) := by
  have hex : ∃ t, M.halt (run M t (init M T0)).st = true :=
    ⟨t1, by rw [h1]; exact hh1⟩
  let tm := Nat.find hex
  have htm := Nat.find_spec hex
  have htmle : tm ≤ t1 := Nat.find_le (by rw [h1]; exact hh1)
  have hfrozen : run M tm (init M T0) = ⟨s1, p1, T1⟩ := by
    rw [← run_stable M T0 htmle htm, h1]
  have hno : ∀ i < tm, M.halt (run M i (init M T0)).st = false := by
    intro i hi
    simpa using Nat.find_min hex hi
  have hs1 : LeftSafeRun (acceptRouteMachine M)
      (init (acceptRouteMachine M) T0) tm := by
    change LeftSafeRun (acceptRouteMachine M)
      (embedAcceptBody M (init M T0)) tm
    exact acceptRoute_leftSafe_body M _ tm hno
      (fun i hi => hsafe1 i (by omega))
  have hr1 : run (acceptRouteMachine M) tm
      (init (acceptRouteMachine M) T0) =
      embedAcceptBody M (⟨s1, p1, T1⟩ : Cfg M) := by
    change run (acceptRouteMachine M) tm
      (embedAcceptBody M (init M T0)) = _
    rw [acceptRoute_run_body M _ tm hno, hfrozen]
  have hsSwitch : LeftSafeRun (acceptRouteMachine M)
      (run (acceptRouteMachine M) tm
        (init (acceptRouteMachine M) T0)) 1 := by
    rw [hr1]
    exact acceptRoute_leftSafe_handoff M _ hh1
  have hafter : run (acceptRouteMachine M) 1
      (run (acceptRouteMachine M) tm
        (init (acceptRouteMachine M) T0)) =
      embedFalseRouter M (init (appendMachine [false]) T1) := by
    rw [hr1, run_succ, run_zero]
    exact acceptRoute_step_false M _ hh1 ha1
  have hs2 : LeftSafeRun (acceptRouteMachine M)
      (run (acceptRouteMachine M) (tm + 1)
        (init (acceptRouteMachine M) T0)) t2 := by
    rw [run_add, hafter]
    exact acceptRoute_leftSafe_falseRouter M _ t2 hsafe2
  have hsMain := leftSafeRun_add (leftSafeRun_add hs1 hsSwitch) hs2
  have hhaltAt : (acceptRouteMachine M).halt
      (run (acceptRouteMachine M) (tm + 1 + t2)
        (init (acceptRouteMachine M) T0)).st = true := by
    rw [show tm + 1 + t2 = (tm + 1) + t2 by omega, run_add,
      run_add, hafter, acceptRoute_run_falseRouter]
    simpa [acceptRouteMachine, embedFalseRouter] using hh2
  have hsSlack : LeftSafeRun (acceptRouteMachine M)
      (run (acceptRouteMachine M) (tm + 1 + t2)
        (init (acceptRouteMachine M) T0)) (t1 - tm) :=
    leftSafeRun_of_halted _ hhaltAt
  have hsAll := leftSafeRun_add hsMain hsSlack
  convert hsAll using 1
  omega

theorem acceptRoute_leftSafe_true (M : Machine)
    (T0 T1 : List Bool) (t1 t2 p1 : Nat) (s1 : M.State)
    (h1 : run M t1 (init M T0) = ⟨s1, p1, T1⟩)
    (hh1 : M.halt s1 = true) (ha1 : M.accept s1 = true)
    (hsafe1 : LeftSafeRun M (init M T0) t1)
    (hsafe2 : LeftSafeRun (appendMachine [true])
      (init (appendMachine [true]) T1) t2)
    (hh2 : (appendMachine [true]).halt
      (run (appendMachine [true]) t2
        (init (appendMachine [true]) T1)).st = true) :
    LeftSafeRun (acceptRouteMachine M)
      (init (acceptRouteMachine M) T0) (t1 + 1 + t2) := by
  have hex : ∃ t, M.halt (run M t (init M T0)).st = true :=
    ⟨t1, by rw [h1]; exact hh1⟩
  let tm := Nat.find hex
  have htm := Nat.find_spec hex
  have htmle : tm ≤ t1 := Nat.find_le (by rw [h1]; exact hh1)
  have hfrozen : run M tm (init M T0) = ⟨s1, p1, T1⟩ := by
    rw [← run_stable M T0 htmle htm, h1]
  have hno : ∀ i < tm, M.halt (run M i (init M T0)).st = false := by
    intro i hi
    simpa using Nat.find_min hex hi
  have hs1 : LeftSafeRun (acceptRouteMachine M)
      (init (acceptRouteMachine M) T0) tm := by
    change LeftSafeRun (acceptRouteMachine M)
      (embedAcceptBody M (init M T0)) tm
    exact acceptRoute_leftSafe_body M _ tm hno
      (fun i hi => hsafe1 i (by omega))
  have hr1 : run (acceptRouteMachine M) tm
      (init (acceptRouteMachine M) T0) =
      embedAcceptBody M (⟨s1, p1, T1⟩ : Cfg M) := by
    change run (acceptRouteMachine M) tm
      (embedAcceptBody M (init M T0)) = _
    rw [acceptRoute_run_body M _ tm hno, hfrozen]
  have hsSwitch : LeftSafeRun (acceptRouteMachine M)
      (run (acceptRouteMachine M) tm
        (init (acceptRouteMachine M) T0)) 1 := by
    rw [hr1]
    exact acceptRoute_leftSafe_handoff M _ hh1
  have hafter : run (acceptRouteMachine M) 1
      (run (acceptRouteMachine M) tm
        (init (acceptRouteMachine M) T0)) =
      embedTrueRouter M (init (appendMachine [true]) T1) := by
    rw [hr1, run_succ, run_zero]
    exact acceptRoute_step_true M _ hh1 ha1
  have hs2 : LeftSafeRun (acceptRouteMachine M)
      (run (acceptRouteMachine M) (tm + 1)
        (init (acceptRouteMachine M) T0)) t2 := by
    rw [run_add, hafter]
    exact acceptRoute_leftSafe_trueRouter M _ t2 hsafe2
  have hsMain := leftSafeRun_add (leftSafeRun_add hs1 hsSwitch) hs2
  have hhaltAt : (acceptRouteMachine M).halt
      (run (acceptRouteMachine M) (tm + 1 + t2)
        (init (acceptRouteMachine M) T0)).st = true := by
    rw [show tm + 1 + t2 = (tm + 1) + t2 by omega, run_add,
      run_add, hafter, acceptRoute_run_trueRouter]
    simpa [acceptRouteMachine, embedTrueRouter] using hh2
  have hsSlack : LeftSafeRun (acceptRouteMachine M)
      (run (acceptRouteMachine M) (tm + 1 + t2)
        (init (acceptRouteMachine M) T0)) (t1 - tm) :=
    leftSafeRun_of_halted _ hhaltAt
  have hsAll := leftSafeRun_add hsMain hsSlack
  convert hsAll using 1
  omega

/-- Full dynamic cashout safety: marker-relative lookup, accept-bit handoff,
reset to physical origin, and the selected singleton output append. -/
theorem runtimeMarkedFrontOutput_leftSafe
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
    let T := outputCap B out ++ residue ++ marker ++ source
    LeftSafeRun runtimeMarkedFrontOutputMachine
      (init runtimeMarkedFrontOutputMachine T)
      (runtimeMarkedFrontOutputClock pairs d w l out) := by
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
  let T1 := outputCap B out ++ residue ++ marker ++ sourcePre ++ mcf.tp
  let bodyClock := runtimeMarkedFrontLookupClock pairs d w l
  have hbody0 := runtimeMarkedFrontLookup_run pairs w l rest hsafe
  have hbody : run runtimeMarkedFrontLookupMachine bodyClock
      (init runtimeMarkedFrontLookupMachine T) =
      ⟨Sum.inr (Sum.inr mcf.st),
        (outputCap B out ++ residue ++ marker).length +
          (sourcePre.length + mcf.hd), T1⟩ := by
    simpa [bodyClock, bits, d, source, marker, sourcePre, archiveTail,
      trailer, mcf, T, T1, hpairs, List.append_assoc] using hbody0
  have hha0 := runtimeFrontLookup_halt_accept w l rest
  dsimp only at hha0
  have hfront := runtimeFrontLookup_run w l rest
  have hfront' : run runtimeFrontLookupCore (runtimeFrontLookupClock d w l)
      (init runtimeFrontLookupCore source) =
      ⟨Sum.inr mcf.st, sourcePre.length + mcf.hd,
        sourcePre ++ mcf.tp⟩ := by
    simpa [bits, d, source, sourcePre, archiveTail, trailer, mcf]
      using hfront
  rw [hfront'] at hha0
  have hh : runtimeMarkedFrontLookupMachine.halt
      (Sum.inr (Sum.inr mcf.st)) = true := by
    simpa [runtimeMarkedFrontLookupMachine, runtimeMarkedAcceptBody,
      headSeqAcceptMachine] using hha0.1
  have ha : runtimeMarkedFrontLookupMachine.accept
      (Sum.inr (Sum.inr mcf.st)) = bv := by
    simpa [runtimeMarkedFrontLookupMachine, runtimeMarkedAcceptBody,
      headSeqAcceptMachine, bv] using hha0.2
  have hsbody := runtimeMarkedFrontLookup_leftSafe pairs w l rest hsafe
  have hsbody' : LeftSafeRun runtimeMarkedFrontLookupMachine
      (init runtimeMarkedFrontLookupMachine T) bodyClock := by
    simpa [bodyClock, bits, d, source, marker, T, hpairs,
      List.append_assoc]
      using hsbody
  by_cases hb : bv = true
  · have hsroute := outputRouter_leftSafe true B out
      (residue ++ marker ++ sourcePre ++ mcf.tp) hout
    have hhroute := outputRouter_halts true B out
      (residue ++ marker ++ sourcePre ++ mcf.tp) hout
    have hs := acceptRoute_leftSafe_true runtimeMarkedFrontLookupMachine
      T T1 bodyClock (outputRouteClock out)
      ((outputCap B out ++ residue ++ marker).length +
        (sourcePre.length + mcf.hd))
      (Sum.inr (Sum.inr mcf.st)) hbody hh (by simpa [hb] using ha)
      hsbody'
      (by simpa [T1, List.append_assoc] using hsroute)
      (by simpa [T1, List.append_assoc] using hhroute)
    simpa [runtimeMarkedFrontOutputMachine, runtimeMarkedFrontOutputClock,
      bodyClock, bits, d, source, marker, T, Nat.add_assoc] using hs
  · have hb0 : bv = false := by simpa using hb
    have hsroute := outputRouter_leftSafe false B out
      (residue ++ marker ++ sourcePre ++ mcf.tp) hout
    have hhroute := outputRouter_halts false B out
      (residue ++ marker ++ sourcePre ++ mcf.tp) hout
    have hs := acceptRoute_leftSafe_false runtimeMarkedFrontLookupMachine
      T T1 bodyClock (outputRouteClock out)
      ((outputCap B out ++ residue ++ marker).length +
        (sourcePre.length + mcf.hd))
      (Sum.inr (Sum.inr mcf.st)) hbody hh (by simpa [hb0] using ha)
      hsbody'
      (by simpa [T1, List.append_assoc] using hsroute)
      (by simpa [T1, List.append_assoc] using hhroute)
    simpa [runtimeMarkedFrontOutputMachine, runtimeMarkedFrontOutputClock,
      bodyClock, bits, d, source, marker, T, Nat.add_assoc] using hs

/-- Exact run and safety of the first cashout on the concrete round-zero
tape.  The result is the marked completed-lookup tape consumed by the
continuation dispatcher. -/
theorem runtimeRoundZero_cashout_safeRun (w : List Bool) (l : Lit)
    (rest : List (List Bool)) :
    let bits := literalLookupTape w l
    let schedule := bits :: rest
    let B := schedule.length
    let pairs := runtimeOutputCapPairs B []
    let sourcePre := flattenPairs (List.replicate B (true, true)) ++
      [false, true]
    let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ archiveTail
    let mcf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    let bv := evalLit (fun k => w.getD k false) l
    let T' := outputCap B [bv] ++ [false, true, false, true] ++
      sourcePre ++ mcf.tp
    let clock := runtimeMarkedFrontOutputClock pairs B w l []
    ∃ sf pf,
      run runtimeMarkedFrontOutputMachine clock
          (init runtimeMarkedFrontOutputMachine
            (runtimeRoundZeroTape B schedule)) = ⟨sf, pf, T'⟩ ∧
      runtimeMarkedFrontOutputMachine.halt sf = true ∧
      LeftSafeRun runtimeMarkedFrontOutputMachine
        (init runtimeMarkedFrontOutputMachine
          (runtimeRoundZeroTape B schedule)) clock := by
  dsimp only
  let bits := literalLookupTape w l
  let schedule := bits :: rest
  let B := schedule.length
  let pairs := runtimeOutputCapPairs B []
  have hpairs : outputCap B [] ++ [] = flattenPairs pairs := by
    simpa [pairs] using (runtimeOutputCapPairs_flatten B []).symm
  have hout : (0 : Nat) < B := by simp [B, schedule]
  have hsafe : RuntimeNoDoubleSepFrom false pairs :=
    (runtimeOutputCapPairs_safe B [] hout).1
  obtain ⟨sf, pf, hrun, hhalt⟩ :=
    runtimeMarkedFrontOutput_exact B [] [] pairs w l rest hout hpairs hsafe
  have hleft :=
    runtimeMarkedFrontOutput_leftSafe B [] [] pairs w l rest
      hout hpairs hsafe
  refine ⟨sf, pf, ?_, hhalt, ?_⟩
  · simpa [bits, schedule, B, pairs, runtimeRoundZeroTape,
      List.append_assoc] using hrun
  · simpa [bits, schedule, B, pairs, runtimeRoundZeroTape,
      List.append_assoc] using hleft

/-- Exact future-archive suffix of the marked round-zero cashout tape.  This
is the physical offset equation needed by the archive-return/unary-rebase
controller; it accounts for the output capacity, doubled marker, rebased
source prefix, completed literal payload, trailer, and equal-length padding. -/
theorem runtimeRoundZero_markedCashout_futureArchive
    (w : List Bool) (l : Lit) (first : List Bool)
    (more : List (List Bool)) :
    let bits := literalLookupTape w l
    let rest := first :: more
    let B := (bits :: rest).length
    let bv := evalLit (fun k => w.getD k false) l
    let sourcePre := flattenPairs (List.replicate B (true, true)) ++
      [false, true]
    let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ archiveTail
    let mcf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    let Tcash := outputCap B [bv] ++ [false, true, false, true] ++
      sourcePre ++ mcf.tp
    let R := 4 * B + 2 * bits.length + 12
    Tcash.drop R = selectedTail rest := by
  dsimp only
  let bits := literalLookupTape w l
  let rest := first :: more
  let B := (bits :: rest).length
  let bv := evalLit (fun k => w.getD k false) l
  let sourcePre := flattenPairs (List.replicate B (true, true)) ++
    [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let Tcash := outputCap B [bv] ++ [false, true, false, true] ++
    sourcePre ++ mcf.tp
  let R := 4 * B + 2 * bits.length + 12
  have hout : [bv].length ≤ B := by simp [B, rest]
  have houtlen := outputCap_length B [bv] hout
  have hsourceLen : sourcePre.length = 2 * B + 2 := by
    simp [sourcePre, flattenPairs_length]
  have htrailer : mcf.tp.drop bits.length = trailer := by
    simpa [mcf, bits, trailer] using masterM_literal_trailer w l trailer
  have hmcf : mcf.tp.drop (2 * bits.length + 4) = archiveTail := by
    rw [show 2 * bits.length + 4 = bits.length + (bits.length + 4) by omega,
      ← List.drop_drop, htrailer]
    simp [trailer, archiveTail]
  have hprefixLen :
      (outputCap B [bv] ++ [false, true, false, true] ++ sourcePre).length =
        4 * B + 8 := by
    simp [houtlen, hsourceLen]
    omega
  change List.drop R
      ((outputCap B [bv] ++ [false, true, false, true] ++ sourcePre) ++
        mcf.tp) = selectedTail rest
  rw [show R =
      (outputCap B [bv] ++ [false, true, false, true] ++ sourcePre).length +
        (2 * bits.length + 4) by rw [hprefixLen]; omega]
  rw [← List.drop_drop, List.drop_left]
  change mcf.tp.drop (2 * bits.length + 4) = archiveTail
  exact hmcf

set_option maxHeartbeats 4000000 in
/-- At the absolute future-archive boundary of the marked round-zero cashout,
the genuine archive-return controller installs the canonical `01` seed.  The
same clock also carries its complete left-safety certificate. -/
theorem runtimeRoundZero_markedCashout_archiveReturnSeed_safeRun
    (w : List Bool) (l : Lit) (first : List Bool)
    (more : List (List Bool)) :
    let bits := literalLookupTape w l
    let rest := first :: more
    let B := (bits :: rest).length
    let bv := evalLit (fun k => w.getD k false) l
    let sourcePre := flattenPairs (List.replicate B (true, true)) ++
      [false, true]
    let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ archiveTail
    let mcf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    let Tcash := outputCap B [bv] ++ [false, true, false, true] ++
      sourcePre ++ mcf.tp
    let R := 4 * B + 2 * bits.length + 12
    ∃ pre a b,
      pre.length = R - 2 ∧
      Tcash = pre ++ [a, b] ++ selectedTail rest ∧
      run runtimeArchiveReturnSeedMachine
          (runtimeArchiveReturnSeedClock rest)
          ⟨runtimeArchiveReturnSeedMachine.start, R, Tcash⟩ =
        ⟨Sum.inr RuntimeRebaseSeedState.done, R,
          pre ++ [false, true] ++ selectedTail rest⟩ ∧
      LeftSafeRun runtimeArchiveReturnSeedMachine
        ⟨runtimeArchiveReturnSeedMachine.start, R, Tcash⟩
        (runtimeArchiveReturnSeedClock rest) := by
  dsimp only
  let bits := literalLookupTape w l
  let rest := first :: more
  let B := (bits :: rest).length
  let bv := evalLit (fun k => w.getD k false) l
  let sourcePre := flattenPairs (List.replicate B (true, true)) ++
    [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let Tcash := outputCap B [bv] ++ [false, true, false, true] ++
    sourcePre ++ mcf.tp
  let R := 4 * B + 2 * bits.length + 12
  have hdrop : Tcash.drop R = selectedTail rest := by
    simpa [bits, rest, B, bv, sourcePre, archiveTail, trailer, mcf,
      Tcash, R] using runtimeRoundZero_markedCashout_futureArchive
        w l first more
  have hR : 2 ≤ R := by simp [R]
  have hsuffix : 0 < (selectedTail rest).length := by
    simp [selectedTail, rest, freshSourceBlock, flattenPairs_length]
  have hRlen : R ≤ Tcash.length := by
    have := congrArg List.length hdrop
    simp only [List.length_drop] at this
    omega
  obtain ⟨pre, a, b, hpre, hshape, hrun⟩ :=
    runtimeArchiveReturnSeed_run_of_drop Tcash R first more
      hR hRlen (by simpa [rest] using hdrop)
  have hpre2 : 2 ≤ pre.length := by rw [hpre]; omega
  have hsafe0 := runtimeArchiveReturnSeed_leftSafe_prefixed
    pre a b first more hpre2
  have hsafe : LeftSafeRun runtimeArchiveReturnSeedMachine
      ⟨runtimeArchiveReturnSeedMachine.start, R, Tcash⟩
      (runtimeArchiveReturnSeedClock rest) := by
    rw [hshape, show R = pre.length + 2 by omega]
    change LeftSafeRun runtimeArchiveReturnSeedMachine
      ⟨runtimeArchiveReturnSeedMachine.start, pre.length + 2,
        pre ++ [a, b] ++ selectedTail (first :: more)⟩
      (runtimeArchiveReturnSeedClock (first :: more))
    exact hsafe0
  exact ⟨pre, a, b, hpre, hshape, hrun, hsafe⟩

set_option maxHeartbeats 4000000 in
/-- Physical locator for a marked continuation tape: first cross the robust
doubled entry marker, then traverse the selector prefix and the completed
literal workspace to the untouched future archive. -/
theorem runtimeRoundZero_markedWorkspaceTailLocate
    (w : List Bool) (l : Lit) (first : List Bool)
    (more : List (List Bool)) :
    let bits := literalLookupTape w l
    let rest := first :: more
    let B := (bits :: rest).length
    let bv := evalLit (fun k => w.getD k false) l
    let pairs := runtimeOutputCapPairs B [bv]
    let markerPre := flattenPairs pairs ++ [false, true, false, true]
    let sourcePre := flattenPairs (List.replicate B (true, true)) ++
      [false, true]
    let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ archiveTail
    let mcf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    let Tcash := markerPre ++ sourcePre ++ mcf.tp
    let markerClock := 2 * pairs.length + 7
    let workspaceClock := sourcePre.length + 2
    let tailClock := 8 * l.1 + 22
    let locateClock := markerClock + 1 +
      (workspaceClock + 1 + tailClock)
    let R := 4 * B + 2 * bits.length + 12
    run runtimeMarkedWorkspaceTailLocatorMachine locateClock
        (init runtimeMarkedWorkspaceTailLocatorMachine Tcash) =
      ⟨Sum.inr (Sum.inr RuntimeWorkspaceTailLocatorState.done),
        R, Tcash⟩ := by
  dsimp only
  let bits := literalLookupTape w l
  let rest := first :: more
  let B := (bits :: rest).length
  let bv := evalLit (fun k => w.getD k false) l
  let pairs := runtimeOutputCapPairs B [bv]
  let markerPre := flattenPairs pairs ++ [false, true, false, true]
  let sourcePre := flattenPairs (List.replicate B (true, true)) ++
    [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let Tcash := markerPre ++ sourcePre ++ mcf.tp
  let markerClock := 2 * pairs.length + 7
  let workspaceClock := sourcePre.length + 2
  let tailClock := 8 * l.1 + 22
  let locateClock := markerClock + 1 +
    (workspaceClock + 1 + tailClock)
  let R := 4 * B + 2 * bits.length + 12
  have hout : [bv].length < B := by simp [B, rest]
  have hpairs : RuntimeNoDoubleSepFrom false pairs :=
    (runtimeOutputCapPairs_safe B [bv] hout).1
  have hB : 0 < B := by simp [B, rest]
  have hsourceCons : ∃ tail, sourcePre = true :: true :: tail := by
    cases hrep : List.replicate B (true, true) with
    | nil =>
        have := congrArg List.length hrep
        simp at this
        omega
    | cons p ps =>
        have hp : p = (true, true) := by
          have := List.eq_replicate_iff.mp hrep.symm
          exact this.2 p (by simp)
        subst p
        exact ⟨flattenPairs ps ++ [false, true], by
          simp [sourcePre, hrep, flattenPairs]⟩
  obtain ⟨sourceTail, hsourceCons⟩ := hsourceCons
  have htailShape : sourcePre ++ mcf.tp =
      true :: true :: (sourcePre ++ mcf.tp).drop 2 := by
    rw [hsourceCons]
    simp
  have hmarker : run runtimeRoundEntryLocatorMachine markerClock
      (init runtimeRoundEntryLocatorMachine Tcash) =
      ⟨RuntimeRoundEntryState.done, markerPre.length, Tcash⟩ := by
    simpa [markerClock, Tcash, markerPre, flattenPairs,
      List.append_assoc] using runtimeRoundEntryLocator_run pairs
        (sourcePre ++ mcf.tp) true true hpairs htailShape (by decide)
  have htoken := masterM_literal_startToken w l trailer
  have hsource : sourcePre = selectedPrefix B [] := by
    simp [sourcePre, selectedPrefix, selectedPrefixPairs,
      flattenPairs_append, flattenPairs]
  have hworkspace : run runtimeWorkspaceLocatorMachine workspaceClock
      ⟨RuntimeWorkspaceLocatorState.countLo, markerPre.length, Tcash⟩ =
      ⟨RuntimeWorkspaceLocatorState.done,
        markerPre.length + sourcePre.length, Tcash⟩ := by
    have h := runtimeWorkspaceLocator_run_prefixed markerPre B [] mcf.tp
      (by simpa [mcf, bits, trailer] using htoken.1)
      (by simpa [mcf, bits, trailer] using htoken.2)
    simpa [workspaceClock, Tcash, hsource, List.append_assoc] using h
  have htail := masterM_literal_workspaceTailLocate_prefixed
    (markerPre ++ sourcePre) w l first more
  have htail' : run runtimeWorkspaceTailLocatorMachine tailClock
      ⟨RuntimeWorkspaceTailLocatorState.boot0,
        markerPre.length + sourcePre.length, Tcash⟩ =
      ⟨RuntimeWorkspaceTailLocatorState.done,
        markerPre.length + sourcePre.length + 2 * bits.length + 4,
        Tcash⟩ := by
    simpa [tailClock, Tcash, mcf, bits, rest, trailer,
      List.append_assoc] using htail
  have hinner := headSeq_run_at runtimeWorkspaceLocatorMachine
    runtimeWorkspaceTailLocatorMachine Tcash Tcash Tcash
    markerPre.length workspaceClock tailClock
    (markerPre.length + sourcePre.length)
    (markerPre.length + sourcePre.length + 2 * bits.length + 4)
    RuntimeWorkspaceLocatorState.done
    RuntimeWorkspaceTailLocatorState.done hworkspace rfl htail' rfl
  have hall := headSeq_run runtimeRoundEntryLocatorMachine
    (headSeqMachine runtimeWorkspaceLocatorMachine
      runtimeWorkspaceTailLocatorMachine)
    Tcash Tcash Tcash markerClock (workspaceClock + 1 + tailClock)
    markerPre.length
    (markerPre.length + sourcePre.length + 2 * bits.length + 4)
    RuntimeRoundEntryState.done
    (Sum.inr RuntimeWorkspaceTailLocatorState.done)
    hmarker rfl (by simpa using hinner) rfl
  have hmarkerLen : markerPre.length = 2 * B + 6 := by
    have hp := runtimeOutputCapPairs_flatten B [bv]
    have hcap := outputCap_length B [bv] (by simp [B, rest])
    simp [markerPre, ← hp] at hcap ⊢
    omega
  have hsourceLen : sourcePre.length = 2 * B + 2 := by
    simp [sourcePre, flattenPairs_length]
  have hhead : markerPre.length + sourcePre.length +
      2 * bits.length + 4 = R := by
    rw [hmarkerLen, hsourceLen]
    simp [R]
    omega
  rw [hhead] at hall
  simpa [runtimeMarkedWorkspaceTailLocatorMachine, locateClock, markerClock,
    workspaceClock, tailClock, sourcePre, flattenPairs_length, pairs, B,
    rest, bv, bits, Tcash, markerPre, archiveTail, trailer, mcf, R,
    List.append_assoc] using hall

/-! ## Consuming marked-entry adapter -/

/-- Exact marker consumption on an arbitrary prefixed tape. -/
theorem runtimeMarkerConsume_run (pre tail : List Bool) :
    run runtimeMarkerConsumeMachine 8
        ⟨runtimeMarkerConsumeMachine.start, pre.length + 4,
          pre ++ [false, true, false, true] ++ tail⟩ =
      ⟨RuntimeMarkerConsumeState.done, pre.length + 4,
        pre ++ [false, false, false, false] ++ tail⟩ := by
  simp [run_succ, step, runtimeMarkerConsumeMachine, moveHead, writeAt,
    List.append_assoc]

/-- Marker consumption never crosses the physical left boundary. -/
theorem runtimeMarkerConsume_leftSafe (pre tail : List Bool) :
    LeftSafeRun runtimeMarkerConsumeMachine
      ⟨runtimeMarkerConsumeMachine.start, pre.length + 4,
        pre ++ [false, true, false, true] ++ tail⟩ 8 := by
  intro i hi hlive hmove
  interval_cases i <;>
    simp [run_succ, step, runtimeMarkerConsumeMachine, moveHead, writeAt]
      at hlive hmove ⊢ <;> omega

/-- Exact and left-safe marked-entry location followed by destructive marker
normalization.  The selector begins at the same physical head, while the old
delimiter has become safe aligned data. -/
theorem runtimeConsumingRoundEntryLocator_safeRun
    (pairs : List (Bool × Bool)) (source : List Bool)
    (hsafe : RuntimeNoDoubleSepFrom false pairs)
    (htail : source = true :: true :: source.drop 2) :
    let T := flattenPairs pairs ++ [false, true, false, true] ++ source
    let Tclean := flattenPairs pairs ++ [false, false, false, false] ++ source
    let markerHead := (flattenPairs pairs ++
      [false, true, false, true]).length
    let markerClock := 2 * pairs.length + 7
    run runtimeConsumingRoundEntryLocatorMachine (markerClock + 1 + 8)
        (init runtimeConsumingRoundEntryLocatorMachine T) =
      ⟨Sum.inr RuntimeMarkerConsumeState.done, markerHead, Tclean⟩ ∧
      LeftSafeRun runtimeConsumingRoundEntryLocatorMachine
        (init runtimeConsumingRoundEntryLocatorMachine T)
        (markerClock + 1 + 8) := by
  dsimp only
  let T := flattenPairs pairs ++ [false, true, false, true] ++ source
  let Tclean := flattenPairs pairs ++ [false, false, false, false] ++ source
  let markerHead := (flattenPairs pairs ++
    [false, true, false, true]).length
  let markerClock := 2 * pairs.length + 7
  have hloc0 := runtimeRoundEntryLocator_run pairs source true true
    hsafe htail (by decide)
  have hloc : run runtimeRoundEntryLocatorMachine markerClock
      (init runtimeRoundEntryLocatorMachine T) =
      ⟨RuntimeRoundEntryState.done, markerHead, T⟩ := by
    simpa [T, markerHead, markerClock, flattenPairs_length,
      List.append_assoc] using hloc0
  have hconsume : run runtimeMarkerConsumeMachine 8
      ⟨runtimeMarkerConsumeMachine.start, markerHead, T⟩ =
      ⟨RuntimeMarkerConsumeState.done, markerHead, Tclean⟩ := by
    simpa [T, Tclean, markerHead, List.append_assoc] using
      runtimeMarkerConsume_run (flattenPairs pairs) source
  have hrun := headSeq_run runtimeRoundEntryLocatorMachine
    runtimeMarkerConsumeMachine T T Tclean markerClock 8
    markerHead markerHead RuntimeRoundEntryState.done
    RuntimeMarkerConsumeState.done hloc rfl hconsume rfl
  have hconsumeSafe : LeftSafeRun runtimeMarkerConsumeMachine
      ⟨runtimeMarkerConsumeMachine.start, markerHead, T⟩ 8 := by
    simpa [T, markerHead, List.append_assoc] using
      runtimeMarkerConsume_leftSafe (flattenPairs pairs) source
  have hconsumeHalt : runtimeMarkerConsumeMachine.halt
      (run runtimeMarkerConsumeMachine 8
        ⟨runtimeMarkerConsumeMachine.start, markerHead, T⟩).st = true := by
    rw [hconsume]
    rfl
  have hleft := headSeq_leftSafe runtimeRoundEntryLocatorMachine
    runtimeMarkerConsumeMachine T T markerClock 8 markerHead
    RuntimeRoundEntryState.done hloc rfl
    (runtimeRoundEntryLocator_leftSafe T markerClock)
    hconsumeSafe hconsumeHalt
  exact ⟨by simpa [runtimeConsumingRoundEntryLocatorMachine, T, Tclean,
      markerHead, markerClock, flattenPairs_length] using hrun,
    by simpa [runtimeConsumingRoundEntryLocatorMachine, T, markerClock]
      using hleft⟩

set_option maxHeartbeats 4000000 in
/-- Corrected origin-to-archive locator: consume the stale doubled marker,
then traverse the selector prefix and completed literal workspace on the
normalized tape. -/
theorem runtimeConsumingMarkedWorkspaceTailLocator_safeRun
    (pairs : List (Bool × Bool)) (w : List Bool) (l : Lit)
    (first : List Bool) (more : List (List Bool))
    (hsafe : RuntimeNoDoubleSepFrom false pairs) :
    let bits := literalLookupTape w l
    let rest := first :: more
    let d := (bits :: rest).length
    let markerPre := flattenPairs pairs ++ [false, true, false, true]
    let cleanPre := flattenPairs pairs ++ [false, false, false, false]
    let sourcePre := flattenPairs (List.replicate d (true, true)) ++
      [false, true]
    let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ archiveTail
    let mcf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    let Tcash := markerPre ++ sourcePre ++ mcf.tp
    let Tclean := cleanPre ++ sourcePre ++ mcf.tp
    let markerClock := 2 * pairs.length + 7
    let entryClock := markerClock + 1 + 8
    let workspaceClock := sourcePre.length + 2
    let tailClock := 8 * l.1 + 22
    let locateClock := entryClock + 1 +
      (workspaceClock + 1 + tailClock)
    let R := cleanPre.length + sourcePre.length + 2 * bits.length + 4
    run runtimeConsumingMarkedWorkspaceTailLocatorMachine locateClock
        (init runtimeConsumingMarkedWorkspaceTailLocatorMachine Tcash) =
      ⟨Sum.inr (Sum.inr RuntimeWorkspaceTailLocatorState.done),
        R, Tclean⟩ ∧
      LeftSafeRun runtimeConsumingMarkedWorkspaceTailLocatorMachine
        (init runtimeConsumingMarkedWorkspaceTailLocatorMachine Tcash)
        locateClock := by
  dsimp only
  let bits := literalLookupTape w l
  let rest := first :: more
  let d := (bits :: rest).length
  let markerPre := flattenPairs pairs ++ [false, true, false, true]
  let cleanPre := flattenPairs pairs ++ [false, false, false, false]
  let sourcePre := flattenPairs (List.replicate d (true, true)) ++
    [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let Tcash := markerPre ++ sourcePre ++ mcf.tp
  let Tclean := cleanPre ++ sourcePre ++ mcf.tp
  let markerClock := 2 * pairs.length + 7
  let entryClock := markerClock + 1 + 8
  let workspaceClock := sourcePre.length + 2
  let tailClock := 8 * l.1 + 22
  let locateClock := entryClock + 1 +
    (workspaceClock + 1 + tailClock)
  let R := cleanPre.length + sourcePre.length + 2 * bits.length + 4
  have hsourceCons : sourcePre ++ mcf.tp =
      true :: true :: (sourcePre ++ mcf.tp).drop 2 := by
    have hd : 0 < d := by simp [d, rest]
    cases hrep : List.replicate d (true, true) with
    | nil =>
        have hlen := congrArg List.length hrep
        simp [d, rest] at hlen
    | cons p ps =>
        have hp : p = (true, true) := by
          have hmem : p ∈ List.replicate d (true, true) := by
            rw [hrep]
            simp
          simpa using (List.mem_replicate.mp hmem).2
        subst p
        simp [sourcePre, hrep, flattenPairs]
  have hentry0 := runtimeConsumingRoundEntryLocator_safeRun
    pairs (sourcePre ++ mcf.tp) hsafe hsourceCons
  have hentry : run runtimeConsumingRoundEntryLocatorMachine entryClock
      (init runtimeConsumingRoundEntryLocatorMachine Tcash) =
      ⟨Sum.inr RuntimeMarkerConsumeState.done,
        cleanPre.length, Tclean⟩ := by
    simpa [bits, rest, d, markerPre, cleanPre, sourcePre, archiveTail,
      trailer, mcf, Tcash, Tclean, markerClock, entryClock,
      flattenPairs_length, List.append_assoc] using hentry0.1
  have hentrySafe : LeftSafeRun runtimeConsumingRoundEntryLocatorMachine
      (init runtimeConsumingRoundEntryLocatorMachine Tcash) entryClock := by
    simpa [bits, rest, d, markerPre, cleanPre, sourcePre, archiveTail,
      trailer, mcf, Tcash, markerClock, entryClock, List.append_assoc]
      using hentry0.2
  have htoken := masterM_literal_startToken w l trailer
  have hsource : sourcePre = selectedPrefix d [] := by
    simp [sourcePre, selectedPrefix, selectedPrefixPairs,
      flattenPairs_append, flattenPairs]
  have hworkspace : run runtimeWorkspaceLocatorMachine workspaceClock
      ⟨RuntimeWorkspaceLocatorState.countLo, cleanPre.length, Tclean⟩ =
      ⟨RuntimeWorkspaceLocatorState.done,
        cleanPre.length + sourcePre.length, Tclean⟩ := by
    have h := runtimeWorkspaceLocator_run_prefixed cleanPre d [] mcf.tp
      (by simpa [mcf, bits, trailer] using htoken.1)
      (by simpa [mcf, bits, trailer] using htoken.2)
    simpa [workspaceClock, Tclean, hsource, List.append_assoc] using h
  have htail0 := masterM_literal_workspaceTailLocate_prefixed
    (cleanPre ++ sourcePre) w l first more
  have htail : run runtimeWorkspaceTailLocatorMachine tailClock
      ⟨RuntimeWorkspaceTailLocatorState.boot0,
        cleanPre.length + sourcePre.length, Tclean⟩ =
      ⟨RuntimeWorkspaceTailLocatorState.done, R, Tclean⟩ := by
    simpa [tailClock, Tclean, mcf, bits, rest, trailer, R,
      List.append_assoc] using htail0
  have hinner := headSeq_run_at runtimeWorkspaceLocatorMachine
    runtimeWorkspaceTailLocatorMachine Tclean Tclean Tclean
    cleanPre.length workspaceClock tailClock
    (cleanPre.length + sourcePre.length) R
    RuntimeWorkspaceLocatorState.done
    RuntimeWorkspaceTailLocatorState.done hworkspace rfl htail rfl
  have hrun := headSeq_run runtimeConsumingRoundEntryLocatorMachine
    (headSeqMachine runtimeWorkspaceLocatorMachine
      runtimeWorkspaceTailLocatorMachine)
    Tcash Tclean Tclean entryClock (workspaceClock + 1 + tailClock)
    cleanPre.length R (Sum.inr RuntimeMarkerConsumeState.done)
    (Sum.inr RuntimeWorkspaceTailLocatorState.done)
    hentry rfl (by simpa using hinner) rfl
  have hsInner := headSeq_leftSafe_at runtimeWorkspaceLocatorMachine
    runtimeWorkspaceTailLocatorMachine Tclean Tclean cleanPre.length
    workspaceClock tailClock (cleanPre.length + sourcePre.length)
    RuntimeWorkspaceLocatorState.done (by simpa using hworkspace) rfl
    (runtimeWorkspaceLocator_leftSafe Tclean cleanPre.length workspaceClock)
    (runtimeWorkspaceTailLocator_leftSafe Tclean
      (cleanPre.length + sourcePre.length) tailClock)
    (by rw [show run (headSeqMachine runtimeWorkspaceLocatorMachine
        runtimeWorkspaceTailLocatorMachine)
        (workspaceClock + 1 + tailClock)
        ⟨(headSeqMachine runtimeWorkspaceLocatorMachine
          runtimeWorkspaceTailLocatorMachine).start, cleanPre.length, Tclean⟩ =
        ⟨Sum.inr RuntimeWorkspaceTailLocatorState.done, R, Tclean⟩ by
          simpa using hinner]; rfl)
  have hinnerHalt : (headSeqMachine runtimeWorkspaceLocatorMachine
      runtimeWorkspaceTailLocatorMachine).halt
      (run (headSeqMachine runtimeWorkspaceLocatorMachine
        runtimeWorkspaceTailLocatorMachine)
        (workspaceClock + 1 + tailClock)
        ⟨(headSeqMachine runtimeWorkspaceLocatorMachine
          runtimeWorkspaceTailLocatorMachine).start,
          cleanPre.length, Tclean⟩).st = true := by
    rw [show run (headSeqMachine runtimeWorkspaceLocatorMachine
        runtimeWorkspaceTailLocatorMachine)
        (workspaceClock + 1 + tailClock)
        ⟨(headSeqMachine runtimeWorkspaceLocatorMachine
          runtimeWorkspaceTailLocatorMachine).start,
          cleanPre.length, Tclean⟩ =
        ⟨Sum.inr RuntimeWorkspaceTailLocatorState.done, R, Tclean⟩ by
          simpa using hinner]
    rfl
  have hleft := headSeq_leftSafe
    runtimeConsumingRoundEntryLocatorMachine
    (headSeqMachine runtimeWorkspaceLocatorMachine
      runtimeWorkspaceTailLocatorMachine)
    Tcash Tclean entryClock (workspaceClock + 1 + tailClock)
    cleanPre.length (Sum.inr RuntimeMarkerConsumeState.done)
    hentry rfl hentrySafe hsInner hinnerHalt
  exact ⟨by simpa [runtimeConsumingMarkedWorkspaceTailLocatorMachine,
      locateClock] using hrun,
    by simpa [runtimeConsumingMarkedWorkspaceTailLocatorMachine,
      locateClock] using hleft⟩

/-- Safety compositor for the three phases of the marked physical locator. -/
theorem runtimeMarkedWorkspaceTailLocator_leftSafe_of_runs
    (T : List Bool) (markerClock workspaceClock tailClock
      markerHead workspaceHead tailHead : Nat)
    (hmarker : run runtimeRoundEntryLocatorMachine markerClock
        (init runtimeRoundEntryLocatorMachine T) =
      ⟨RuntimeRoundEntryState.done, markerHead, T⟩)
    (hworkspace : run runtimeWorkspaceLocatorMachine workspaceClock
        ⟨RuntimeWorkspaceLocatorState.countLo, markerHead, T⟩ =
      ⟨RuntimeWorkspaceLocatorState.done, workspaceHead, T⟩)
    (htail : run runtimeWorkspaceTailLocatorMachine tailClock
        ⟨RuntimeWorkspaceTailLocatorState.boot0, workspaceHead, T⟩ =
      ⟨RuntimeWorkspaceTailLocatorState.done, tailHead, T⟩) :
    LeftSafeRun runtimeMarkedWorkspaceTailLocatorMachine
      (init runtimeMarkedWorkspaceTailLocatorMachine T)
      (markerClock + 1 + (workspaceClock + 1 + tailClock)) := by
  have hinner := headSeq_run_at runtimeWorkspaceLocatorMachine
    runtimeWorkspaceTailLocatorMachine T T T markerHead
    workspaceClock tailClock workspaceHead tailHead
    RuntimeWorkspaceLocatorState.done
    RuntimeWorkspaceTailLocatorState.done hworkspace rfl htail rfl
  have hsInner := headSeq_leftSafe_at runtimeWorkspaceLocatorMachine
    runtimeWorkspaceTailLocatorMachine T T markerHead workspaceClock tailClock
    workspaceHead RuntimeWorkspaceLocatorState.done (by simpa using hworkspace) rfl
    (runtimeWorkspaceLocator_leftSafe T markerHead workspaceClock)
    (runtimeWorkspaceTailLocator_leftSafe T workspaceHead tailClock)
    (by
      have := congrArg (fun c => runtimeWorkspaceTailLocatorMachine.halt c.st)
        htail
      simpa [runtimeWorkspaceTailLocatorMachine] using this)
  simpa [runtimeMarkedWorkspaceTailLocatorMachine] using
    headSeq_leftSafe_at runtimeRoundEntryLocatorMachine
      (headSeqMachine runtimeWorkspaceLocatorMachine
        runtimeWorkspaceTailLocatorMachine)
      T T 0 markerClock (workspaceClock + 1 + tailClock) markerHead
      RuntimeRoundEntryState.done (by simpa using hmarker) rfl
      (runtimeRoundEntryLocator_leftSafe T markerClock) hsInner
      (by rw [show run (headSeqMachine runtimeWorkspaceLocatorMachine
          runtimeWorkspaceTailLocatorMachine)
          (workspaceClock + 1 + tailClock)
          ⟨(headSeqMachine runtimeWorkspaceLocatorMachine
            runtimeWorkspaceTailLocatorMachine).start, markerHead, T⟩ =
          ⟨Sum.inr RuntimeWorkspaceTailLocatorState.done,
            tailHead, T⟩ by simpa using hinner]; rfl)

set_option maxHeartbeats 4000000 in
/-- Generic marked origin-to-future-archive locator.  Unlike the round-zero
specialization, the aligned prefix may be any separator-safe pair list, so
the theorem applies to the surviving physical output prefix of later
scheduled rounds. -/
theorem runtimeMarkedWorkspaceTailLocator_safeRun
    (pairs : List (Bool × Bool)) (w : List Bool) (l : Lit)
    (first : List Bool) (more : List (List Bool))
    (hsafe : RuntimeNoDoubleSepFrom false pairs) :
    let bits := literalLookupTape w l
    let rest := first :: more
    let d := (bits :: rest).length
    let markerPre := flattenPairs pairs ++ [false, true, false, true]
    let sourcePre := flattenPairs (List.replicate d (true, true)) ++
      [false, true]
    let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ archiveTail
    let mcf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    let Tcash := markerPre ++ sourcePre ++ mcf.tp
    let markerClock := 2 * pairs.length + 7
    let workspaceClock := sourcePre.length + 2
    let tailClock := 8 * l.1 + 22
    let locateClock := markerClock + 1 +
      (workspaceClock + 1 + tailClock)
    let R := markerPre.length + sourcePre.length + 2 * bits.length + 4
    run runtimeMarkedWorkspaceTailLocatorMachine locateClock
        (init runtimeMarkedWorkspaceTailLocatorMachine Tcash) =
      ⟨Sum.inr (Sum.inr RuntimeWorkspaceTailLocatorState.done),
        R, Tcash⟩ ∧
      LeftSafeRun runtimeMarkedWorkspaceTailLocatorMachine
        (init runtimeMarkedWorkspaceTailLocatorMachine Tcash) locateClock := by
  dsimp only
  let bits := literalLookupTape w l
  let rest := first :: more
  let d := (bits :: rest).length
  let markerPre := flattenPairs pairs ++ [false, true, false, true]
  let sourcePre := flattenPairs (List.replicate d (true, true)) ++
    [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let Tcash := markerPre ++ sourcePre ++ mcf.tp
  let markerClock := 2 * pairs.length + 7
  let workspaceClock := sourcePre.length + 2
  let tailClock := 8 * l.1 + 22
  let locateClock := markerClock + 1 +
    (workspaceClock + 1 + tailClock)
  let R := markerPre.length + sourcePre.length + 2 * bits.length + 4
  have hd : 0 < d := by simp [d, rest]
  have hsourceCons : ∃ tail, sourcePre = true :: true :: tail := by
    cases hrep : List.replicate d (true, true) with
    | nil =>
        have hlen := congrArg List.length hrep
        simp [d, rest] at hlen
    | cons p ps =>
        have hp : p = (true, true) := by
          have hmem : p ∈ List.replicate d (true, true) := by
            rw [hrep]
            simp
          simpa using (List.mem_replicate.mp hmem).2
        subst p
        exact ⟨flattenPairs ps ++ [false, true], by
          simp [sourcePre, hrep, flattenPairs]⟩
  obtain ⟨sourceTail, hsourceCons⟩ := hsourceCons
  have htailShape : sourcePre ++ mcf.tp =
      true :: true :: (sourcePre ++ mcf.tp).drop 2 := by
    rw [hsourceCons]
    simp
  have hmarker : run runtimeRoundEntryLocatorMachine markerClock
      (init runtimeRoundEntryLocatorMachine Tcash) =
      ⟨RuntimeRoundEntryState.done, markerPre.length, Tcash⟩ := by
    simpa [markerClock, Tcash, markerPre, flattenPairs,
      List.append_assoc] using runtimeRoundEntryLocator_run pairs
        (sourcePre ++ mcf.tp) true true hsafe htailShape (by decide)
  have htoken := masterM_literal_startToken w l trailer
  have hsource : sourcePre = selectedPrefix d [] := by
    simp [sourcePre, selectedPrefix, selectedPrefixPairs,
      flattenPairs_append, flattenPairs]
  have hworkspace : run runtimeWorkspaceLocatorMachine workspaceClock
      ⟨RuntimeWorkspaceLocatorState.countLo, markerPre.length, Tcash⟩ =
      ⟨RuntimeWorkspaceLocatorState.done,
        markerPre.length + sourcePre.length, Tcash⟩ := by
    have h := runtimeWorkspaceLocator_run_prefixed markerPre d [] mcf.tp
      (by simpa [mcf, bits, trailer] using htoken.1)
      (by simpa [mcf, bits, trailer] using htoken.2)
    simpa [workspaceClock, Tcash, hsource, List.append_assoc] using h
  have htail0 := masterM_literal_workspaceTailLocate_prefixed
    (markerPre ++ sourcePre) w l first more
  have htail : run runtimeWorkspaceTailLocatorMachine tailClock
      ⟨RuntimeWorkspaceTailLocatorState.boot0,
        markerPre.length + sourcePre.length, Tcash⟩ =
      ⟨RuntimeWorkspaceTailLocatorState.done, R, Tcash⟩ := by
    simpa [tailClock, Tcash, mcf, bits, rest, trailer, R,
      List.append_assoc] using htail0
  have hinner := headSeq_run_at runtimeWorkspaceLocatorMachine
    runtimeWorkspaceTailLocatorMachine Tcash Tcash Tcash
    markerPre.length workspaceClock tailClock
    (markerPre.length + sourcePre.length) R
    RuntimeWorkspaceLocatorState.done
    RuntimeWorkspaceTailLocatorState.done hworkspace rfl htail rfl
  have hall := headSeq_run runtimeRoundEntryLocatorMachine
    (headSeqMachine runtimeWorkspaceLocatorMachine
      runtimeWorkspaceTailLocatorMachine)
    Tcash Tcash Tcash markerClock (workspaceClock + 1 + tailClock)
    markerPre.length R RuntimeRoundEntryState.done
    (Sum.inr RuntimeWorkspaceTailLocatorState.done)
    hmarker rfl (by simpa using hinner) rfl
  refine ⟨?_, ?_⟩
  · exact hall
  · exact runtimeMarkedWorkspaceTailLocator_leftSafe_of_runs Tcash
      markerClock workspaceClock tailClock markerPre.length
      (markerPre.length + sourcePre.length) R hmarker hworkspace htail

set_option maxHeartbeats 4000000 in
/-- Complete marked physical rebase from an arbitrary separator-safe aligned
prefix.  The two semantic premises are exactly the physical archive suffix
equation and the scratch-fit inequality; all machine clocks and safety
witnesses are constructed internally. -/
theorem runtimeMarkedPhysicalUnaryRebase_safeRun
    (pairs : List (Bool × Bool)) (w : List Bool) (l : Lit)
    (first : List Bool) (more : List (List Bool))
    (hsafe : RuntimeNoDoubleSepFrom false pairs)
    (hdrop :
      let bits := literalLookupTape w l
      let rest := first :: more
      let d := (bits :: rest).length
      let markerPre := flattenPairs pairs ++ [false, true, false, true]
      let sourcePre := flattenPairs (List.replicate d (true, true)) ++
        [false, true]
      let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
      let trailer := [true, false, false, true] ++
        List.replicate bits.length true ++ archiveTail
      let mcf := run masterM (literalLookupClock w l)
        (init masterM (bits ++ trailer))
      let Tcash := markerPre ++ sourcePre ++ mcf.tp
      let R := markerPre.length + sourcePre.length + 2 * bits.length + 4
      Tcash.drop R = selectedTail rest)
    (hfit :
      let bits := literalLookupTape w l
      let rest := first :: more
      let d := (bits :: rest).length
      let markerPre := flattenPairs pairs ++ [false, true, false, true]
      let sourcePre := flattenPairs (List.replicate d (true, true)) ++
        [false, true]
      let R := markerPre.length + sourcePre.length + 2 * bits.length + 4
      2 * rest.length + 4 ≤ R - 2) :
    let bits := literalLookupTape w l
    let rest := first :: more
    let d := (bits :: rest).length
    let markerPre := flattenPairs pairs ++ [false, true, false, true]
    let sourcePre := flattenPairs (List.replicate d (true, true)) ++
      [false, true]
    let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ archiveTail
    let mcf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    let Tcash := markerPre ++ sourcePre ++ mcf.tp
    let markerClock := 2 * pairs.length + 7
    let workspaceClock := sourcePre.length + 2
    let tailClock := 8 * l.1 + 22
    let locateClock := markerClock + 1 +
      (workspaceClock + 1 + tailClock)
    let seedClock := runtimeArchiveReturnSeedClock rest
    let prefixClock := locateClock + 1 + seedClock
    let R := markerPre.length + sourcePre.length + 2 * bits.length + 4
    ∃ base unaryClock,
      run runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine
          (prefixClock + 1 + unaryClock)
          (init runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine Tcash) =
        ⟨Sum.inr RuntimeUnaryRebaseState.done,
          R + (selectedTail rest).length,
          base ++ [false, true, false, true] ++
            sourceSelectorInput rest.length 0 rest⟩ ∧
      LeftSafeRun runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine
        (init runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine Tcash)
        (prefixClock + 1 + unaryClock) := by
  dsimp only
  let bits := literalLookupTape w l
  let rest := first :: more
  let d := (bits :: rest).length
  let markerPre := flattenPairs pairs ++ [false, true, false, true]
  let sourcePre := flattenPairs (List.replicate d (true, true)) ++
    [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let Tcash := markerPre ++ sourcePre ++ mcf.tp
  let markerClock := 2 * pairs.length + 7
  let workspaceClock := sourcePre.length + 2
  let tailClock := 8 * l.1 + 22
  let locateClock := markerClock + 1 +
    (workspaceClock + 1 + tailClock)
  let seedClock := runtimeArchiveReturnSeedClock rest
  let prefixClock := locateClock + 1 + seedClock
  let R := markerPre.length + sourcePre.length + 2 * bits.length + 4
  have hdrop' : Tcash.drop R = selectedTail rest := by
    exact hdrop
  have hfit' : 2 * rest.length + 4 ≤ R - 2 := by
    exact hfit
  have hR : 2 ≤ R := by simp [R, markerPre]
  have hsuffix : 0 < (selectedTail rest).length := by
    simp [selectedTail, rest, freshSourceBlock, flattenPairs_length]
  have hRlen : R ≤ Tcash.length := by
    have hlen := congrArg List.length hdrop'
    simp only [List.length_drop] at hlen
    omega
  obtain ⟨pre, a, b, hpre, hshape, hseed⟩ :=
    runtimeArchiveReturnSeed_run_of_drop Tcash R first more
      hR hRlen (by simpa [rest] using hdrop')
  have hpre2 : 2 ≤ pre.length := by
    rw [hpre]
    omega
  have hsseed0 := runtimeArchiveReturnSeed_leftSafe_prefixed
    pre a b first more hpre2
  have hsseed : LeftSafeRun runtimeArchiveReturnSeedMachine
      ⟨runtimeArchiveReturnSeedMachine.start, R, Tcash⟩ seedClock := by
    rw [hshape, show R = pre.length + 2 by omega]
    simpa [seedClock, rest] using hsseed0
  have hloc := runtimeMarkedWorkspaceTailLocator_safeRun
    pairs w l first more hsafe
  have hlocRun : run runtimeMarkedWorkspaceTailLocatorMachine locateClock
      (init runtimeMarkedWorkspaceTailLocatorMachine Tcash) =
      ⟨Sum.inr (Sum.inr RuntimeWorkspaceTailLocatorState.done),
        R, Tcash⟩ := by
    simpa [bits, rest, d, markerPre, sourcePre, archiveTail, trailer,
      mcf, Tcash, markerClock, workspaceClock, tailClock, locateClock, R]
      using hloc.1
  have hlocSafe : LeftSafeRun runtimeMarkedWorkspaceTailLocatorMachine
      (init runtimeMarkedWorkspaceTailLocatorMachine Tcash) locateClock := by
    simpa [bits, rest, d, markerPre, sourcePre, archiveTail, trailer,
      mcf, Tcash, markerClock, workspaceClock, tailClock, locateClock, R]
      using hloc.2
  have hseedJoin := headSeq_run runtimeMarkedWorkspaceTailLocatorMachine
    runtimeArchiveReturnSeedMachine Tcash Tcash
    (pre ++ [false, true] ++ selectedTail rest)
    locateClock seedClock R R
    (Sum.inr (Sum.inr RuntimeWorkspaceTailLocatorState.done))
    (Sum.inr RuntimeRebaseSeedState.done)
    hlocRun rfl (by simpa [seedClock, rest] using hseed) rfl
  have hseedHalt : runtimeArchiveReturnSeedMachine.halt
      (run runtimeArchiveReturnSeedMachine seedClock
        ⟨runtimeArchiveReturnSeedMachine.start, R, Tcash⟩).st = true := by
    rw [show run runtimeArchiveReturnSeedMachine seedClock
        ⟨runtimeArchiveReturnSeedMachine.start, R, Tcash⟩ =
      ⟨Sum.inr RuntimeRebaseSeedState.done, R,
        pre ++ [false, true] ++ selectedTail rest⟩ by
          simpa [seedClock, rest] using hseed]
    rfl
  have hseedSafe := headSeq_leftSafe
    runtimeMarkedWorkspaceTailLocatorMachine runtimeArchiveReturnSeedMachine
    Tcash Tcash locateClock seedClock R
    (Sum.inr (Sum.inr RuntimeWorkspaceTailLocatorState.done))
    hlocRun rfl hlocSafe hsseed hseedHalt
  obtain ⟨base, unaryClock, _, _, hunary, hsunary⟩ :=
    runtimeUnaryRebase_physical_safeRun pre first more
      (by simpa [rest, hpre] using hfit')
  have hRpre : pre.length + 2 = R := by omega
  have hunary' : run runtimeUnaryRebaseMachine unaryClock
      ⟨RuntimeUnaryRebaseState.init1, R,
        pre ++ [false, true] ++ selectedTail rest⟩ =
      ⟨RuntimeUnaryRebaseState.done,
        R + (selectedTail rest).length,
        base ++ [false, true, false, true] ++
          sourceSelectorInput rest.length 0 rest⟩ := by
    simpa [rest, hRpre] using hunary
  have hsunary' : LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.init1, R,
        pre ++ [false, true] ++ selectedTail rest⟩ unaryClock := by
    simpa [rest, hRpre] using hsunary
  have hjoin := headSeq_run runtimeMarkedWorkspaceArchiveReturnSeedMachine
    runtimeUnaryRebaseMachine Tcash
    (pre ++ [false, true] ++ selectedTail rest)
    (base ++ [false, true, false, true] ++
      sourceSelectorInput rest.length 0 rest)
    prefixClock unaryClock R (R + (selectedTail rest).length)
    (Sum.inr (Sum.inr RuntimeRebaseSeedState.done))
    RuntimeUnaryRebaseState.done
    (by simpa [runtimeMarkedWorkspaceArchiveReturnSeedMachine,
      prefixClock] using hseedJoin) rfl hunary' rfl
  have hsjoin := headSeq_leftSafe
    runtimeMarkedWorkspaceArchiveReturnSeedMachine runtimeUnaryRebaseMachine
    Tcash (pre ++ [false, true] ++ selectedTail rest)
    prefixClock unaryClock R
    (Sum.inr (Sum.inr RuntimeRebaseSeedState.done))
    (by simpa [runtimeMarkedWorkspaceArchiveReturnSeedMachine,
      prefixClock] using hseedJoin) rfl
    (by simpa [runtimeMarkedWorkspaceArchiveReturnSeedMachine,
      prefixClock] using hseedSafe)
    hsunary' (by
      have hh := congrArg (fun c => runtimeUnaryRebaseMachine.halt c.st)
        hunary'
      simpa [runtimeUnaryRebaseMachine] using hh)
  exact ⟨base, unaryClock, hjoin, hsjoin⟩

set_option maxHeartbeats 4000000 in
/-- Unconditional form of the generic marked controller on the concrete
completed-literal workspace.  Tail preservation supplies the archive `drop`
equation, while the selector prefix alone supplies enough unary scratch. -/
theorem runtimeMarkedPhysicalUnaryRebase_complete
    (pairs : List (Bool × Bool)) (w : List Bool) (l : Lit)
    (first : List Bool) (more : List (List Bool))
    (hsafe : RuntimeNoDoubleSepFrom false pairs) :
    let bits := literalLookupTape w l
    let rest := first :: more
    let d := (bits :: rest).length
    let markerPre := flattenPairs pairs ++ [false, true, false, true]
    let sourcePre := flattenPairs (List.replicate d (true, true)) ++
      [false, true]
    let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ archiveTail
    let mcf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    let Tcash := markerPre ++ sourcePre ++ mcf.tp
    let markerClock := 2 * pairs.length + 7
    let workspaceClock := sourcePre.length + 2
    let tailClock := 8 * l.1 + 22
    let locateClock := markerClock + 1 +
      (workspaceClock + 1 + tailClock)
    let seedClock := runtimeArchiveReturnSeedClock rest
    let prefixClock := locateClock + 1 + seedClock
    let R := markerPre.length + sourcePre.length + 2 * bits.length + 4
    ∃ base unaryClock,
      run runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine
          (prefixClock + 1 + unaryClock)
          (init runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine Tcash) =
        ⟨Sum.inr RuntimeUnaryRebaseState.done,
          R + (selectedTail rest).length,
          base ++ [false, true, false, true] ++
            sourceSelectorInput rest.length 0 rest⟩ ∧
      LeftSafeRun runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine
        (init runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine Tcash)
        (prefixClock + 1 + unaryClock) := by
  dsimp only
  let bits := literalLookupTape w l
  let rest := first :: more
  let d := (bits :: rest).length
  let markerPre := flattenPairs pairs ++ [false, true, false, true]
  let sourcePre := flattenPairs (List.replicate d (true, true)) ++
    [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let Tcash := markerPre ++ sourcePre ++ mcf.tp
  let R := markerPre.length + sourcePre.length + 2 * bits.length + 4
  have hmaster := masterM_literal_trailer w l trailer
  have hmcf : mcf.tp.drop bits.length = trailer := by
    simpa [bits, trailer, mcf] using hmaster
  have hmcfTail : mcf.tp.drop (2 * bits.length + 4) =
      selectedTail rest := by
    rw [show 2 * bits.length + 4 = bits.length + (4 + bits.length) by omega,
      ← List.drop_drop, hmcf]
    change List.drop (4 + bits.length)
      ([true, false, false, true] ++ List.replicate bits.length true ++
        archiveTail) = selectedTail rest
    rw [show 4 + bits.length =
      4 + (List.replicate bits.length true).length by simp,
      ← List.drop_drop]
    simp [archiveTail, selectedTail]
  have hdrop : Tcash.drop R = selectedTail rest := by
    rw [show R = (markerPre ++ sourcePre).length +
        (2 * bits.length + 4) by simp [R]; omega,
      ← List.drop_drop]
    simp [Tcash, List.append_assoc, hmcfTail]
  have hfit : 2 * rest.length + 4 ≤ R - 2 := by
    simp [R, markerPre, sourcePre, flattenPairs_length, d, rest]
    omega
  exact runtimeMarkedPhysicalUnaryRebase_safeRun
    pairs w l first more hsafe hdrop hfit

set_option maxHeartbeats 4000000 in
theorem runtimeRoundZero_markedWorkspaceTailLocate_leftSafe
    (w : List Bool) (l : Lit) (first : List Bool)
    (more : List (List Bool)) :
    let bits := literalLookupTape w l
    let rest := first :: more
    let B := (bits :: rest).length
    let bv := evalLit (fun k => w.getD k false) l
    let pairs := runtimeOutputCapPairs B [bv]
    let markerPre := flattenPairs pairs ++ [false, true, false, true]
    let sourcePre := flattenPairs (List.replicate B (true, true)) ++
      [false, true]
    let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ archiveTail
    let mcf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    let Tcash := markerPre ++ sourcePre ++ mcf.tp
    let markerClock := 2 * pairs.length + 7
    let workspaceClock := sourcePre.length + 2
    let tailClock := 8 * l.1 + 22
    LeftSafeRun runtimeMarkedWorkspaceTailLocatorMachine
      (init runtimeMarkedWorkspaceTailLocatorMachine Tcash)
      (markerClock + 1 + (workspaceClock + 1 + tailClock)) := by
  dsimp only
  let bits := literalLookupTape w l
  let rest := first :: more
  let B := (bits :: rest).length
  let bv := evalLit (fun k => w.getD k false) l
  let pairs := runtimeOutputCapPairs B [bv]
  let markerPre := flattenPairs pairs ++ [false, true, false, true]
  let sourcePre := flattenPairs (List.replicate B (true, true)) ++
    [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let Tcash := markerPre ++ sourcePre ++ mcf.tp
  let markerClock := 2 * pairs.length + 7
  let workspaceClock := sourcePre.length + 2
  let tailClock := 8 * l.1 + 22
  have hout : [bv].length < B := by simp [B, rest]
  have hpairs := (runtimeOutputCapPairs_safe B [bv] hout).1
  have hsourceCons : ∃ tail, sourcePre = true :: true :: tail := by
    cases hrep : List.replicate B (true, true) with
    | nil =>
        have hlen := congrArg List.length hrep
        simp at hlen
        simp [B, rest] at hlen
    | cons p ps =>
        have hp : p = (true, true) := by
          have hmem : p ∈ List.replicate B (true, true) := by
            rw [hrep]
            simp
          simpa using (List.mem_replicate.mp hmem).2
        subst p
        exact ⟨flattenPairs ps ++ [false, true], by
          simp [sourcePre, hrep, flattenPairs]⟩
  obtain ⟨sourceTail, hsourceCons⟩ := hsourceCons
  have htailShape : sourcePre ++ mcf.tp =
      true :: true :: (sourcePre ++ mcf.tp).drop 2 := by
    rw [hsourceCons]
    simp
  have hmarker : run runtimeRoundEntryLocatorMachine markerClock
      (init runtimeRoundEntryLocatorMachine Tcash) =
      ⟨RuntimeRoundEntryState.done, markerPre.length, Tcash⟩ := by
    simpa [markerClock, Tcash, markerPre, flattenPairs,
      List.append_assoc] using runtimeRoundEntryLocator_run pairs
        (sourcePre ++ mcf.tp) true true hpairs htailShape (by decide)
  have htoken := masterM_literal_startToken w l trailer
  have hsource : sourcePre = selectedPrefix B [] := by
    simp [sourcePre, selectedPrefix, selectedPrefixPairs,
      flattenPairs_append, flattenPairs]
  have hworkspace : run runtimeWorkspaceLocatorMachine workspaceClock
      ⟨RuntimeWorkspaceLocatorState.countLo, markerPre.length, Tcash⟩ =
      ⟨RuntimeWorkspaceLocatorState.done,
        markerPre.length + sourcePre.length, Tcash⟩ := by
    have h := runtimeWorkspaceLocator_run_prefixed markerPre B [] mcf.tp
      (by simpa [mcf, bits, trailer] using htoken.1)
      (by simpa [mcf, bits, trailer] using htoken.2)
    simpa [workspaceClock, Tcash, hsource, List.append_assoc] using h
  have htail0 := masterM_literal_workspaceTailLocate_prefixed
    (markerPre ++ sourcePre) w l first more
  have htail : run runtimeWorkspaceTailLocatorMachine tailClock
      ⟨RuntimeWorkspaceTailLocatorState.boot0,
        markerPre.length + sourcePre.length, Tcash⟩ =
      ⟨RuntimeWorkspaceTailLocatorState.done,
        markerPre.length + sourcePre.length + 2 * bits.length + 4,
        Tcash⟩ := by
    simpa [tailClock, Tcash, mcf, bits, rest, trailer,
      List.append_assoc] using htail0
  exact runtimeMarkedWorkspaceTailLocator_leftSafe_of_runs Tcash
    markerClock workspaceClock tailClock markerPre.length
    (markerPre.length + sourcePre.length)
    (markerPre.length + sourcePre.length + 2 * bits.length + 4)
    hmarker hworkspace htail

set_option maxHeartbeats 4000000 in
/-- Marked origin-to-archive discovery followed by canonical archive return
and seed installation. -/
theorem runtimeRoundZero_markedWorkspaceArchiveReturnSeed_run
    (w : List Bool) (l : Lit) (first : List Bool)
    (more : List (List Bool)) :
    let bits := literalLookupTape w l
    let rest := first :: more
    let B := (bits :: rest).length
    let bv := evalLit (fun k => w.getD k false) l
    let pairs := runtimeOutputCapPairs B [bv]
    let markerPre := flattenPairs pairs ++ [false, true, false, true]
    let sourcePre := flattenPairs (List.replicate B (true, true)) ++
      [false, true]
    let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ archiveTail
    let mcf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    let Tcash := markerPre ++ sourcePre ++ mcf.tp
    let markerClock := 2 * pairs.length + 7
    let workspaceClock := sourcePre.length + 2
    let tailClock := 8 * l.1 + 22
    let locateClock := markerClock + 1 +
      (workspaceClock + 1 + tailClock)
    let seedClock := runtimeArchiveReturnSeedClock rest
    let R := 4 * B + 2 * bits.length + 12
    ∃ pre a b,
      pre.length = R - 2 ∧
      Tcash = pre ++ [a, b] ++ selectedTail rest ∧
      run runtimeMarkedWorkspaceArchiveReturnSeedMachine
          (locateClock + 1 + seedClock)
          (init runtimeMarkedWorkspaceArchiveReturnSeedMachine Tcash) =
        ⟨Sum.inr (Sum.inr RuntimeRebaseSeedState.done), R,
          pre ++ [false, true] ++ selectedTail rest⟩ := by
  dsimp only
  let bits := literalLookupTape w l
  let rest := first :: more
  let B := (bits :: rest).length
  let bv := evalLit (fun k => w.getD k false) l
  let pairs := runtimeOutputCapPairs B [bv]
  let markerPre := flattenPairs pairs ++ [false, true, false, true]
  let sourcePre := flattenPairs (List.replicate B (true, true)) ++
    [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let Tcash := markerPre ++ sourcePre ++ mcf.tp
  let markerClock := 2 * pairs.length + 7
  let workspaceClock := sourcePre.length + 2
  let tailClock := 8 * l.1 + 22
  let locateClock := markerClock + 1 +
    (workspaceClock + 1 + tailClock)
  let seedClock := runtimeArchiveReturnSeedClock rest
  let R := 4 * B + 2 * bits.length + 12
  have hcap : flattenPairs pairs = outputCap B [bv] := by
    simpa [pairs] using runtimeOutputCapPairs_flatten B [bv]
  have hTcash : Tcash = outputCap B [bv] ++
      [false, true, false, true] ++ sourcePre ++ mcf.tp := by
    simp [Tcash, markerPre, hcap, List.append_assoc]
  have hloc := runtimeRoundZero_markedWorkspaceTailLocate w l first more
  have hloc' : run runtimeMarkedWorkspaceTailLocatorMachine locateClock
      (init runtimeMarkedWorkspaceTailLocatorMachine Tcash) =
      ⟨Sum.inr (Sum.inr RuntimeWorkspaceTailLocatorState.done),
        R, Tcash⟩ := by
    simpa [bits, rest, B, bv, pairs, markerPre, sourcePre, archiveTail,
      trailer, mcf, Tcash, markerClock, workspaceClock, tailClock,
      locateClock, R] using hloc
  obtain ⟨pre, a, b, hpre, hshape, hseed, _⟩ :=
    runtimeRoundZero_markedCashout_archiveReturnSeed_safeRun
      w l first more
  have hseed' : run runtimeArchiveReturnSeedMachine seedClock
      ⟨runtimeArchiveReturnSeedMachine.start, R, Tcash⟩ =
      ⟨Sum.inr RuntimeRebaseSeedState.done, R,
        pre ++ [false, true] ++ selectedTail rest⟩ := by
    rw [hTcash]
    exact hseed
  have hall := headSeq_run runtimeMarkedWorkspaceTailLocatorMachine
    runtimeArchiveReturnSeedMachine Tcash Tcash
    (pre ++ [false, true] ++ selectedTail rest)
    locateClock seedClock R R
    (Sum.inr (Sum.inr RuntimeWorkspaceTailLocatorState.done))
    (Sum.inr RuntimeRebaseSeedState.done) hloc' rfl hseed' rfl
  refine ⟨pre, a, b, hpre, ?_, ?_⟩
  · rw [hcap]
    exact hshape
  · simpa [runtimeMarkedWorkspaceArchiveReturnSeedMachine, locateClock,
      markerClock, workspaceClock, tailClock, seedClock, sourcePre,
      flattenPairs_length, pairs, B, rest, bv, bits, Tcash, markerPre,
      archiveTail, trailer, mcf, R, List.append_assoc] using hall

set_option maxHeartbeats 4000000 in
/-- The exact marked locator/archive-seed composition is left-safe under the
same phase clocks used by its concrete run theorem. -/
theorem runtimeRoundZero_markedWorkspaceArchiveReturnSeed_leftSafe
    (w : List Bool) (l : Lit) (first : List Bool)
    (more : List (List Bool)) :
    let bits := literalLookupTape w l
    let rest := first :: more
    let B := (bits :: rest).length
    let bv := evalLit (fun k => w.getD k false) l
    let pairs := runtimeOutputCapPairs B [bv]
    let markerPre := flattenPairs pairs ++ [false, true, false, true]
    let sourcePre := flattenPairs (List.replicate B (true, true)) ++
      [false, true]
    let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ archiveTail
    let mcf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    let Tcash := markerPre ++ sourcePre ++ mcf.tp
    let markerClock := 2 * pairs.length + 7
    let workspaceClock := sourcePre.length + 2
    let tailClock := 8 * l.1 + 22
    let locateClock := markerClock + 1 +
      (workspaceClock + 1 + tailClock)
    let seedClock := runtimeArchiveReturnSeedClock rest
    LeftSafeRun runtimeMarkedWorkspaceArchiveReturnSeedMachine
      (init runtimeMarkedWorkspaceArchiveReturnSeedMachine Tcash)
      (locateClock + 1 + seedClock) := by
  dsimp only
  let bits := literalLookupTape w l
  let rest := first :: more
  let B := (bits :: rest).length
  let bv := evalLit (fun k => w.getD k false) l
  let pairs := runtimeOutputCapPairs B [bv]
  let markerPre := flattenPairs pairs ++ [false, true, false, true]
  let sourcePre := flattenPairs (List.replicate B (true, true)) ++
    [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let Tcash := markerPre ++ sourcePre ++ mcf.tp
  let markerClock := 2 * pairs.length + 7
  let workspaceClock := sourcePre.length + 2
  let tailClock := 8 * l.1 + 22
  let locateClock := markerClock + 1 +
    (workspaceClock + 1 + tailClock)
  let seedClock := runtimeArchiveReturnSeedClock rest
  let R := 4 * B + 2 * bits.length + 12
  have hcap : flattenPairs pairs = outputCap B [bv] := by
    simpa [pairs] using runtimeOutputCapPairs_flatten B [bv]
  have hTcash : Tcash = outputCap B [bv] ++
      [false, true, false, true] ++ sourcePre ++ mcf.tp := by
    simp [Tcash, markerPre, hcap, List.append_assoc]
  have hloc0 := runtimeRoundZero_markedWorkspaceTailLocate w l first more
  have hloc : run runtimeMarkedWorkspaceTailLocatorMachine locateClock
      (init runtimeMarkedWorkspaceTailLocatorMachine Tcash) =
      ⟨Sum.inr (Sum.inr RuntimeWorkspaceTailLocatorState.done),
        R, Tcash⟩ := by
    simpa [bits, rest, B, bv, pairs, markerPre, sourcePre, archiveTail,
      trailer, mcf, Tcash, markerClock, workspaceClock, tailClock,
      locateClock, R] using hloc0
  have hsLoc0 := runtimeRoundZero_markedWorkspaceTailLocate_leftSafe
    w l first more
  have hsLoc : LeftSafeRun runtimeMarkedWorkspaceTailLocatorMachine
      (init runtimeMarkedWorkspaceTailLocatorMachine Tcash) locateClock := by
    simpa [bits, rest, B, bv, pairs, markerPre, sourcePre, archiveTail,
      trailer, mcf, Tcash, markerClock, workspaceClock, tailClock,
      locateClock] using hsLoc0
  obtain ⟨pre, a, b, _, _, hseed, hsSeed0⟩ :=
    runtimeRoundZero_markedCashout_archiveReturnSeed_safeRun
      w l first more
  have hseed' : run runtimeArchiveReturnSeedMachine seedClock
      ⟨runtimeArchiveReturnSeedMachine.start, R, Tcash⟩ =
      ⟨Sum.inr RuntimeRebaseSeedState.done, R,
        pre ++ [false, true] ++ selectedTail rest⟩ := by
    rw [hTcash]
    exact hseed
  have hsSeed : LeftSafeRun runtimeArchiveReturnSeedMachine
      ⟨runtimeArchiveReturnSeedMachine.start, R, Tcash⟩ seedClock := by
    rw [hTcash]
    exact hsSeed0
  have hhSeed : runtimeArchiveReturnSeedMachine.halt
      (run runtimeArchiveReturnSeedMachine seedClock
        ⟨runtimeArchiveReturnSeedMachine.start, R, Tcash⟩).st = true := by
    rw [hseed']
    rfl
  simpa [runtimeMarkedWorkspaceArchiveReturnSeedMachine, locateClock,
    markerClock, workspaceClock, tailClock, seedClock, sourcePre,
    flattenPairs_length, pairs, B, rest, bv, bits, Tcash, markerPre,
    archiveTail, trailer, mcf, List.append_assoc] using
    headSeq_leftSafe runtimeMarkedWorkspaceTailLocatorMachine
      runtimeArchiveReturnSeedMachine Tcash Tcash locateClock seedClock R
      (Sum.inr (Sum.inr RuntimeWorkspaceTailLocatorState.done))
      hloc rfl hsLoc hsSeed hhSeed

set_option maxHeartbeats 4000000 in
/-- Complete marked physical controller through unary rebasing. -/
theorem runtimeRoundZero_markedPhysicalUnaryRebase_safeRun
    (w : List Bool) (l : Lit) (first : List Bool)
    (more : List (List Bool)) :
    let bits := literalLookupTape w l
    let rest := first :: more
    let B := (bits :: rest).length
    let bv := evalLit (fun k => w.getD k false) l
    let pairs := runtimeOutputCapPairs B [bv]
    let markerPre := flattenPairs pairs ++ [false, true, false, true]
    let sourcePre := flattenPairs (List.replicate B (true, true)) ++
      [false, true]
    let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ archiveTail
    let mcf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    let Tcash := markerPre ++ sourcePre ++ mcf.tp
    let markerClock := 2 * pairs.length + 7
    let workspaceClock := sourcePre.length + 2
    let tailClock := 8 * l.1 + 22
    let locateClock := markerClock + 1 +
      (workspaceClock + 1 + tailClock)
    let seedClock := runtimeArchiveReturnSeedClock rest
    let prefixClock := locateClock + 1 + seedClock
    let R := 4 * B + 2 * bits.length + 12
    ∃ base unaryClock,
      run runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine
          (prefixClock + 1 + unaryClock)
          (init runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine Tcash) =
        ⟨Sum.inr RuntimeUnaryRebaseState.done,
          R + (selectedTail rest).length,
          base ++ [false, true, false, true] ++
            sourceSelectorInput rest.length 0 rest⟩ ∧
      LeftSafeRun runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine
        (init runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine Tcash)
        (prefixClock + 1 + unaryClock) := by
  dsimp only
  let bits := literalLookupTape w l
  let rest := first :: more
  let B := (bits :: rest).length
  let bv := evalLit (fun k => w.getD k false) l
  let pairs := runtimeOutputCapPairs B [bv]
  let markerPre := flattenPairs pairs ++ [false, true, false, true]
  let sourcePre := flattenPairs (List.replicate B (true, true)) ++
    [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let Tcash := markerPre ++ sourcePre ++ mcf.tp
  let markerClock := 2 * pairs.length + 7
  let workspaceClock := sourcePre.length + 2
  let tailClock := 8 * l.1 + 22
  let locateClock := markerClock + 1 +
    (workspaceClock + 1 + tailClock)
  let seedClock := runtimeArchiveReturnSeedClock rest
  let prefixClock := locateClock + 1 + seedClock
  let R := 4 * B + 2 * bits.length + 12
  obtain ⟨pre, a, b, hpre, hshape, hseedrun⟩ :=
    runtimeRoundZero_markedWorkspaceArchiveReturnSeed_run w l first more
  have hfit : 2 * rest.length + 4 ≤ pre.length := by
    rw [hpre]
    simp [R, B, rest]
    omega
  obtain ⟨base, unaryClock, _, _, hunary, hsunary⟩ :=
    runtimeUnaryRebase_physical_safeRun pre first more
      (by simpa [rest] using hfit)
  have hR : pre.length + 2 = R := by
    rw [hpre]
    exact Nat.sub_add_cancel (by simp [R])
  have hunary' : run runtimeUnaryRebaseMachine unaryClock
      ⟨RuntimeUnaryRebaseState.init1, R,
        pre ++ [false, true] ++ selectedTail rest⟩ =
      ⟨RuntimeUnaryRebaseState.done,
        R + (selectedTail rest).length,
        base ++ [false, true, false, true] ++
          sourceSelectorInput rest.length 0 rest⟩ := by
    simpa [rest, hR] using hunary
  have hsunary' : LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.init1, R,
        pre ++ [false, true] ++ selectedTail rest⟩ unaryClock := by
    simpa [rest, hR] using hsunary
  have hsseed0 := runtimeRoundZero_markedWorkspaceArchiveReturnSeed_leftSafe
    w l first more
  have hsseed : LeftSafeRun runtimeMarkedWorkspaceArchiveReturnSeedMachine
      (init runtimeMarkedWorkspaceArchiveReturnSeedMachine Tcash)
      prefixClock := by
    simpa [bits, rest, B, bv, pairs, markerPre, sourcePre, archiveTail,
      trailer, mcf, Tcash, markerClock, workspaceClock, tailClock,
      locateClock, seedClock, prefixClock] using hsseed0
  have hseedrun' : run runtimeMarkedWorkspaceArchiveReturnSeedMachine
      prefixClock (init runtimeMarkedWorkspaceArchiveReturnSeedMachine Tcash) =
      ⟨Sum.inr (Sum.inr RuntimeRebaseSeedState.done), R,
        pre ++ [false, true] ++ selectedTail rest⟩ := by
    simpa [bits, rest, B, bv, pairs, markerPre, sourcePre, archiveTail,
      trailer, mcf, Tcash, markerClock, workspaceClock, tailClock,
      locateClock, seedClock, prefixClock, R] using hseedrun
  have hjoin := headSeq_run runtimeMarkedWorkspaceArchiveReturnSeedMachine
    runtimeUnaryRebaseMachine Tcash
    (pre ++ [false, true] ++ selectedTail rest)
    (base ++ [false, true, false, true] ++
      sourceSelectorInput rest.length 0 rest)
    prefixClock unaryClock R (R + (selectedTail rest).length)
    (Sum.inr (Sum.inr RuntimeRebaseSeedState.done))
    RuntimeUnaryRebaseState.done hseedrun' rfl hunary' rfl
  have hsjoin := headSeq_leftSafe
    runtimeMarkedWorkspaceArchiveReturnSeedMachine runtimeUnaryRebaseMachine
    Tcash (pre ++ [false, true] ++ selectedTail rest)
    prefixClock unaryClock R
    (Sum.inr (Sum.inr RuntimeRebaseSeedState.done))
    hseedrun' rfl hsseed hsunary' (by
      have := congrArg (fun c => runtimeUnaryRebaseMachine.halt c.st) hunary'
      simpa [runtimeUnaryRebaseMachine] using this)
  refine ⟨base, unaryClock, ?_, ?_⟩
  · simpa [runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine,
      prefixClock, locateClock, markerClock, workspaceClock, tailClock,
      seedClock, sourcePre, flattenPairs_length, pairs, B, rest, bv, bits,
      Tcash, markerPre, archiveTail, trailer, mcf, R, List.append_assoc]
      using hjoin
  · simpa [runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine,
      prefixClock, locateClock, markerClock, workspaceClock, tailClock,
      seedClock, sourcePre, flattenPairs_length, pairs, B, rest, bv, bits,
      Tcash, markerPre, archiveTail, trailer, mcf, R, List.append_assoc]
      using hsjoin

/-! ## Fixed round body -/

def runtimeFixedRoundBody : Machine :=
  seqMachine runtimeMarkedFrontOutputMachine runtimeContinuationDispatchMachine

/-- The single datum needed for one indexed use of `runtimeRep_run`: an
exact transition to the next tail, together with halt and left-safety at the
same clock and endpoint. -/
def RuntimeFixedRoundCertificate (T T' : List Bool) : Prop :=
  ∃ clock sf pf,
    run runtimeFixedRoundBody clock (init runtimeFixedRoundBody T) =
        ⟨sf, pf, T'⟩ ∧
      runtimeFixedRoundBody.halt sf = true ∧
      LeftSafeRun runtimeFixedRoundBody
        (init runtimeFixedRoundBody T) clock

/-- Convert per-index existential round certificates into the coherent
clock/state/head functions expected by `runtimeRep_run`.  Values outside the
live range are harmless defaults; inside `t < B`, all three projections come
from the same certificate. -/
theorem runtimeFixedRound_family_of_certificates (B : Nat)
    (tail : Nat → List Bool)
    (hcert : ∀ t, t < B →
      RuntimeFixedRoundCertificate (tail t) (tail (t + 1))) :
    ∃ bodyClock : Nat → Nat,
      ∃ sf : Nat → runtimeFixedRoundBody.State,
      ∃ pf : Nat → Nat,
        (∀ t, t < B →
          run runtimeFixedRoundBody (bodyClock t)
              (init runtimeFixedRoundBody (tail t)) =
            ⟨sf t, pf t, tail (t + 1)⟩) ∧
        (∀ t, t < B → runtimeFixedRoundBody.halt (sf t) = true) ∧
        (∀ t, t < B →
          LeftSafeRun runtimeFixedRoundBody
            (init runtimeFixedRoundBody (tail t)) (bodyClock t)) := by
  let bodyClock := fun t => if ht : t < B then (hcert t ht).choose else 0
  let sf := fun t => if ht : t < B then
    (hcert t ht).choose_spec.choose else runtimeFixedRoundBody.start
  let pf := fun t => if ht : t < B then
    (hcert t ht).choose_spec.choose_spec.choose else 0
  refine ⟨bodyClock, sf, pf, ?_, ?_, ?_⟩
  · intro t ht
    simp only [bodyClock, sf, pf, dif_pos ht]
    exact (hcert t ht).choose_spec.choose_spec.choose_spec.1
  · intro t ht
    simp only [sf, dif_pos ht]
    exact (hcert t ht).choose_spec.choose_spec.choose_spec.2.1
  · intro t ht
    simp only [bodyClock, dif_pos ht]
    exact (hcert t ht).choose_spec.choose_spec.choose_spec.2.2

/-- Direct existential-clock application of `runtimeRep_run`.  Once a
concrete scheduled construction supplies one synchronized certificate for
each live index, the verified repetition controller and its countdown
adapter run end to end with no further clock/state witness choices. -/
theorem runtimeRep_run_of_fixedRound_certificates (B : Nat)
    (tail : Nat → List Bool)
    (hcert : ∀ t, t < B →
      RuntimeFixedRoundCertificate (tail t) (tail (t + 1))) :
    ∃ totalClock,
      run (repMachine (runtimeCountdownBody B runtimeFixedRoundBody))
          totalClock
          (init (repMachine (runtimeCountdownBody B runtimeFixedRoundBody))
            (cntT B 0 ++ tail 0)) =
        ⟨Sum.inl (4, false), 2 * B + 1, unaryD B ++ tail B⟩ := by
  obtain ⟨bodyClock, sf, pf, hrun, hhalt, hleft⟩ :=
    runtimeFixedRound_family_of_certificates B tail hcert
  let protectedClock := fun t =>
    runtimeCountdownBodyClock B runtimeFixedRoundBody
      (tail t) (bodyClock t)
  refine ⟨repRounds protectedClock B + (4 * B + 4), ?_⟩
  simpa [protectedClock] using
    (runtimeRep_run runtimeFixedRoundBody B tail bodyClock sf pf
      hrun hhalt hleft)

/-- Finite-chain interface for the concrete scheduled construction.  A list
of `B + 1` physical tapes and synchronized certificates between adjacent
entries is enough to run the complete repetition controller. -/
theorem runtimeRep_run_of_fixedRound_chain (B : Nat)
    (tapes : List (List Bool))
    (hlen : tapes.length = B + 1)
    (hchain : ∀ t, t < B →
      RuntimeFixedRoundCertificate (tapes.getD t [])
        (tapes.getD (t + 1) [])) :
    ∃ totalClock,
      run (repMachine (runtimeCountdownBody B runtimeFixedRoundBody))
          totalClock
          (init (repMachine (runtimeCountdownBody B runtimeFixedRoundBody))
            (cntT B 0 ++ tapes.getD 0 [])) =
        ⟨Sum.inl (4, false), 2 * B + 1,
          unaryD B ++ tapes.getD B []⟩ := by
  let tail := fun t => tapes.getD t []
  have hcert : ∀ t, t < B →
      RuntimeFixedRoundCertificate (tail t) (tail (t + 1)) := by
    intro t ht
    exact hchain t ht
  simpa [tail] using
    (runtimeRep_run_of_fixedRound_certificates B tail hcert)

def runtimeFixedRoundClock (pairs : List (Bool × Bool))
    (d : Nat) (w : List Bool) (l : Lit) (out : List Bool)
    (dispatchClock : Nat) : Nat :=
  runtimeMarkedFrontOutputClock pairs d w l out + 1 + dispatchClock

/-- Exact terminal round assembly from the already concrete cashout and
terminal-dispatch endpoints. -/
theorem runtimeFixedRound_run_terminal_of_runs
    (T T' : List Bool) (cashClock dispatchClock pf : Nat)
    (sf : runtimeMarkedFrontOutputMachine.State)
    (hcash : run runtimeMarkedFrontOutputMachine cashClock
      (init runtimeMarkedFrontOutputMachine T) = ⟨sf, pf, T'⟩)
    (hhcash : runtimeMarkedFrontOutputMachine.halt sf = true)
    (hdispatch : run runtimeContinuationDispatchMachine dispatchClock
      (init runtimeContinuationDispatchMachine T') =
        ⟨Sum.inr (Sum.inr ()), 0, T'⟩) :
    run runtimeFixedRoundBody (cashClock + 1 + dispatchClock)
        (init runtimeFixedRoundBody T) =
      ⟨Sum.inr (Sum.inr (Sum.inr ())), 0, T'⟩ := by
  simpa [runtimeFixedRoundBody] using
    seq_run runtimeMarkedFrontOutputMachine
      runtimeContinuationDispatchMachine T T' T' cashClock dispatchClock
      sf pf (Sum.inr (Sum.inr ())) 0 hcash hhcash hdispatch
      runtimeContinuationDispatch_halt_terminal

/-- Exact nonterminal round assembly from cashout into the physical
archive-return/unary-rebase arm selected by the continuation classifier. -/
theorem runtimeFixedRound_run_nonterminal_of_runs
    (T T' T'' : List Bool) (cashClock dispatchClock pf rebaseHead : Nat)
    (sf : runtimeMarkedFrontOutputMachine.State)
    (rebaseState : runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine.State)
    (hcash : run runtimeMarkedFrontOutputMachine cashClock
      (init runtimeMarkedFrontOutputMachine T) = ⟨sf, pf, T'⟩)
    (hhcash : runtimeMarkedFrontOutputMachine.halt sf = true)
    (hdispatch : run runtimeContinuationDispatchMachine dispatchClock
      (init runtimeContinuationDispatchMachine T') =
        ⟨Sum.inr (Sum.inl rebaseState), rebaseHead, T''⟩)
    (hhrebase : runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine.halt
      rebaseState = true) :
    run runtimeFixedRoundBody (cashClock + 1 + dispatchClock)
        (init runtimeFixedRoundBody T) =
      ⟨Sum.inr (Sum.inr (Sum.inl rebaseState)), rebaseHead, T''⟩ := by
  simpa [runtimeFixedRoundBody] using
    seq_run runtimeMarkedFrontOutputMachine
      runtimeContinuationDispatchMachine T T' T'' cashClock dispatchClock
      sf pf (Sum.inr (Sum.inl rebaseState)) rebaseHead hcash hhcash
      hdispatch (runtimeContinuationDispatch_halt_nonterminal _ hhrebase)

/-! ## Resetting sequential-composition safety -/

theorem seq_leftSafe_inl (M1 M2 : Machine) (c : Cfg M1)
    (t : Nat) (hno : ∀ i < t, M1.halt (run M1 i c).st = false)
    (hsafe : LeftSafeRun M1 c t) :
    LeftSafeRun (seqMachine M1 M2) (inlCfg M1 M2 c) t := by
  intro i hi hhalt hmove
  have hr := run_seq_inl M1 M2 c i (fun j hj => hno j (by omega))
  rw [hr] at hhalt hmove ⊢
  have hh := hno i hi
  have hm : (M1.δ (run M1 i c).st
      ((run M1 i c).tp.getD (run M1 i c).hd false)).2.2 = 0 := by
    simpa [seqMachine, inlCfg, hh] using hmove
  exact hsafe i hi hh hm

theorem seq_leftSafe_handoff (M1 M2 : Machine) (c : Cfg M1)
    (hh : M1.halt c.st = true) :
    LeftSafeRun (seqMachine M1 M2) (inlCfg M1 M2 c) 1 := by
  apply leftSafeRun_one_of_not_left
  simp [seqMachine, inlCfg, hh]

theorem seq_leftSafe_inr (M1 M2 : Machine) (c : Cfg M2)
    (t : Nat) (hsafe : LeftSafeRun M2 c t) :
    LeftSafeRun (seqMachine M1 M2) (inrCfg M1 M2 c) t := by
  intro i hi hhalt hmove
  rw [run_seq_inr M1 M2 c i] at hhalt hmove ⊢
  have hh : M2.halt (run M2 i c).st = false := by
    simpa [seqMachine, inrCfg] using hhalt
  have hm : (M2.δ (run M2 i c).st
      ((run M2 i c).tp.getD (run M2 i c).hd false)).2.2 = 0 := by
    simpa [seqMachine, inrCfg] using hmove
  exact hsafe i hi hh hm

/-- `seqMachine` preserves left-safety across its real reset-to-origin
handoff, including slack between the first halt and the advertised clock. -/
theorem seq_leftSafe (M1 M2 : Machine) (T0 T1 : List Bool)
    (t1 t2 p1 : Nat) (s1 : M1.State)
    (h1 : run M1 t1 (init M1 T0) = ⟨s1, p1, T1⟩)
    (hh1 : M1.halt s1 = true)
    (hsafe1 : LeftSafeRun M1 (init M1 T0) t1)
    (hsafe2 : LeftSafeRun M2 (init M2 T1) t2)
    (hh2 : M2.halt (run M2 t2 (init M2 T1)).st = true) :
    LeftSafeRun (seqMachine M1 M2)
      (init (seqMachine M1 M2) T0) (t1 + 1 + t2) := by
  have hex : ∃ t, M1.halt (run M1 t (init M1 T0)).st = true :=
    ⟨t1, by rw [h1]; exact hh1⟩
  let tm := Nat.find hex
  have htm := Nat.find_spec hex
  have htmle : tm ≤ t1 := Nat.find_le (by rw [h1]; exact hh1)
  have hfrozen : run M1 tm (init M1 T0) = ⟨s1, p1, T1⟩ := by
    rw [← run_stable M1 T0 htmle htm, h1]
  have hno : ∀ i < tm, M1.halt (run M1 i (init M1 T0)).st = false := by
    intro i hi
    simpa using Nat.find_min hex hi
  have hs1 : LeftSafeRun (seqMachine M1 M2)
      (init (seqMachine M1 M2) T0) tm := by
    change LeftSafeRun (seqMachine M1 M2)
      (inlCfg M1 M2 (init M1 T0)) tm
    exact seq_leftSafe_inl M1 M2 _ tm hno
      (fun i hi => hsafe1 i (by omega))
  have hr1 : run (seqMachine M1 M2) tm
      (init (seqMachine M1 M2) T0) =
      inlCfg M1 M2 (⟨s1, p1, T1⟩ : Cfg M1) := by
    change run (seqMachine M1 M2) tm (inlCfg M1 M2 (init M1 T0)) = _
    rw [run_seq_inl M1 M2 _ tm hno, hfrozen]
  have hsSwitch : LeftSafeRun (seqMachine M1 M2)
      (run (seqMachine M1 M2) tm (init (seqMachine M1 M2) T0)) 1 := by
    rw [hr1]
    exact seq_leftSafe_handoff M1 M2 _ hh1
  have hafter : run (seqMachine M1 M2) 1
      (run (seqMachine M1 M2) tm (init (seqMachine M1 M2) T0)) =
      inrCfg M1 M2 (init M2 T1) := by
    rw [hr1, run_succ, run_zero]
    exact step_seq_handoff M1 M2 _ hh1
  have hs2 : LeftSafeRun (seqMachine M1 M2)
      (run (seqMachine M1 M2) (tm + 1)
        (init (seqMachine M1 M2) T0)) t2 := by
    rw [run_add, hafter]
    exact seq_leftSafe_inr M1 M2 _ t2 hsafe2
  have hsMain := leftSafeRun_add (leftSafeRun_add hs1 hsSwitch) hs2
  have hhaltAt : (seqMachine M1 M2).halt
      (run (seqMachine M1 M2) (tm + 1 + t2)
        (init (seqMachine M1 M2) T0)).st = true := by
    rw [show tm + 1 + t2 = (tm + 1) + t2 by omega, run_add,
      run_add, hafter, run_seq_inr]
    simpa [seqMachine, inrCfg] using hh2
  have hsSlack : LeftSafeRun (seqMachine M1 M2)
      (run (seqMachine M1 M2) (tm + 1 + t2)
        (init (seqMachine M1 M2) T0)) (t1 - tm) :=
    leftSafeRun_of_halted _ hhaltAt
  have hsAll := leftSafeRun_add hsMain hsSlack
  convert hsAll using 1
  omega

/-- Safety packaging for either fixed-round branch. -/
theorem runtimeFixedRound_leftSafe_of_runs
    (T T' : List Bool) (cashClock dispatchClock pf : Nat)
    (sf : runtimeMarkedFrontOutputMachine.State)
    (hcash : run runtimeMarkedFrontOutputMachine cashClock
      (init runtimeMarkedFrontOutputMachine T) = ⟨sf, pf, T'⟩)
    (hhcash : runtimeMarkedFrontOutputMachine.halt sf = true)
    (hcashSafe : LeftSafeRun runtimeMarkedFrontOutputMachine
      (init runtimeMarkedFrontOutputMachine T) cashClock)
    (hdispatchSafe : LeftSafeRun runtimeContinuationDispatchMachine
      (init runtimeContinuationDispatchMachine T') dispatchClock)
    (hhdispatch : runtimeContinuationDispatchMachine.halt
      (run runtimeContinuationDispatchMachine dispatchClock
        (init runtimeContinuationDispatchMachine T')).st = true) :
    LeftSafeRun runtimeFixedRoundBody (init runtimeFixedRoundBody T)
      (cashClock + 1 + dispatchClock) := by
  simpa [runtimeFixedRoundBody] using
    seq_leftSafe runtimeMarkedFrontOutputMachine
      runtimeContinuationDispatchMachine T T' cashClock dispatchClock pf sf
      hcash hhcash hcashSafe hdispatchSafe hhdispatch

/-- One synchronized certificate for a complete nonterminal fixed round.
The endpoint equation, its halt proof, and left-safety all share the same
cashout and dispatcher witnesses, which is the exact interface required by
the recursive `runtimeRep_run` family. -/
theorem runtimeFixedRound_nonterminal_safeRun_of_runs
    (T T' T'' : List Bool) (cashClock dispatchClock pf rebaseHead : Nat)
    (sf : runtimeMarkedFrontOutputMachine.State)
    (rebaseState : runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine.State)
    (hcash : run runtimeMarkedFrontOutputMachine cashClock
      (init runtimeMarkedFrontOutputMachine T) = ⟨sf, pf, T'⟩)
    (hhcash : runtimeMarkedFrontOutputMachine.halt sf = true)
    (hcashSafe : LeftSafeRun runtimeMarkedFrontOutputMachine
      (init runtimeMarkedFrontOutputMachine T) cashClock)
    (hdispatch : run runtimeContinuationDispatchMachine dispatchClock
      (init runtimeContinuationDispatchMachine T') =
        ⟨Sum.inr (Sum.inl rebaseState), rebaseHead, T''⟩)
    (hhrebase : runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine.halt
      rebaseState = true)
    (hdispatchSafe : LeftSafeRun runtimeContinuationDispatchMachine
      (init runtimeContinuationDispatchMachine T') dispatchClock) :
    run runtimeFixedRoundBody (cashClock + 1 + dispatchClock)
        (init runtimeFixedRoundBody T) =
        ⟨Sum.inr (Sum.inr (Sum.inl rebaseState)), rebaseHead, T''⟩ ∧
      runtimeFixedRoundBody.halt
        (Sum.inr (Sum.inr (Sum.inl rebaseState))) = true ∧
      LeftSafeRun runtimeFixedRoundBody (init runtimeFixedRoundBody T)
        (cashClock + 1 + dispatchClock) := by
  have hrun := runtimeFixedRound_run_nonterminal_of_runs T T' T''
    cashClock dispatchClock pf rebaseHead sf rebaseState hcash hhcash
    hdispatch hhrebase
  have hhdispatch : runtimeContinuationDispatchMachine.halt
      (run runtimeContinuationDispatchMachine dispatchClock
        (init runtimeContinuationDispatchMachine T')).st = true := by
    rw [hdispatch]
    exact runtimeContinuationDispatch_halt_nonterminal rebaseState hhrebase
  refine ⟨hrun, ?_, ?_⟩
  · simpa [runtimeFixedRoundBody, seqMachine] using
      (runtimeContinuationDispatch_halt_nonterminal rebaseState hhrebase)
  · exact runtimeFixedRound_leftSafe_of_runs T T' cashClock dispatchClock
      pf sf hcash hhcash hcashSafe hdispatchSafe hhdispatch

/-- Terminal companion to `runtimeFixedRound_nonterminal_safeRun_of_runs`.
It presents the last scheduled round through the same synchronized
run/halt/safety interface, with the terminal dispatcher preserving `T'` and
returning to physical origin. -/
theorem runtimeFixedRound_terminal_safeRun_of_runs
    (T T' : List Bool) (cashClock dispatchClock pf : Nat)
    (sf : runtimeMarkedFrontOutputMachine.State)
    (hcash : run runtimeMarkedFrontOutputMachine cashClock
      (init runtimeMarkedFrontOutputMachine T) = ⟨sf, pf, T'⟩)
    (hhcash : runtimeMarkedFrontOutputMachine.halt sf = true)
    (hcashSafe : LeftSafeRun runtimeMarkedFrontOutputMachine
      (init runtimeMarkedFrontOutputMachine T) cashClock)
    (hdispatch : run runtimeContinuationDispatchMachine dispatchClock
      (init runtimeContinuationDispatchMachine T') =
        ⟨Sum.inr (Sum.inr ()), 0, T'⟩)
    (hdispatchSafe : LeftSafeRun runtimeContinuationDispatchMachine
      (init runtimeContinuationDispatchMachine T') dispatchClock) :
    run runtimeFixedRoundBody (cashClock + 1 + dispatchClock)
        (init runtimeFixedRoundBody T) =
        ⟨Sum.inr (Sum.inr (Sum.inr ())), 0, T'⟩ ∧
      runtimeFixedRoundBody.halt
        (Sum.inr (Sum.inr (Sum.inr ()))) = true ∧
      LeftSafeRun runtimeFixedRoundBody (init runtimeFixedRoundBody T)
        (cashClock + 1 + dispatchClock) := by
  have hrun := runtimeFixedRound_run_terminal_of_runs T T' cashClock
    dispatchClock pf sf hcash hhcash hdispatch
  have hhdispatch : runtimeContinuationDispatchMachine.halt
      (run runtimeContinuationDispatchMachine dispatchClock
        (init runtimeContinuationDispatchMachine T')).st = true := by
    rw [hdispatch]
    exact runtimeContinuationDispatch_halt_terminal
  refine ⟨hrun, ?_, ?_⟩
  · simpa [runtimeFixedRoundBody, seqMachine] using
      runtimeContinuationDispatch_halt_terminal
  · exact runtimeFixedRound_leftSafe_of_runs T T' cashClock dispatchClock
      pf sf hcash hhcash hcashSafe hdispatchSafe hhdispatch

/-- Constructor form of the synchronized nonterminal package, ready for the
indexed certificate family consumed by `runtimeRep_run_of_fixedRound_certificates`. -/
theorem runtimeFixedRoundCertificate_nonterminal_of_runs
    (T T' T'' : List Bool) (cashClock dispatchClock pf rebaseHead : Nat)
    (sf : runtimeMarkedFrontOutputMachine.State)
    (rebaseState : runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine.State)
    (hcash : run runtimeMarkedFrontOutputMachine cashClock
      (init runtimeMarkedFrontOutputMachine T) = ⟨sf, pf, T'⟩)
    (hhcash : runtimeMarkedFrontOutputMachine.halt sf = true)
    (hcashSafe : LeftSafeRun runtimeMarkedFrontOutputMachine
      (init runtimeMarkedFrontOutputMachine T) cashClock)
    (hdispatch : run runtimeContinuationDispatchMachine dispatchClock
      (init runtimeContinuationDispatchMachine T') =
        ⟨Sum.inr (Sum.inl rebaseState), rebaseHead, T''⟩)
    (hhrebase : runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine.halt
      rebaseState = true)
    (hdispatchSafe : LeftSafeRun runtimeContinuationDispatchMachine
      (init runtimeContinuationDispatchMachine T') dispatchClock) :
    RuntimeFixedRoundCertificate T T'' := by
  have h := runtimeFixedRound_nonterminal_safeRun_of_runs T T' T''
    cashClock dispatchClock pf rebaseHead sf rebaseState hcash hhcash
    hcashSafe hdispatch hhrebase hdispatchSafe
  exact ⟨cashClock + 1 + dispatchClock,
    Sum.inr (Sum.inr (Sum.inl rebaseState)), rebaseHead,
    h.1, h.2.1, h.2.2⟩

/-- Constructor form of the synchronized terminal package. -/
theorem runtimeFixedRoundCertificate_terminal_of_runs
    (T T' : List Bool) (cashClock dispatchClock pf : Nat)
    (sf : runtimeMarkedFrontOutputMachine.State)
    (hcash : run runtimeMarkedFrontOutputMachine cashClock
      (init runtimeMarkedFrontOutputMachine T) = ⟨sf, pf, T'⟩)
    (hhcash : runtimeMarkedFrontOutputMachine.halt sf = true)
    (hcashSafe : LeftSafeRun runtimeMarkedFrontOutputMachine
      (init runtimeMarkedFrontOutputMachine T) cashClock)
    (hdispatch : run runtimeContinuationDispatchMachine dispatchClock
      (init runtimeContinuationDispatchMachine T') =
        ⟨Sum.inr (Sum.inr ()), 0, T'⟩)
    (hdispatchSafe : LeftSafeRun runtimeContinuationDispatchMachine
      (init runtimeContinuationDispatchMachine T') dispatchClock) :
    RuntimeFixedRoundCertificate T T' := by
  have h := runtimeFixedRound_terminal_safeRun_of_runs T T' cashClock
    dispatchClock pf sf hcash hhcash hcashSafe hdispatch hdispatchSafe
  exact ⟨cashClock + 1 + dispatchClock,
    Sum.inr (Sum.inr (Sum.inr ())), 0, h.1, h.2.1, h.2.2⟩

/-- Concrete safety of the nonterminal continuation arm from the reachable
completed-lookup tape. -/
theorem runtimeContinuationDispatch_leftSafe_nonterminal
    (pairs : List (Bool × Bool)) (w : List Bool) (l : Lit)
    (first : List Bool) (more : List (List Bool))
    (hsafe : RuntimeNoDoubleSepFrom false pairs)
    (rebaseClock : Nat)
    (hrebaseSafe :
      let bits := literalLookupTape w l
      let rest := first :: more
      let d := (bits :: rest).length
      let sourcePre := flattenPairs (List.replicate d (true, true)) ++
        [false, true]
      let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
      let trailer := [true, false, false, true] ++
        List.replicate bits.length true ++ archiveTail
      let mcf := run masterM (literalLookupClock w l)
        (init masterM (bits ++ trailer))
      let markerPre := flattenPairs pairs ++ [false, true, false, true]
      LeftSafeRun runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine
        (init runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine
          (markerPre ++ sourcePre ++ mcf.tp)) rebaseClock)
    (hrebaseHalt :
      let bits := literalLookupTape w l
      let rest := first :: more
      let d := (bits :: rest).length
      let sourcePre := flattenPairs (List.replicate d (true, true)) ++
        [false, true]
      let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
      let trailer := [true, false, false, true] ++
        List.replicate bits.length true ++ archiveTail
      let mcf := run masterM (literalLookupClock w l)
        (init masterM (bits ++ trailer))
      let markerPre := flattenPairs pairs ++ [false, true, false, true]
      runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine.halt
        (run runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine rebaseClock
          (init runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine
            (markerPre ++ sourcePre ++ mcf.tp))).st = true) :
    let bits := literalLookupTape w l
    let rest := first :: more
    let d := (bits :: rest).length
    let sourcePre := flattenPairs (List.replicate d (true, true)) ++
      [false, true]
    let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ archiveTail
    let mcf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    let markerPre := flattenPairs pairs ++ [false, true, false, true]
    let T := markerPre ++ sourcePre ++ mcf.tp
    LeftSafeRun runtimeContinuationDispatchMachine
      (init runtimeContinuationDispatchMachine T)
      (runtimeMarkedContinuationClock pairs d l + 1 + rebaseClock) := by
  dsimp only
  let bits := literalLookupTape w l
  let rest := first :: more
  let d := (bits :: rest).length
  let sourcePre := flattenPairs (List.replicate d (true, true)) ++
    [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let markerPre := flattenPairs pairs ++ [false, true, false, true]
  let T := markerPre ++ sourcePre ++ mcf.tp
  have hloc0 := runtimeMarkedContinuation_run pairs w l rest hsafe
  have hloc : run runtimeMarkedContinuationMachine
      (runtimeMarkedContinuationClock pairs d l)
      (init runtimeMarkedContinuationMachine T) =
      ⟨Sum.inr (RuntimeContinuationLocatorState.done true),
        markerPre.length + (sourcePre.length + 2 * bits.length + 6), T⟩ := by
    simpa [bits, rest, d, sourcePre, archiveTail, trailer, mcf, markerPre, T]
      using hloc0
  have hsLoc := runtimeMarkedContinuation_leftSafe pairs w l rest hsafe
  have hs := condSeq_leftSafe_true runtimeMarkedContinuationMachine
    runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine runtimeTerminalHaltMachine
    T T (runtimeMarkedContinuationClock pairs d l) rebaseClock
    (markerPre.length + (sourcePre.length + 2 * bits.length + 6))
    (Sum.inr (RuntimeContinuationLocatorState.done true)) hloc rfl rfl
    (by simpa [bits, rest, d, sourcePre, archiveTail, trailer, mcf,
      markerPre, T] using hsLoc)
    (by simpa [bits, rest, d, sourcePre, archiveTail, trailer, mcf,
      markerPre, T] using hrebaseSafe)
    (by simpa [bits, rest, d, sourcePre, archiveTail, trailer, mcf,
      markerPre, T] using hrebaseHalt)
  simpa [runtimeContinuationDispatchMachine, bits, rest, d, sourcePre,
    archiveTail, trailer, mcf, markerPre, T] using hs
/-- Generic nonterminal adjacency for an arbitrary surviving aligned output
prefix.  Cashout, dispatcher selection, halt, and left-safety are assembled
around one marked physical rebase run/safety pair. -/
theorem runtimeMarked_nonterminalCertificate_of_rebase
    (B : Nat) (out residue : List Bool)
    (pairs pairs' : List (Bool × Bool))
    (w : List Bool) (l : Lit) (first : List Bool)
    (more : List (List Bool))
    (hout : out.length < B)
    (hpairs : outputCap B out ++ residue = flattenPairs pairs)
    (hsafe : RuntimeNoDoubleSepFrom false pairs)
    (hpairs' : outputCap B
        (out ++ [evalLit (fun k => w.getD k false) l]) ++ residue =
      flattenPairs pairs')
    (hsafe' : RuntimeNoDoubleSepFrom false pairs')
    (rebaseClock rebaseHead : Nat)
    (rebaseState : runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine.State)
    (rebaseTape : List Bool)
    (hrebase :
      let bits := literalLookupTape w l
      let rest := first :: more
      let d := (bits :: rest).length
      let sourcePre := flattenPairs (List.replicate d (true, true)) ++
        [false, true]
      let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
      let trailer := [true, false, false, true] ++
        List.replicate bits.length true ++ archiveTail
      let mcf := run masterM (literalLookupClock w l)
        (init masterM (bits ++ trailer))
      let Tcash := flattenPairs pairs' ++ [false, true, false, true] ++
        sourcePre ++ mcf.tp
      run runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine rebaseClock
          (init runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine Tcash) =
        ⟨rebaseState, rebaseHead, rebaseTape⟩)
    (hhrebase : runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine.halt
      rebaseState = true)
    (hrebaseSafe :
      let bits := literalLookupTape w l
      let rest := first :: more
      let d := (bits :: rest).length
      let sourcePre := flattenPairs (List.replicate d (true, true)) ++
        [false, true]
      let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
      let trailer := [true, false, false, true] ++
        List.replicate bits.length true ++ archiveTail
      let mcf := run masterM (literalLookupClock w l)
        (init masterM (bits ++ trailer))
      let Tcash := flattenPairs pairs' ++ [false, true, false, true] ++
        sourcePre ++ mcf.tp
      LeftSafeRun runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine
        (init runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine Tcash)
        rebaseClock) :
    let bits := literalLookupTape w l
    let rest := first :: more
    let d := (bits :: rest).length
    let T := outputCap B out ++ residue ++ [false, true, false, true] ++
      sourceSelectorInput d 0 (bits :: rest)
    RuntimeFixedRoundCertificate T rebaseTape := by
  dsimp only
  let bits := literalLookupTape w l
  let rest := first :: more
  let d := (bits :: rest).length
  let bv := evalLit (fun k => w.getD k false) l
  let sourcePre := flattenPairs (List.replicate d (true, true)) ++
    [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let T := outputCap B out ++ residue ++ [false, true, false, true] ++
    sourceSelectorInput d 0 (bits :: rest)
  let Tcash := flattenPairs pairs' ++ [false, true, false, true] ++
    sourcePre ++ mcf.tp
  obtain ⟨sf, pf, hcash0, hhcash⟩ :=
    runtimeMarkedFrontOutput_exact B out residue pairs w l rest
      hout hpairs hsafe
  have hTcash : outputCap B (out ++ [bv]) ++ residue ++
      [false, true, false, true] ++ sourcePre ++ mcf.tp = Tcash := by
    rw [hpairs']
  have hcash : run runtimeMarkedFrontOutputMachine
      (runtimeMarkedFrontOutputClock pairs d w l out)
      (init runtimeMarkedFrontOutputMachine T) = ⟨sf, pf, Tcash⟩ := by
    rw [← hTcash]
    simpa [bits, rest, d, bv, sourcePre, archiveTail, trailer, mcf,
      T, List.append_assoc] using hcash0
  have hcashSafe0 := runtimeMarkedFrontOutput_leftSafe
    B out residue pairs w l rest hout hpairs hsafe
  have hcashSafe : LeftSafeRun runtimeMarkedFrontOutputMachine
      (init runtimeMarkedFrontOutputMachine T)
      (runtimeMarkedFrontOutputClock pairs d w l out) := by
    simpa [bits, rest, d, T, List.append_assoc] using hcashSafe0
  have hdispatch := runtimeContinuationDispatch_run_nonterminal
    pairs' w l first more hsafe' rebaseClock rebaseHead rebaseState
      rebaseTape hrebase hhrebase
  have hrebaseHalt : runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine.halt
      (run runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine rebaseClock
        (init runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine Tcash)).st =
        true := by
    rw [hrebase]
    exact hhrebase
  have hdispatchSafe := runtimeContinuationDispatch_leftSafe_nonterminal
    pairs' w l first more hsafe' rebaseClock hrebaseSafe hrebaseHalt
  apply runtimeFixedRoundCertificate_nonterminal_of_runs T Tcash rebaseTape
    (runtimeMarkedFrontOutputClock pairs d w l out)
    (runtimeMarkedContinuationClock pairs' d l + 1 + rebaseClock)
    pf rebaseHead sf rebaseState
  · exact hcash
  · exact hhcash
  · exact hcashSafe
  · exact hdispatch
  · exact hhrebase
  · exact hdispatchSafe

set_option maxHeartbeats 4000000 in
/-- Unconditional generic nonterminal adjacency.  Once the physical output
prefix has safe aligned pair decompositions before and after the singleton
cashout, the corrected marked controller supplies its own rebase clock,
endpoint, halt, and safety witnesses. -/
theorem runtimeMarked_nonterminalCertificate
    (B : Nat) (out residue : List Bool)
    (pairs pairs' : List (Bool × Bool))
    (w : List Bool) (l : Lit) (first : List Bool)
    (more : List (List Bool))
    (hout : out.length < B)
    (hpairs : outputCap B out ++ residue = flattenPairs pairs)
    (hsafe : RuntimeNoDoubleSepFrom false pairs)
    (hpairs' : outputCap B
        (out ++ [evalLit (fun k => w.getD k false) l]) ++ residue =
      flattenPairs pairs')
    (hsafe' : RuntimeNoDoubleSepFrom false pairs') :
    let bits := literalLookupTape w l
    let rest := first :: more
    let d := (bits :: rest).length
    let T := outputCap B out ++ residue ++ [false, true, false, true] ++
      sourceSelectorInput d 0 (bits :: rest)
    ∃ nextTape, RuntimeFixedRoundCertificate T nextTape := by
  dsimp only
  let bits := literalLookupTape w l
  let rest := first :: more
  let d := (bits :: rest).length
  let markerPre := flattenPairs pairs' ++ [false, true, false, true]
  let sourcePre := flattenPairs (List.replicate d (true, true)) ++
    [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let Tcash := markerPre ++ sourcePre ++ mcf.tp
  let markerClock := 2 * pairs'.length + 7
  let workspaceClock := sourcePre.length + 2
  let tailClock := 8 * l.1 + 22
  let locateClock := markerClock + 1 +
    (workspaceClock + 1 + tailClock)
  let seedClock := runtimeArchiveReturnSeedClock rest
  let prefixClock := locateClock + 1 + seedClock
  let R := markerPre.length + sourcePre.length + 2 * bits.length + 4
  obtain ⟨base, unaryClock, hrun, hleft⟩ :=
    runtimeMarkedPhysicalUnaryRebase_complete
      pairs' w l first more hsafe'
  let nextTape := base ++ [false, true, false, true] ++
    sourceSelectorInput rest.length 0 rest
  have hrun' : run runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine
      (prefixClock + 1 + unaryClock)
      (init runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine Tcash) =
      ⟨Sum.inr RuntimeUnaryRebaseState.done,
        R + (selectedTail rest).length, nextTape⟩ := by
    simpa [bits, rest, d, markerPre, sourcePre, archiveTail, trailer,
      mcf, Tcash, markerClock, workspaceClock, tailClock, locateClock,
      seedClock, prefixClock, R, nextTape] using hrun
  have hleft' : LeftSafeRun
      runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine
      (init runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine Tcash)
      (prefixClock + 1 + unaryClock) := by
    simpa [bits, rest, d, markerPre, sourcePre, archiveTail, trailer,
      mcf, Tcash, markerClock, workspaceClock, tailClock, locateClock,
      seedClock, prefixClock, R] using hleft
  refine ⟨nextTape, runtimeMarked_nonterminalCertificate_of_rebase
    B out residue pairs pairs' w l first more hout hpairs hsafe hpairs'
    hsafe' (prefixClock + 1 + unaryClock)
    (R + (selectedTail rest).length)
    (Sum.inr RuntimeUnaryRebaseState.done) nextTape ?_ rfl ?_⟩
  · dsimp only
    exact hrun'
  · dsimp only
    exact hleft'

/-- The complete first fixed-round adjacency, with the sole remaining native
premise being the physical rebaser's exact run/safety pair on the marked
cashout endpoint. -/
theorem runtimeRoundZero_nonterminalCertificate_of_rebase
    (w : List Bool) (l : Lit) (first : List Bool)
    (more : List (List Bool))
    (rebaseClock rebaseHead : Nat)
    (rebaseState : runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine.State)
    (rebaseTape : List Bool)
    (hrebase :
      let bits := literalLookupTape w l
      let rest := first :: more
      let B := (bits :: rest).length
      let bv := evalLit (fun k => w.getD k false) l
      let sourcePre := flattenPairs
        (List.replicate (bits :: rest).length (true, true)) ++ [false, true]
      let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
      let trailer := [true, false, false, true] ++
        List.replicate bits.length true ++ archiveTail
      let mcf := run masterM (literalLookupClock w l)
        (init masterM (bits ++ trailer))
      let Tcash := outputCap B [bv] ++ [false, true, false, true] ++
        sourcePre ++ mcf.tp
      run runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine rebaseClock
          (init runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine Tcash) =
        ⟨rebaseState, rebaseHead, rebaseTape⟩)
    (hhrebase : runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine.halt
      rebaseState = true)
    (hrebaseSafe :
      let bits := literalLookupTape w l
      let rest := first :: more
      let B := (bits :: rest).length
      let bv := evalLit (fun k => w.getD k false) l
      let sourcePre := flattenPairs
        (List.replicate (bits :: rest).length (true, true)) ++ [false, true]
      let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
      let trailer := [true, false, false, true] ++
        List.replicate bits.length true ++ archiveTail
      let mcf := run masterM (literalLookupClock w l)
        (init masterM (bits ++ trailer))
      let Tcash := outputCap B [bv] ++ [false, true, false, true] ++
        sourcePre ++ mcf.tp
      LeftSafeRun runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine
        (init runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine Tcash)
        rebaseClock) :
    let bits := literalLookupTape w l
    let rest := first :: more
    let B := (bits :: rest).length
    RuntimeFixedRoundCertificate
      (runtimeRoundZeroTape B (bits :: rest)) rebaseTape := by
  dsimp only
  let bits := literalLookupTape w l
  let rest := first :: more
  let B := (bits :: rest).length
  let bv := evalLit (fun k => w.getD k false) l
  let pairs0 := runtimeOutputCapPairs B []
  let pairs1 := runtimeOutputCapPairs B [bv]
  let sourcePre := flattenPairs (List.replicate B (true, true)) ++
    [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let Tcash := outputCap B [bv] ++ [false, true, false, true] ++
    sourcePre ++ mcf.tp
  obtain ⟨sf, pf, hcash, hhcash, hcashSafe⟩ :=
    runtimeRoundZero_cashout_safeRun w l rest
  have hout1 : [bv].length < B := by simp [B, rest]
  have hpairs1 : outputCap B [bv] = flattenPairs pairs1 := by
    simpa [pairs1] using (runtimeOutputCapPairs_flatten B [bv]).symm
  have hTcash : Tcash = flattenPairs pairs1 ++
      [false, true, false, true] ++ sourcePre ++ mcf.tp := by
    simp [Tcash, hpairs1, List.append_assoc]
  have hsafe1 : RuntimeNoDoubleSepFrom false pairs1 :=
    (runtimeOutputCapPairs_safe B [bv] hout1).1
  have hdispatch := runtimeContinuationDispatch_run_nonterminal
    pairs1 w l first more hsafe1 rebaseClock rebaseHead rebaseState
    rebaseTape
    (by dsimp only; rw [← hTcash]; exact hrebase)
    hhrebase
  have hrebaseHalt : runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine.halt
      (run runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine rebaseClock
        (init runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine Tcash)).st =
        true := by
    rw [hrebase]
    exact hhrebase
  have hdispatchSafe := runtimeContinuationDispatch_leftSafe_nonterminal
    pairs1 w l first more hsafe1 rebaseClock
    (by dsimp only; rw [← hTcash]; exact hrebaseSafe)
    (by dsimp only; rw [← hTcash]; exact hrebaseHalt)
  have hdispatch' : run runtimeContinuationDispatchMachine
      (runtimeMarkedContinuationClock pairs1 B l + 1 + rebaseClock)
      (init runtimeContinuationDispatchMachine Tcash) =
        ⟨Sum.inr (Sum.inl rebaseState), rebaseHead, rebaseTape⟩ := by
    rw [hTcash]
    exact hdispatch
  have hdispatchSafe' : LeftSafeRun runtimeContinuationDispatchMachine
      (init runtimeContinuationDispatchMachine Tcash)
      (runtimeMarkedContinuationClock pairs1 B l + 1 + rebaseClock) := by
    rw [hTcash]
    exact hdispatchSafe
  apply runtimeFixedRoundCertificate_nonterminal_of_runs
    (runtimeRoundZeroTape B (bits :: rest)) Tcash rebaseTape
    (runtimeMarkedFrontOutputClock pairs0 B w l [])
    (runtimeMarkedContinuationClock pairs1 B l + 1 + rebaseClock)
    pf rebaseHead sf rebaseState
  · simpa [bits, rest, B, bv, pairs0, sourcePre, archiveTail,
      trailer, mcf, Tcash] using hcash
  · exact hhcash
  · simpa [bits, rest, B, pairs0] using hcashSafe
  · exact hdispatch'
  · exact hhrebase
  · exact hdispatchSafe'

set_option maxHeartbeats 4000000 in
/-- Unconditional certified first adjacency: the corrected marked physical
controller supplies the dispatcher premise internally. -/
theorem runtimeRoundZero_nonterminalCertificate
    (w : List Bool) (l : Lit) (first : List Bool)
    (more : List (List Bool)) :
    let bits := literalLookupTape w l
    let rest := first :: more
    let B := (bits :: rest).length
    ∃ nextTape,
      RuntimeFixedRoundCertificate
        (runtimeRoundZeroTape B (bits :: rest)) nextTape := by
  dsimp only
  let bits := literalLookupTape w l
  let rest := first :: more
  let B := (bits :: rest).length
  let bv := evalLit (fun k => w.getD k false) l
  let pairs := runtimeOutputCapPairs B [bv]
  let markerPre := flattenPairs pairs ++ [false, true, false, true]
  let sourcePre := flattenPairs (List.replicate B (true, true)) ++
    [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let Tmarked := markerPre ++ sourcePre ++ mcf.tp
  let markerClock := 2 * pairs.length + 7
  let workspaceClock := sourcePre.length + 2
  let tailClock := 8 * l.1 + 22
  let locateClock := markerClock + 1 +
    (workspaceClock + 1 + tailClock)
  let seedClock := runtimeArchiveReturnSeedClock rest
  let prefixClock := locateClock + 1 + seedClock
  let R := 4 * B + 2 * bits.length + 12
  obtain ⟨base, unaryClock, hrun, hsafe⟩ :=
    runtimeRoundZero_markedPhysicalUnaryRebase_safeRun w l first more
  let nextTape := base ++ [false, true, false, true] ++
    sourceSelectorInput rest.length 0 rest
  have hcap : flattenPairs pairs = outputCap B [bv] := by
    simpa [pairs] using runtimeOutputCapPairs_flatten B [bv]
  have hTmarked : Tmarked = outputCap B [bv] ++
      [false, true, false, true] ++ sourcePre ++ mcf.tp := by
    simp [Tmarked, markerPre, hcap, List.append_assoc]
  have hrun' : run runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine
      (prefixClock + 1 + unaryClock)
      (init runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine Tmarked) =
      ⟨Sum.inr RuntimeUnaryRebaseState.done,
        R + (selectedTail rest).length, nextTape⟩ := by
    simpa [bits, rest, B, bv, pairs, markerPre, sourcePre, archiveTail,
      trailer, mcf, Tmarked, markerClock, workspaceClock, tailClock,
      locateClock, seedClock, prefixClock, R, nextTape] using hrun
  have hsafe' : LeftSafeRun
      runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine
      (init runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine Tmarked)
      (prefixClock + 1 + unaryClock) := by
    simpa [bits, rest, B, bv, pairs, markerPre, sourcePre, archiveTail,
      trailer, mcf, Tmarked, markerClock, workspaceClock, tailClock,
      locateClock, seedClock, prefixClock] using hsafe
  refine ⟨nextTape, runtimeRoundZero_nonterminalCertificate_of_rebase
    w l first more (prefixClock + 1 + unaryClock)
    (R + (selectedTail rest).length)
    (Sum.inr RuntimeUnaryRebaseState.done) nextTape ?_ rfl ?_⟩
  · dsimp only
    rw [← hTmarked]
    exact hrun'
  · dsimp only
    rw [← hTmarked]
    exact hsafe'

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
      (outputCap B out' ++ residue).IsPrefix rcf.tp ∧
      (outputCap B out' ++ residue).length =
        (R - 2) - (2 * rest.length + 4) ∧
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
  refine ⟨residue, unaryClock, pairs, hpref, hlen, hpairs', hsafe, ?_, ?_⟩
  · simpa [B, schedule, preBlocks, l, bits, rest, pre, out, out', T,
      lookupClock, M, routeClock, rcf, locateClock, tailClock,
      prefixClock, seedClock, R, hpairs'] using hrun
  · simpa [B, schedule, preBlocks, l, bits, rest, pre, out, out', T,
      lookupClock, M, routeClock, rcf, locateClock, tailClock,
      prefixClock, seedClock, R] using hleft

/-- Canonical form of the scheduled surviving prefix.  The next-round
prefix is the uniquely determined `take` of the routed tape at the certified
physical cut, rather than an independently chosen residue witness. -/
theorem scheduled_physicalUnaryRebase_canonicalSafeRun
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
    let cut := (R - 2) - (2 * rest.length + 4)
    ∃ residue unaryClock pairs,
      rcf.tp.take cut = outputCap B out' ++ residue ∧
      rcf.tp.take cut = flattenPairs pairs ∧
      RuntimeNoDoubleSepFrom false pairs ∧
      run outputWorkspaceArchiveReturnUnaryRebaseMachine
          ((prefixClock + 1 + seedClock) + 1 + unaryClock)
          (init outputWorkspaceArchiveReturnUnaryRebaseMachine rcf.tp) =
        ⟨outputWorkspaceArchiveReturnUnaryRebaseDone,
          R + (selectedTail rest).length,
          rcf.tp.take cut ++ [false, true, false, true] ++
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
  let cut := (R - 2) - (2 * rest.length + 4)
  obtain ⟨residue, unaryClock, pairs, hpref, hlen, hpairs, hsafe,
      hrun, hleft⟩ := scheduled_physicalUnaryRebase_pairSafeRun x w ht htnext
  have hcanon : outputCap B out' ++ residue = rcf.tp.take cut := by
    rw [List.prefix_iff_eq_take] at hpref
    calc
      outputCap B out' ++ residue =
          rcf.tp.take (outputCap B out' ++ residue).length := hpref
      _ = rcf.tp.take cut := by rw [hlen]
  refine ⟨residue, unaryClock, pairs, hcanon.symm, ?_, hsafe, ?_, ?_⟩
  · rw [← hpairs, hcanon]
  · simpa [B, schedule, preBlocks, l, bits, rest, pre, out, out', T,
      lookupClock, M, routeClock, rcf, locateClock, tailClock,
      prefixClock, seedClock, R, cut, ← hpairs, hcanon] using hrun
  · simpa [B, schedule, preBlocks, l, bits, rest, pre, out, out', T,
      lookupClock, M, routeClock, rcf, locateClock, tailClock,
      prefixClock, seedClock, R, cut] using hleft

/-! ## Canonical scheduled marked entries -/

/-- The physical cut produced at scheduled index `t` is the unique aligned,
separator-safe prefix for the marked entry at `t + 1`.  This packages the
successor representation independently of the obsolete unmarked controller
state type: only the canonical routed-tape `take` is retained. -/
theorem scheduled_nextMarkedEntry_pairSafe
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
    let R := 2 * B + 2 + pre.length + 2 * bits.length + 4
    let cut := (R - 2) - (2 * rest.length + 4)
    let physPrefix := rcf.tp.take cut
    let nextEntry := physPrefix ++ [false, true, false, true] ++
      sourceSelectorInput rest.length 0 rest
    ∃ residue pairs,
      physPrefix = outputCap B out' ++ residue ∧
      physPrefix = flattenPairs pairs ∧
      RuntimeNoDoubleSepFrom false pairs ∧
      nextEntry = flattenPairs pairs ++ [false, true, false, true] ++
        sourceSelectorInput rest.length 0 rest := by
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
  let R := 2 * B + 2 + pre.length + 2 * bits.length + 4
  let cut := (R - 2) - (2 * rest.length + 4)
  let physPrefix := rcf.tp.take cut
  let nextEntry := physPrefix ++ [false, true, false, true] ++
    sourceSelectorInput rest.length 0 rest
  obtain ⟨residue, unaryClock, pairs, hprefix, hpairs, hsafe,
      hrun, hleft⟩ :=
    scheduled_physicalUnaryRebase_canonicalSafeRun x w ht htnext
  refine ⟨residue, pairs, ?_, ?_, hsafe, ?_⟩
  · simpa [B, schedule, preBlocks, l, bits, rest, pre, out, out', T,
      lookupClock, M, routeClock, rcf, R, cut, physPrefix] using hprefix
  · simpa [B, schedule, preBlocks, l, bits, rest, pre, out, out', T,
      lookupClock, M, routeClock, rcf, R, cut, physPrefix] using hpairs
  · have h := congrArg (fun z => z ++ [false, true, false, true] ++
        sourceSelectorInput rest.length 0 rest) hpairs
    simpa [B, schedule, preBlocks, l, bits, rest, pre, out, out', T,
      lookupClock, M, routeClock, rcf, R, cut, physPrefix, nextEntry]
      using h

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.scheduled_physicalUnaryRebase_pairSafeRun
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.scheduled_physicalUnaryRebase_canonicalSafeRun
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.scheduled_nextMarkedEntry_pairSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeFixedRound_family_of_certificates
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeRep_run_of_fixedRound_certificates
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeRep_run_of_fixedRound_chain
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeRoundZeroTape_pairSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeMarkerConsume_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeMarkerConsume_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeConsumingRoundEntryLocator_safeRun
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeConsumingMarkedWorkspaceTailLocator_safeRun
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeRoundZero_cashout_safeRun
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeRoundZero_markedCashout_futureArchive
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeRoundZero_markedCashout_archiveReturnSeed_safeRun
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeRoundZero_markedWorkspaceTailLocate
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeMarkedWorkspaceTailLocator_safeRun
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeMarkedPhysicalUnaryRebase_safeRun
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeMarkedPhysicalUnaryRebase_complete
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeRoundZero_markedWorkspaceTailLocate_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeRoundZero_markedWorkspaceArchiveReturnSeed_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeRoundZero_markedWorkspaceArchiveReturnSeed_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeRoundZero_markedPhysicalUnaryRebase_safeRun
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeMarked_nonterminalCertificate_of_rebase
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeMarked_nonterminalCertificate
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeRoundZero_nonterminalCertificate_of_rebase
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeRoundZero_nonterminalCertificate
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.selectedPrefix_succ
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.scheduled_selectedPrefix_succ
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeMarkedFrontOutput_exact
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeMarkedFrontLookup_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeMarkedFrontOutput_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeFixedRound_run_terminal_of_runs
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeFixedRound_run_nonterminal_of_runs
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeFixedRound_leftSafe_of_runs
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeFixedRound_nonterminal_safeRun_of_runs
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeFixedRound_terminal_safeRun_of_runs
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeFixedRoundCertificate_nonterminal_of_runs
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeFixedRoundCertificate_terminal_of_runs
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeContinuationDispatch_leftSafe_nonterminal
