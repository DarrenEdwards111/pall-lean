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
    (rebaseState : outputWorkspaceArchiveReturnUnaryRebaseMachine.State)
    (hcash : run runtimeMarkedFrontOutputMachine cashClock
      (init runtimeMarkedFrontOutputMachine T) = ⟨sf, pf, T'⟩)
    (hhcash : runtimeMarkedFrontOutputMachine.halt sf = true)
    (hdispatch : run runtimeContinuationDispatchMachine dispatchClock
      (init runtimeContinuationDispatchMachine T') =
        ⟨Sum.inr (Sum.inl rebaseState), rebaseHead, T''⟩)
    (hhrebase : outputWorkspaceArchiveReturnUnaryRebaseMachine.halt
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
    (rebaseState : outputWorkspaceArchiveReturnUnaryRebaseMachine.State)
    (hcash : run runtimeMarkedFrontOutputMachine cashClock
      (init runtimeMarkedFrontOutputMachine T) = ⟨sf, pf, T'⟩)
    (hhcash : runtimeMarkedFrontOutputMachine.halt sf = true)
    (hcashSafe : LeftSafeRun runtimeMarkedFrontOutputMachine
      (init runtimeMarkedFrontOutputMachine T) cashClock)
    (hdispatch : run runtimeContinuationDispatchMachine dispatchClock
      (init runtimeContinuationDispatchMachine T') =
        ⟨Sum.inr (Sum.inl rebaseState), rebaseHead, T''⟩)
    (hhrebase : outputWorkspaceArchiveReturnUnaryRebaseMachine.halt
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
    (rebaseState : outputWorkspaceArchiveReturnUnaryRebaseMachine.State)
    (hcash : run runtimeMarkedFrontOutputMachine cashClock
      (init runtimeMarkedFrontOutputMachine T) = ⟨sf, pf, T'⟩)
    (hhcash : runtimeMarkedFrontOutputMachine.halt sf = true)
    (hcashSafe : LeftSafeRun runtimeMarkedFrontOutputMachine
      (init runtimeMarkedFrontOutputMachine T) cashClock)
    (hdispatch : run runtimeContinuationDispatchMachine dispatchClock
      (init runtimeContinuationDispatchMachine T') =
        ⟨Sum.inr (Sum.inl rebaseState), rebaseHead, T''⟩)
    (hhrebase : outputWorkspaceArchiveReturnUnaryRebaseMachine.halt
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
      LeftSafeRun outputWorkspaceArchiveReturnUnaryRebaseMachine
        (init outputWorkspaceArchiveReturnUnaryRebaseMachine
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
      outputWorkspaceArchiveReturnUnaryRebaseMachine.halt
        (run outputWorkspaceArchiveReturnUnaryRebaseMachine rebaseClock
          (init outputWorkspaceArchiveReturnUnaryRebaseMachine
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
    outputWorkspaceArchiveReturnUnaryRebaseMachine runtimeTerminalHaltMachine
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

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.scheduled_physicalUnaryRebase_pairSafeRun
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.scheduled_physicalUnaryRebase_canonicalSafeRun
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeFixedRound_family_of_certificates
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeRep_run_of_fixedRound_certificates
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeRep_run_of_fixedRound_chain
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeRoundZeroTape_pairSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeRoundZero_cashout_safeRun
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
