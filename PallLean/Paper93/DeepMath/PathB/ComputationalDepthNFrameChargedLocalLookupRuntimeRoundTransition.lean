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
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeMarkedFrontLookup_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeMarkedFrontOutput_leftSafe
