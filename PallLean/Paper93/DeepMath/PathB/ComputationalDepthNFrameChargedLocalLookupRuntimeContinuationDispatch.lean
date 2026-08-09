import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCondSeqMachine
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeContinuationLocator
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimePhysicalUnaryRebase
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeLeftSafety

/-!
# Charged local lookup: tape-driven continuation dispatch

The continuation locator exposes the presence of a future archive in its
accept bit.  This file consumes that bit with the verified conditional
sequencer.  The true arm is the fixed physical archive-return/unary-rebase
controller; the false arm is a genuinely terminal zero-step machine.

The handoff is therefore operational: both arms begin after the conditional
sequencer's real reset-to-origin transition, and no semantic branch choice or
head reposition appears in the machine definition.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeContinuationDispatch

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CondSeqMachine
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceTailLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeUnaryRebaseWriter
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeMarkedEntry
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeContinuationLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalUnaryRebase
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeLeftSafety

set_option maxHeartbeats 1000000

/-- A zero-step terminal arm.  It preserves the routed final tape exactly. -/
def runtimeTerminalHaltMachine : Machine where
  State := Unit
  fin := inferInstance
  dec := inferInstance
  start := ()
  halt := fun _ => true
  δ := fun _ _ => ((), none, 2)
  accept := fun _ => true

/-- Tape-driven post-cashout branch: future archive means physical rebase;
terminal blank means immediate final halt. -/
inductive RuntimeMarkerConsumeState
  | boot | cell3 | cell2 | cell1 | cell0
  | return1 | return2 | return3 | done
  deriving DecidableEq, Fintype

def runtimeMarkerConsumeMachine : Machine where
  State := RuntimeMarkerConsumeState
  fin := inferInstance
  dec := inferInstance
  start := .boot
  halt := fun s => decide (s = .done)
  δ := fun s _ =>
    match s with
    | .boot => (.cell3, none, 0)
    | .cell3 => (.cell2, some false, 0)
    | .cell2 => (.cell1, some false, 0)
    | .cell1 => (.cell0, some false, 0)
    | .cell0 => (.return1, some false, 1)
    | .return1 => (.return2, none, 1)
    | .return2 => (.return3, none, 1)
    | .return3 => (.done, none, 1)
    | .done => (.done, none, 2)
  accept := fun _ => false

/-- Local primitive for the marked-to-compact shifter.  Starting on a
two-cell `00` hole followed by one arbitrary pair, it bubbles the hole one
pair to the right while retaining the pair in finite control. -/
inductive RuntimeCompactBubbleState
  | holeLo | holeHi | readLo | readHi (lo : Bool)
  | clearLo (lo hi : Bool) | writeHi (lo hi : Bool)
  | writeLo (lo : Bool) | done
  deriving DecidableEq, Fintype

def runtimeCompactBubbleMachine : Machine where
  State := RuntimeCompactBubbleState
  fin := inferInstance
  dec := inferInstance
  start := .holeLo
  halt := fun s => decide (s = .done)
  δ := fun s b =>
    match s with
    | .holeLo => (.holeHi, none, 1)
    | .holeHi => (.readLo, none, 1)
    | .readLo => (.readHi b, none, 1)
    | .readHi lo => (.clearLo lo b, some false, 0)
    | .clearLo lo hi => (.writeHi lo hi, some false, 0)
    | .writeHi lo hi => (.writeLo lo, some hi, 0)
    | .writeLo lo => (.done, some lo, 2)
    | .done => (.done, none, 2)
  accept := fun _ => false

def runtimeConsumingRoundEntryLocatorMachine : Machine :=
  headSeqMachine runtimeRoundEntryLocatorMachine runtimeMarkerConsumeMachine

def runtimeMarkedWorkspaceTailLocatorMachine : Machine :=
  headSeqMachine runtimeRoundEntryLocatorMachine
    (headSeqMachine runtimeWorkspaceLocatorMachine
      runtimeWorkspaceTailLocatorMachine)

/-- Corrected locator path used by the recursive controller: locate and
consume the old routing marker before traversing the workspace/archive tail. -/
def runtimeConsumingMarkedWorkspaceTailLocatorMachine : Machine :=
  headSeqMachine runtimeConsumingRoundEntryLocatorMachine
    (headSeqMachine runtimeWorkspaceLocatorMachine
      runtimeWorkspaceTailLocatorMachine)

def runtimeConsumingMarkedWorkspaceArchiveReturnSeedMachine : Machine :=
  headSeqMachine runtimeConsumingMarkedWorkspaceTailLocatorMachine
    runtimeArchiveReturnSeedMachine

def runtimeConsumingMarkedWorkspaceArchiveReturnUnaryRebaseMachine : Machine :=
  headSeqMachine runtimeConsumingMarkedWorkspaceArchiveReturnSeedMachine
    runtimeUnaryRebaseMachine

def runtimeMarkedWorkspaceArchiveReturnSeedMachine : Machine :=
  headSeqMachine runtimeMarkedWorkspaceTailLocatorMachine
    runtimeArchiveReturnSeedMachine

def runtimeMarkedWorkspaceArchiveReturnUnaryRebaseMachine : Machine :=
  headSeqMachine runtimeMarkedWorkspaceArchiveReturnSeedMachine
    runtimeUnaryRebaseMachine

def runtimeContinuationDispatchMachine : Machine :=
  condSeqMachine runtimeMarkedContinuationMachine
    runtimeConsumingMarkedWorkspaceArchiveReturnUnaryRebaseMachine
    runtimeTerminalHaltMachine

/-! ## Concrete marked-classifier left safety -/

/-- The sole left-moving locator transition leaves `markerHi`; that state can
only be entered by a preceding right move from `markerLo`. -/
def RuntimeRoundEntrySafeInv (c : Cfg runtimeRoundEntryLocatorMachine) : Prop :=
  ∀ b, c.st = RuntimeRoundEntryState.markerHi b → 0 < c.hd

theorem runtimeRoundEntrySafeInv_step
    (c : Cfg runtimeRoundEntryLocatorMachine)
    (h : RuntimeRoundEntrySafeInv c) :
    RuntimeRoundEntrySafeInv (step runtimeRoundEntryLocatorMachine c) := by
  intro b hb
  by_cases hh : runtimeRoundEntryLocatorMachine.halt c.st = true
  · rw [step_of_halted _ hh] at hb ⊢
    exact h b hb
  · have hh' : runtimeRoundEntryLocatorMachine.halt c.st = false := by
      simpa using hh
    simp only [step, hh', Bool.false_eq_true, if_false] at hb ⊢
    cases hs : c.st <;>
      simp [runtimeRoundEntryLocatorMachine, moveHead, hs] at hb ⊢ <;>
      split_ifs at hb <;> simp_all

theorem runtimeRoundEntrySafeInv_run
    (c : Cfg runtimeRoundEntryLocatorMachine)
    (h : RuntimeRoundEntrySafeInv c) (n : Nat) :
    RuntimeRoundEntrySafeInv (run runtimeRoundEntryLocatorMachine n c) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      rw [run_succ]
      exact runtimeRoundEntrySafeInv_step _ ih

/-- The robust marker locator is left-safe from every ordinary locator start,
independently of the scanned tape and clock. -/
theorem runtimeRoundEntryLocator_leftSafe (T : List Bool) (n : Nat) :
    LeftSafeRun runtimeRoundEntryLocatorMachine
      (init runtimeRoundEntryLocatorMachine T) n := by
  have hinv0 : RuntimeRoundEntrySafeInv
      (init runtimeRoundEntryLocatorMachine T) := by
    intro b hb
    simp [runtimeRoundEntryLocatorMachine, init] at hb
  intro i hi _ hmove
  have hinv := runtimeRoundEntrySafeInv_run
    (init runtimeRoundEntryLocatorMachine T) hinv0 i
  let c := run runtimeRoundEntryLocatorMachine i
    (init runtimeRoundEntryLocatorMachine T)
  change (runtimeRoundEntryLocatorMachine.δ c.st
    (c.tp.getD c.hd false)).2.2 = 0 at hmove
  change 0 < c.hd
  cases hs : c.st with
  | lo previous =>
      rw [hs] at hmove
      simp [runtimeRoundEntryLocatorMachine] at hmove
  | hi previous loBit =>
      rw [hs] at hmove
      simp [runtimeRoundEntryLocatorMachine] at hmove
      split_ifs at hmove <;> simp_all
  | markerLo =>
      rw [hs] at hmove
      simp [runtimeRoundEntryLocatorMachine] at hmove
  | markerHi loBit => exact hinv loBit hs
  | markerBack =>
      rw [hs] at hmove
      simp [runtimeRoundEntryLocatorMachine] at hmove
  | done =>
      rw [hs] at hmove
      simp [runtimeRoundEntryLocatorMachine] at hmove

/-- The complete robust marker scan followed by the exact continuation
classifier is left-safe on every reachable completed lookup tape. -/
theorem runtimeMarkedContinuation_leftSafe
    (pairs : List (Bool × Bool)) (w : List Bool) (l : Lit)
    (rest : List (List Bool))
    (hsafe : RuntimeNoDoubleSepFrom false pairs) :
    let bits := literalLookupTape w l
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
    LeftSafeRun runtimeMarkedContinuationMachine
      (init runtimeMarkedContinuationMachine T)
      (runtimeMarkedContinuationClock pairs d l) := by
  dsimp only
  let bits := literalLookupTape w l
  let d := (bits :: rest).length
  let sourcePre := flattenPairs (List.replicate d (true, true)) ++
    [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let markerPre := flattenPairs pairs ++ [false, true, false, true]
  let tail := sourcePre ++ mcf.tp
  let T := markerPre ++ tail
  let locatorClock := 2 * pairs.length + 7
  let bodyClock := runtimeContinuationLocatorClock d l
  let z := decide (rest ≠ [])
  have htail : tail = true :: true :: tail.drop 2 := by
    simp [tail, sourcePre, d, List.replicate_succ, flattenPairs,
      List.append_assoc]
  have hloc0 := runtimeRoundEntryLocator_run pairs tail true true
    hsafe htail (by simp [runtimePairIsSep])
  have hloc : run runtimeRoundEntryLocatorMachine locatorClock
      (init runtimeRoundEntryLocatorMachine T) =
      ⟨RuntimeRoundEntryState.done, markerPre.length, T⟩ := by
    simpa [locatorClock, T, markerPre, tail, flattenPairs,
      flattenPairs_length, List.append_assoc] using hloc0
  have hbody0 := masterM_literal_continuationLocate w l rest
  have hbody : run runtimeContinuationLocatorMachine bodyClock
      (init runtimeContinuationLocatorMachine tail) =
      ⟨RuntimeContinuationLocatorState.done z,
        sourcePre.length + 2 * bits.length + 6, tail⟩ := by
    simpa [bodyClock, bits, d, sourcePre, archiveTail, trailer, mcf,
      z, tail] using hbody0
  have hbodyPrefix := runtimeContinuationLocator_prefixSafe tail bodyClock
  have hbodyLeft : LeftSafeRun runtimeContinuationLocatorMachine
      (init runtimeContinuationLocatorMachine tail) bodyClock := by
    intro i hi
    exact (hbodyPrefix i hi).leftInside
  have hbodyShift : LeftSafeRun runtimeContinuationLocatorMachine
      ⟨runtimeContinuationLocatorMachine.start, markerPre.length, T⟩
      bodyClock := by
    have hs := leftSafeRun_shiftCfg runtimeContinuationLocatorMachine
      markerPre (init runtimeContinuationLocatorMachine tail) bodyClock
      hbodyPrefix hbodyLeft
    simpa [shiftCfg, T, tail, init] using hs
  have hlocLeft := runtimeRoundEntryLocator_leftSafe T locatorClock
  have hbodyHalt : runtimeContinuationLocatorMachine.halt
      (run runtimeContinuationLocatorMachine bodyClock
        ⟨runtimeContinuationLocatorMachine.start, markerPre.length, T⟩).st =
      true := by
    have hshift := run_shiftCfg runtimeContinuationLocatorMachine markerPre
      (init runtimeContinuationLocatorMachine tail) bodyClock hbodyPrefix
    have hstart : shiftCfg runtimeContinuationLocatorMachine markerPre
        (init runtimeContinuationLocatorMachine tail) =
      (⟨runtimeContinuationLocatorMachine.start, markerPre.length, T⟩ :
        Cfg runtimeContinuationLocatorMachine) := by
      simp [shiftCfg, T, tail, init]
    rw [← hstart, hshift, hbody]
    rfl
  have hs := headSeqAccept_leftSafe runtimeRoundEntryLocatorMachine
    runtimeContinuationLocatorMachine T T locatorClock bodyClock
    markerPre.length RuntimeRoundEntryState.done hloc rfl hlocLeft
    hbodyShift hbodyHalt
  simpa [runtimeMarkedContinuationMachine, runtimeMarkedContinuationClock,
    runtimeMarkedAcceptBody, runtimeMarkedAcceptClock, locatorClock,
    bodyClock, bits, d, sourcePre, archiveTail, trailer, mcf, markerPre,
    tail, T, Nat.add_assoc] using hs

/-! ## Conditional-dispatch left-safety calculus -/

theorem condSeq_leftSafe_inl (M1 Mt Mf : Machine) (c : Cfg M1)
    (t : Nat) (hno : ∀ i < t, M1.halt (run M1 i c).st = false)
    (hsafe : LeftSafeRun M1 c t) :
    LeftSafeRun (condSeqMachine M1 Mt Mf) (inlCfg M1 Mt Mf c) t := by
  intro i hi hhalt hmove
  have hr := run_cond_inl (M1 := M1) (Mt := Mt) (Mf := Mf) c i
    (fun j hj => hno j (by omega))
  rw [hr] at hhalt hmove ⊢
  have hh1 := hno i hi
  have hm1 : (M1.δ (run M1 i c).st
      ((run M1 i c).tp.getD (run M1 i c).hd false)).2.2 = 0 := by
    simpa [condSeqMachine, inlCfg, hh1] using hmove
  exact hsafe i hi hh1 hm1

theorem condSeq_leftSafe_handoff (M1 Mt Mf : Machine) (c : Cfg M1)
    (hh : M1.halt c.st = true) :
    LeftSafeRun (condSeqMachine M1 Mt Mf) (inlCfg M1 Mt Mf c) 1 := by
  apply leftSafeRun_one_of_not_left
  simp [condSeqMachine, inlCfg, hh]

theorem condSeq_leftSafe_inrl (M1 Mt Mf : Machine) (c : Cfg Mt)
    (t : Nat) (hsafe : LeftSafeRun Mt c t) :
    LeftSafeRun (condSeqMachine M1 Mt Mf) (inrlCfg M1 Mt Mf c) t := by
  intro i hi hhalt hmove
  rw [run_cond_inrl (M1 := M1) (Mt := Mt) (Mf := Mf) c i] at hhalt hmove ⊢
  have hh : Mt.halt (run Mt i c).st = false := by
    simpa [condSeqMachine, inrlCfg] using hhalt
  have hm : (Mt.δ (run Mt i c).st
      ((run Mt i c).tp.getD (run Mt i c).hd false)).2.2 = 0 := by
    simpa [condSeqMachine, inrlCfg] using hmove
  exact hsafe i hi hh hm

theorem condSeq_leftSafe_inrr (M1 Mt Mf : Machine) (c : Cfg Mf)
    (t : Nat) (hsafe : LeftSafeRun Mf c t) :
    LeftSafeRun (condSeqMachine M1 Mt Mf) (inrrCfg M1 Mt Mf c) t := by
  intro i hi hhalt hmove
  rw [run_cond_inrr (M1 := M1) (Mt := Mt) (Mf := Mf) c i] at hhalt hmove ⊢
  have hh : Mf.halt (run Mf i c).st = false := by
    simpa [condSeqMachine, inrrCfg] using hhalt
  have hm : (Mf.δ (run Mf i c).st
      ((run Mf i c).tp.getD (run Mf i c).hd false)).2.2 = 0 := by
    simpa [condSeqMachine, inrrCfg] using hmove
  exact hsafe i hi hh hm

/-- Left safety composes through the real true-arm reset handoff, including
the same least-halt slack absorption used by `condSeq_run_true`. -/
theorem condSeq_leftSafe_true (M1 Mt Mf : Machine)
    (T0 T1 : List Bool) (t1 t2 p1 : Nat)
    (s1 : M1.State)
    (h1 : run M1 t1 (init M1 T0) = ⟨s1, p1, T1⟩)
    (hh1 : M1.halt s1 = true) (ha1 : M1.accept s1 = true)
    (hsafe1 : LeftSafeRun M1 (init M1 T0) t1)
    (hsafe2 : LeftSafeRun Mt (init Mt T1) t2)
    (hh2 : Mt.halt (run Mt t2 (init Mt T1)).st = true) :
    LeftSafeRun (condSeqMachine M1 Mt Mf)
      (init (condSeqMachine M1 Mt Mf) T0) (t1 + 1 + t2) := by
  have hex : ∃ t, M1.halt (run M1 t (init M1 T0)).st = true :=
    ⟨t1, by rw [h1]; exact hh1⟩
  let tm := Nat.find hex
  have htm : M1.halt (run M1 tm (init M1 T0)).st = true :=
    Nat.find_spec hex
  have htmle : tm ≤ t1 := Nat.find_le (by rw [h1]; exact hh1)
  have hfrozen : run M1 tm (init M1 T0) = ⟨s1, p1, T1⟩ := by
    rw [← run_stable M1 T0 htmle htm, h1]
  have hno : ∀ i < tm,
      M1.halt (run M1 i (init M1 T0)).st = false := by
    intro i hi
    simpa using Nat.find_min hex hi
  have hs1 : LeftSafeRun (condSeqMachine M1 Mt Mf)
      (init (condSeqMachine M1 Mt Mf) T0) tm := by
    change LeftSafeRun (condSeqMachine M1 Mt Mf)
      (inlCfg M1 Mt Mf (init M1 T0)) tm
    exact condSeq_leftSafe_inl M1 Mt Mf (init M1 T0) tm hno
      (fun i hi => hsafe1 i (by omega))
  have hrun1 : run (condSeqMachine M1 Mt Mf) tm
      (init (condSeqMachine M1 Mt Mf) T0) =
      inlCfg M1 Mt Mf (⟨s1, p1, T1⟩ : Cfg M1) := by
    change run (condSeqMachine M1 Mt Mf) tm
      (inlCfg M1 Mt Mf (init M1 T0)) = _
    rw [run_cond_inl (M1 := M1) (Mt := Mt) (Mf := Mf) _ tm hno, hfrozen]
  have hsSwitch : LeftSafeRun (condSeqMachine M1 Mt Mf)
      (run (condSeqMachine M1 Mt Mf) tm
        (init (condSeqMachine M1 Mt Mf) T0)) 1 := by
    rw [hrun1]
    exact condSeq_leftSafe_handoff M1 Mt Mf _ hh1
  have hafter : run (condSeqMachine M1 Mt Mf) 1
      (run (condSeqMachine M1 Mt Mf) tm
        (init (condSeqMachine M1 Mt Mf) T0)) =
      inrlCfg M1 Mt Mf (init Mt T1) := by
    rw [hrun1, run_succ, run_zero]
    exact step_cond_handoff_true (M1 := M1) (Mt := Mt) (Mf := Mf)
      (⟨s1, p1, T1⟩ : Cfg M1) hh1 ha1
  have hs2 : LeftSafeRun (condSeqMachine M1 Mt Mf)
      (run (condSeqMachine M1 Mt Mf) (tm + 1)
        (init (condSeqMachine M1 Mt Mf) T0)) t2 := by
    rw [run_add, hafter]
    exact condSeq_leftSafe_inrl M1 Mt Mf _ t2 hsafe2
  have hsMain : LeftSafeRun (condSeqMachine M1 Mt Mf)
      (init (condSeqMachine M1 Mt Mf) T0) (tm + 1 + t2) :=
    leftSafeRun_add (leftSafeRun_add hs1 hsSwitch) hs2
  have hhaltAt : (condSeqMachine M1 Mt Mf).halt
      (run (condSeqMachine M1 Mt Mf) (tm + 1 + t2)
        (init (condSeqMachine M1 Mt Mf) T0)).st =
      Mt.halt (run Mt t2 (init Mt T1)).st := by
    rw [show tm + 1 + t2 = (tm + 1) + t2 by omega, run_add]
    rw [run_add, hafter, run_cond_inrl]
    rfl
  have hsSlack : LeftSafeRun (condSeqMachine M1 Mt Mf)
      (run (condSeqMachine M1 Mt Mf) (tm + 1 + t2)
        (init (condSeqMachine M1 Mt Mf) T0)) (t1 - tm) :=
    PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeLeftSafety.leftSafeRun_of_halted
      _ (by rw [hhaltAt, hh2])
  have hsAll := leftSafeRun_add hsMain hsSlack
  convert hsAll using 1
  omega

/-- False-arm counterpart of `condSeq_leftSafe_true`. -/
theorem condSeq_leftSafe_false (M1 Mt Mf : Machine)
    (T0 T1 : List Bool) (t1 t2 p1 : Nat)
    (s1 : M1.State)
    (h1 : run M1 t1 (init M1 T0) = ⟨s1, p1, T1⟩)
    (hh1 : M1.halt s1 = true) (ha1 : M1.accept s1 = false)
    (hsafe1 : LeftSafeRun M1 (init M1 T0) t1)
    (hsafe2 : LeftSafeRun Mf (init Mf T1) t2)
    (hh2 : Mf.halt (run Mf t2 (init Mf T1)).st = true) :
    LeftSafeRun (condSeqMachine M1 Mt Mf)
      (init (condSeqMachine M1 Mt Mf) T0) (t1 + 1 + t2) := by
  have hex : ∃ t, M1.halt (run M1 t (init M1 T0)).st = true :=
    ⟨t1, by rw [h1]; exact hh1⟩
  let tm := Nat.find hex
  have htmle : tm ≤ t1 := Nat.find_le (by rw [h1]; exact hh1)
  have hfrozen : run M1 tm (init M1 T0) = ⟨s1, p1, T1⟩ := by
    rw [← run_stable M1 T0 htmle (Nat.find_spec hex), h1]
  have hno : ∀ i < tm,
      M1.halt (run M1 i (init M1 T0)).st = false := by
    intro i hi
    simpa using Nat.find_min hex hi
  have hs1 : LeftSafeRun (condSeqMachine M1 Mt Mf)
      (init (condSeqMachine M1 Mt Mf) T0) tm := by
    change LeftSafeRun (condSeqMachine M1 Mt Mf)
      (inlCfg M1 Mt Mf (init M1 T0)) tm
    exact condSeq_leftSafe_inl M1 Mt Mf (init M1 T0) tm hno
      (fun i hi => hsafe1 i (by omega))
  have hrun1 : run (condSeqMachine M1 Mt Mf) tm
      (init (condSeqMachine M1 Mt Mf) T0) =
      inlCfg M1 Mt Mf (⟨s1, p1, T1⟩ : Cfg M1) := by
    change run (condSeqMachine M1 Mt Mf) tm
      (inlCfg M1 Mt Mf (init M1 T0)) = _
    rw [run_cond_inl (M1 := M1) (Mt := Mt) (Mf := Mf) _ tm hno, hfrozen]
  have hsSwitch : LeftSafeRun (condSeqMachine M1 Mt Mf)
      (run (condSeqMachine M1 Mt Mf) tm
        (init (condSeqMachine M1 Mt Mf) T0)) 1 := by
    rw [hrun1]
    exact condSeq_leftSafe_handoff M1 Mt Mf _ hh1
  have hafter : run (condSeqMachine M1 Mt Mf) 1
      (run (condSeqMachine M1 Mt Mf) tm
        (init (condSeqMachine M1 Mt Mf) T0)) =
      inrrCfg M1 Mt Mf (init Mf T1) := by
    rw [hrun1, run_succ, run_zero]
    exact step_cond_handoff_false (M1 := M1) (Mt := Mt) (Mf := Mf)
      (⟨s1, p1, T1⟩ : Cfg M1) hh1 ha1
  have hs2 : LeftSafeRun (condSeqMachine M1 Mt Mf)
      (run (condSeqMachine M1 Mt Mf) (tm + 1)
        (init (condSeqMachine M1 Mt Mf) T0)) t2 := by
    rw [run_add, hafter]
    exact condSeq_leftSafe_inrr M1 Mt Mf _ t2 hsafe2
  have hsMain : LeftSafeRun (condSeqMachine M1 Mt Mf)
      (init (condSeqMachine M1 Mt Mf) T0) (tm + 1 + t2) :=
    leftSafeRun_add (leftSafeRun_add hs1 hsSwitch) hs2
  have hhaltAt : (condSeqMachine M1 Mt Mf).halt
      (run (condSeqMachine M1 Mt Mf) (tm + 1 + t2)
        (init (condSeqMachine M1 Mt Mf) T0)).st =
      Mf.halt (run Mf t2 (init Mf T1)).st := by
    rw [show tm + 1 + t2 = (tm + 1) + t2 by omega, run_add]
    rw [run_add, hafter, run_cond_inrr]
    rfl
  have hsSlack : LeftSafeRun (condSeqMachine M1 Mt Mf)
      (run (condSeqMachine M1 Mt Mf) (tm + 1 + t2)
        (init (condSeqMachine M1 Mt Mf) T0)) (t1 - tm) :=
    leftSafeRun_of_halted _ (by rw [hhaltAt, hh2])
  have hsAll := leftSafeRun_add hsMain hsSlack
  convert hsAll using 1
  omega

/-- Exact nonterminal dispatch.  The only arm premise is the native run of
the fixed physical rebaser on the classifier-preserved tape. -/
theorem runtimeContinuationDispatch_run_nonterminal
    (pairs : List (Bool × Bool)) (w : List Bool) (l : Lit)
    (first : List Bool) (more : List (List Bool))
    (hsafe : RuntimeNoDoubleSepFrom false pairs)
    (rebaseClock rebaseHead : Nat)
    (rebaseState : runtimeConsumingMarkedWorkspaceArchiveReturnUnaryRebaseMachine.State)
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
      let markerPre := flattenPairs pairs ++ [false, true, false, true]
      run runtimeConsumingMarkedWorkspaceArchiveReturnUnaryRebaseMachine rebaseClock
          (init runtimeConsumingMarkedWorkspaceArchiveReturnUnaryRebaseMachine
            (markerPre ++ sourcePre ++ mcf.tp)) =
        ⟨rebaseState, rebaseHead, rebaseTape⟩)
    (hrebaseHalt :
      runtimeConsumingMarkedWorkspaceArchiveReturnUnaryRebaseMachine.halt rebaseState = true) :
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
    run runtimeContinuationDispatchMachine
        (runtimeMarkedContinuationClock pairs d l + 1 + rebaseClock)
        (init runtimeContinuationDispatchMachine
          (markerPre ++ sourcePre ++ mcf.tp)) =
      ⟨Sum.inr (Sum.inl rebaseState), rebaseHead, rebaseTape⟩ := by
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
  have hloc := runtimeMarkedContinuation_run pairs w l rest hsafe
  have hloc' : run runtimeMarkedContinuationMachine
      (runtimeMarkedContinuationClock pairs d l)
      (init runtimeMarkedContinuationMachine T) =
      ⟨Sum.inr (RuntimeContinuationLocatorState.done true),
        markerPre.length + (sourcePre.length + 2 * bits.length + 6), T⟩ := by
    simpa [bits, rest, d, sourcePre, archiveTail, trailer, mcf, markerPre, T]
      using hloc
  apply condSeq_run_true T T rebaseTape
    (runtimeMarkedContinuationClock pairs d l) rebaseClock
    (Sum.inr (RuntimeContinuationLocatorState.done true))
    (markerPre.length + (sourcePre.length + 2 * bits.length + 6))
    rebaseState rebaseHead hloc'
  · rfl
  · rfl
  · simpa [bits, rest, d, sourcePre, archiveTail, trailer, mcf, markerPre, T]
      using hrebase
  · exact hrebaseHalt

/-- Exact terminal dispatch.  With no future archive, the classifier selects
the halt arm, resets to physical origin, and leaves every tape cell intact. -/
theorem runtimeContinuationDispatch_run_terminal
    (pairs : List (Bool × Bool)) (w : List Bool) (l : Lit)
    (hsafe : RuntimeNoDoubleSepFrom false pairs) :
    let bits := literalLookupTape w l
    let rest : List (List Bool) := []
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
    run runtimeContinuationDispatchMachine
        (runtimeMarkedContinuationClock pairs d l + 1)
        (init runtimeContinuationDispatchMachine T) =
      ⟨Sum.inr (Sum.inr ()), 0, T⟩ := by
  dsimp only
  let bits := literalLookupTape w l
  let rest : List (List Bool) := []
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
  have hloc := runtimeMarkedContinuation_run pairs w l rest hsafe
  have hloc' : run runtimeMarkedContinuationMachine
      (runtimeMarkedContinuationClock pairs d l)
      (init runtimeMarkedContinuationMachine T) =
      ⟨Sum.inr (RuntimeContinuationLocatorState.done false),
        markerPre.length + (sourcePre.length + 2 * bits.length + 6), T⟩ := by
    simpa [bits, rest, d, sourcePre, archiveTail, trailer, mcf, markerPre, T]
      using hloc
  have hdispatch := condSeq_run_false
    (M1 := runtimeMarkedContinuationMachine)
    (Mt := runtimeConsumingMarkedWorkspaceArchiveReturnUnaryRebaseMachine)
    (Mf := runtimeTerminalHaltMachine)
    T T T (runtimeMarkedContinuationClock pairs d l) 0
    (Sum.inr (RuntimeContinuationLocatorState.done false))
    (markerPre.length + (sourcePre.length + 2 * bits.length + 6))
    () 0 hloc' (by rfl) (by rfl) (by rfl) (by rfl)
  simpa [runtimeContinuationDispatchMachine, bits, rest, d, sourcePre,
    archiveTail, trailer, mcf, markerPre, T] using hdispatch

/-- The complete terminal branch is concretely left-safe; it needs no
physical-rebase premise because the false arm is already halted. -/
theorem runtimeContinuationDispatch_leftSafe_terminal
    (pairs : List (Bool × Bool)) (w : List Bool) (l : Lit)
    (hsafe : RuntimeNoDoubleSepFrom false pairs) :
    let bits := literalLookupTape w l
    let rest : List (List Bool) := []
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
      (runtimeMarkedContinuationClock pairs d l + 1) := by
  dsimp only
  let bits := literalLookupTape w l
  let rest : List (List Bool) := []
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
      ⟨Sum.inr (RuntimeContinuationLocatorState.done false),
        markerPre.length + (sourcePre.length + 2 * bits.length + 6), T⟩ := by
    simpa [bits, rest, d, sourcePre, archiveTail, trailer, mcf, markerPre, T]
      using hloc0
  have hleft := runtimeMarkedContinuation_leftSafe pairs w l rest hsafe
  have hs := condSeq_leftSafe_false runtimeMarkedContinuationMachine
    runtimeConsumingMarkedWorkspaceArchiveReturnUnaryRebaseMachine runtimeTerminalHaltMachine
    T T (runtimeMarkedContinuationClock pairs d l) 0
    (markerPre.length + (sourcePre.length + 2 * bits.length + 6))
    (Sum.inr (RuntimeContinuationLocatorState.done false))
    hloc rfl rfl
    (by simpa [bits, rest, d, sourcePre, archiveTail, trailer, mcf,
      markerPre, T] using hleft)
    (by simp [LeftSafeRun]) (by rfl)
  simpa [runtimeContinuationDispatchMachine, bits, rest, d, sourcePre,
    archiveTail, trailer, mcf, markerPre, T] using hs

theorem runtimeContinuationDispatch_halt_nonterminal
    (s : runtimeConsumingMarkedWorkspaceArchiveReturnUnaryRebaseMachine.State)
    (h : runtimeConsumingMarkedWorkspaceArchiveReturnUnaryRebaseMachine.halt s = true) :
    runtimeContinuationDispatchMachine.halt
      (Sum.inr (Sum.inl s)) = true := by
  simpa [runtimeContinuationDispatchMachine] using
    cond_halt_final_true
      (M1 := runtimeMarkedContinuationMachine)
      (Mt := runtimeConsumingMarkedWorkspaceArchiveReturnUnaryRebaseMachine)
      (Mf := runtimeTerminalHaltMachine) s h

theorem runtimeContinuationDispatch_halt_terminal :
    runtimeContinuationDispatchMachine.halt
      (Sum.inr (Sum.inr ())) = true := by
  rfl

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeContinuationDispatch

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeContinuationDispatch.runtimeContinuationDispatch_run_nonterminal
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeContinuationDispatch.runtimeContinuationDispatch_run_terminal
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeContinuationDispatch.condSeq_leftSafe_true
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeContinuationDispatch.runtimeRoundEntryLocator_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeContinuationDispatch.runtimeMarkedContinuation_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeContinuationDispatch.condSeq_leftSafe_false
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeContinuationDispatch.runtimeContinuationDispatch_leftSafe_terminal
