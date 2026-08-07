import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeRoundEntryAdapter
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeLeftSafety

/-!
# Charged local lookup: execute from the runtime entry marker

The unary rebaser leaves a variable-length, pair-aligned residue before its
reserved doubled separator.  The fixed locator already rediscovers the exact
selector origin.  This file turns that endpoint into an executable handoff:
after locating the marker, a prefix-safe accepting body runs with that
selector as its virtual origin, preserving the entire residue and exposing
the body's real accept bit.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeMarkedEntry

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixAdapter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeLeftSafety
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryAdapter

/-- Locate the doubled runtime marker, then execute an accepting body from
the discovered selector head without resetting between the two phases. -/
def runtimeMarkedAcceptBody (M : Machine) : Machine :=
  headSeqAcceptMachine runtimeRoundEntryLocatorMachine M

def runtimeMarkedAcceptClock (pairs : List (Bool × Bool))
    (bodyClock : Nat) : Nat :=
  2 * pairs.length + 7 + 1 + bodyClock

/-- Exact marker-relative transport for any prefix-safe accepting body. -/
theorem runtimeMarkedAcceptBody_run (M : Machine)
    (pairs : List (Bool × Bool)) (tail tail' : List Bool)
    (tailLo tailHi : Bool)
    (hsafeMarker : RuntimeNoDoubleSepFrom false pairs)
    (htail : tail = tailLo :: tailHi :: tail.drop 2)
    (hnonsep : runtimePairIsSep (tailLo, tailHi) = false)
    (bodyClock : Nat) (sf : M.State) (pf : Nat)
    (hrun : run M bodyClock (init M tail) = ⟨sf, pf, tail'⟩)
    (hhalt : M.halt sf = true)
    (hsafeBody : PrefixSafeRun M (init M tail) bodyClock) :
    let pre := flattenPairs pairs ++ [false, true, false, true]
    run (runtimeMarkedAcceptBody M)
        (runtimeMarkedAcceptClock pairs bodyClock)
        (init (runtimeMarkedAcceptBody M) (pre ++ tail)) =
      ⟨Sum.inr sf, pre.length + pf, pre ++ tail'⟩ := by
  dsimp only
  let pre := flattenPairs pairs ++ [false, true, false, true]
  let T := pre ++ tail
  have hloc := runtimeRoundEntryLocator_run pairs tail tailLo tailHi
    hsafeMarker htail hnonsep
  have hloc' : run runtimeRoundEntryLocatorMachine
      (2 * pairs.length + 7)
      (init runtimeRoundEntryLocatorMachine T) =
    ⟨RuntimeRoundEntryState.done, pre.length, T⟩ := by
    simpa [T, pre, flattenPairs_length, List.append_assoc] using hloc
  have hshift := run_shiftCfg M pre (init M tail) bodyClock hsafeBody
  have hbody : run M bodyClock ⟨M.start, pre.length, T⟩ =
      ⟨sf, pre.length + pf, pre ++ tail'⟩ := by
    have hstart : shiftCfg M pre (init M tail) =
        (⟨M.start, pre.length, T⟩ : Cfg M) := by
      simp [shiftCfg, init, T]
    rw [← hstart, hshift, hrun]
    simp [shiftCfg]
  have hjoin := headSeqAccept_run runtimeRoundEntryLocatorMachine M
    T T (pre ++ tail') (2 * pairs.length + 7) bodyClock
    pre.length (pre.length + pf) RuntimeRoundEntryState.done sf
    hloc' rfl hbody hhalt
  simpa [runtimeMarkedAcceptBody, runtimeMarkedAcceptClock, pre, T,
    Nat.add_assoc] using hjoin

/-- The marker handoff exposes the nested body's accept bit unchanged. -/
theorem runtimeMarkedAcceptBody_accept (M : Machine) (sf : M.State) :
    (runtimeMarkedAcceptBody M).accept (Sum.inr sf) = M.accept sf := by
  rfl

/-! ## Reset-free selector for a freshly rebased archive -/

inductive RuntimeFrontSelectorState
  | lo
  | hi (loBit : Bool)
  | headerLo
  | headerHi
  | done
  deriving Fintype, DecidableEq

open RuntimeFrontSelectorState

/-- A rebased selector always selects its first archive block: `11* 01 10`.
This specialized fixed parser contains no reset transition, unlike the more
general selector that must repeatedly return to its countdown origin. -/
def runtimeFrontSelectorMachine : Machine where
  State := RuntimeFrontSelectorState
  fin := inferInstance
  dec := inferInstance
  start := .lo
  halt s := decide (s = .done)
  δ s b := match s with
    | .lo => (.hi b, none, 1)
    | .hi loBit =>
        if loBit && b then (.lo, none, 1)
        else if !loBit && b then (.headerLo, none, 1)
        else (.hi loBit, none, 2)
    | .headerLo => (.headerHi, none, 1)
    | .headerHi => (.done, none, 1)
    | .done => (.done, none, 2)
  accept := fun _ => false

theorem runtimeFrontSelector_pair (T : List Bool) (q : Nat)
    (hlo : T.getD q false = true)
    (hhi : T.getD (q + 1) false = true) :
    run runtimeFrontSelectorMachine 2 ⟨lo, q, T⟩ =
      ⟨lo, q + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo hhi
  simp [run_succ, step, runtimeFrontSelectorMachine, moveHead, hlo, hhi]

theorem runtimeFrontSelector_scan (pre tail : List Bool) : ∀ n,
    run runtimeFrontSelectorMachine (2 * n)
        ⟨lo, pre.length,
          pre ++ flattenPairs (List.replicate n (true, true)) ++ tail⟩ =
      ⟨lo, pre.length + 2 * n,
        pre ++ flattenPairs (List.replicate n (true, true)) ++ tail⟩
  | 0 => by simp
  | n + 1 => by
      let T := pre ++ flattenPairs (List.replicate (n + 1) (true, true)) ++ tail
      have hlo : T.getD pre.length false = true := by
        simp [T, List.replicate_succ, flattenPairs]
      have hhi : T.getD (pre.length + 1) false = true := by
        simp [T, List.replicate_succ, flattenPairs]
      have hpair := runtimeFrontSelector_pair T pre.length hlo hhi
      have ih := runtimeFrontSelector_scan (pre ++ [true, true]) tail n
      rw [show 2 * (n + 1) = 2 + 2 * n by omega, run_add, hpair]
      simpa [T, flattenPairs, List.replicate_succ, List.append_assoc,
        Nat.add_assoc] using ih

/-- Cross the rebased countdown, its `01` boundary, and the first fresh
archive header `10`, halting at the selected doubled payload. -/
theorem runtimeFrontSelector_run (d : Nat) (tail : List Bool) :
    let T := flattenPairs (List.replicate d (true, true)) ++
      [false, true, true, false] ++ tail
    run runtimeFrontSelectorMachine (2 * d + 4)
        (init runtimeFrontSelectorMachine T) =
      ⟨done, 2 * d + 4, T⟩ := by
  dsimp only
  let pre := flattenPairs (List.replicate d (true, true))
  let T := pre ++ [false, true, true, false] ++ tail
  have hscan := runtimeFrontSelector_scan ([] : List Bool)
    ([false, true, true, false] ++ tail) d
  have hscan' : run runtimeFrontSelectorMachine (2 * d)
      (init runtimeFrontSelectorMachine T) = ⟨lo, 2 * d, T⟩ := by
    simpa [T, pre] using hscan
  rw [show 2 * d + 4 = 2 * d + 4 by rfl, run_add, hscan']
  simp [run_succ, step, runtimeFrontSelectorMachine, moveHead, T, pre,
    flattenPairs_length]

theorem runtimeFrontSelector_move_ne_reset
    (s : runtimeFrontSelectorMachine.State) (b : Bool) :
    (runtimeFrontSelectorMachine.δ s b).2.2 ≠ 3 := by
  cases s <;> cases b <;> simp [runtimeFrontSelectorMachine] <;>
    split_ifs <;> simp

theorem runtimeFrontSelector_move_ne_left
    (s : runtimeFrontSelectorMachine.State) (b : Bool) :
    (runtimeFrontSelectorMachine.δ s b).2.2 ≠ 0 := by
  cases s <;> cases b <;> simp [runtimeFrontSelectorMachine] <;>
    split_ifs <;> simp

theorem runtimeFrontSelector_prefixSafe (T : List Bool) (n : Nat) :
    PrefixSafeRun runtimeFrontSelectorMachine
      (init runtimeFrontSelectorMachine T) n := by
  intro i hi
  constructor
  · intro _
    exact runtimeFrontSelector_move_ne_reset _ _
  · intro _ hleft
    exact False.elim (runtimeFrontSelector_move_ne_left _ _ hleft)

def runtimeFrontSelectorInput (d : Nat) (tail : List Bool) : List Bool :=
  flattenPairs (List.replicate d (true, true)) ++
    [false, true, true, false] ++ tail

theorem sourceSelectorInput_front (bits : List Bool)
    (rest : List (List Bool)) :
    sourceSelectorInput (bits :: rest).length 0 (bits :: rest) =
      runtimeFrontSelectorInput (bits :: rest).length
        (encodeD bits ++ flattenPairs (rest.flatMap freshSourceBlock)) := by
  simp [sourceSelectorInput, sourceArchive, runtimeFrontSelectorInput,
    freshSourceBlock, List.append_assoc]
  rw [← flattenPairs_dataPairs bits]
  simp [flattenPairs_append, flattenPairs, List.append_assoc]

/-- The real marker-to-payload controller.  It first tolerates the reachable
double/triple separator boundary, then crosses the freshly rebased selector
`11* 01` and its first archive header `10`, halting at the first doubled
payload cell. -/
theorem runtimeMarkedFrontSelector_run
    (pairs : List (Bool × Bool)) (d : Nat) (tail : List Bool)
    (hd : 0 < d) (hsafe : RuntimeNoDoubleSepFrom false pairs) :
    let source := runtimeFrontSelectorInput d tail
    let pre := flattenPairs pairs ++ [false, true, false, true]
    run (runtimeMarkedAcceptBody runtimeFrontSelectorMachine)
        (runtimeMarkedAcceptClock pairs (2 * d + 4))
        (init (runtimeMarkedAcceptBody runtimeFrontSelectorMachine)
          (pre ++ source)) =
      ⟨Sum.inr done, pre.length + (2 * d + 4), pre ++ source⟩ := by
  dsimp only
  let source := runtimeFrontSelectorInput d tail
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hsource : source = true :: true :: source.drop 2 := by
    simp [source, runtimeFrontSelectorInput, List.replicate_succ,
      flattenPairs, List.append_assoc]
  apply runtimeMarkedAcceptBody_run runtimeFrontSelectorMachine pairs
    source source true true hsafe hsource (by simp [runtimePairIsSep])
    (2 * (k + 1) + 4) done (2 * (k + 1) + 4)
  · simpa [source, runtimeFrontSelectorInput] using
      runtimeFrontSelector_run (k + 1) tail
  · rfl
  · exact runtimeFrontSelector_prefixSafe source (2 * (k + 1) + 4)

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeMarkedEntry

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeMarkedEntry.runtimeMarkedAcceptBody_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeMarkedEntry.runtimeFrontSelector_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeMarkedEntry.runtimeMarkedFrontSelector_run
