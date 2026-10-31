import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeRebaseLocator

/-!
# Fixed locator for the preserved future source archive

Absolute splice offsets should not be stored in doubled unary: that metadata
can be larger than the consumed workspace it describes.  The preserved future
archive is already self-delimiting.  Each block has grammar

`10 (00|11)* 01`

and the physical end is the default blank pair `00`.  This file defines one
fixed finite controller that parses exactly that grammar, crosses every future
block, and halts after the first blank header.  It therefore derives the live
remaining-block traversal directly from tape structure, with no offset or
block count in its state space.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveLocator

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativeOutput
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTailPreservation

inductive RuntimeArchiveLocatorState
  | headerLo
  | headerHi (lo : Bool)
  | dataLo
  | dataHi (lo : Bool)
  | done
  deriving DecidableEq, Fintype

open RuntimeArchiveLocatorState

/-- Fixed parser for a contiguous archive of fresh `10 ... 01` blocks. -/
def runtimeArchiveLocatorMachine : Machine where
  State := RuntimeArchiveLocatorState
  fin := inferInstance
  dec := inferInstance
  start := .headerLo
  halt := fun s => decide (s = .done)
  δ := fun s b =>
    match s with
    | .headerLo => (.headerHi b, none, 1)
    | .headerHi lo =>
        if lo && !b then (.dataLo, none, 1)
        else if !lo && !b then (.done, none, 1)
        else (.done, none, 2)
    | .dataLo => (.dataHi b, none, 1)
    | .dataHi lo =>
        if lo = b then (.dataLo, none, 1)
        else if !lo && b then (.headerLo, none, 1)
        else (.done, none, 2)
    | .done => (.done, none, 2)
  accept := fun _ => false

theorem runtimeArchive_run_header (T : List Bool) (p : Nat)
    (h0 : T.getD p false = true)
    (h1 : T.getD (p + 1) false = false) :
    run runtimeArchiveLocatorMachine 2 ⟨.headerLo, p, T⟩ =
      ⟨dataLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h0 h1
  simp [run_succ, step, runtimeArchiveLocatorMachine, moveHead, h0, h1]

theorem runtimeArchive_run_dataPair (T : List Bool) (p : Nat)
    (h : T.getD p false = T.getD (p + 1) false) :
    run runtimeArchiveLocatorMachine 2 ⟨dataLo, p, T⟩ =
      ⟨dataLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [run_succ, step, runtimeArchiveLocatorMachine, moveHead, h]

theorem runtimeArchive_run_terminator (T : List Bool) (p : Nat)
    (h0 : T.getD p false = false)
    (h1 : T.getD (p + 1) false = true) :
    run runtimeArchiveLocatorMachine 2 ⟨dataLo, p, T⟩ =
      ⟨headerLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h0 h1
  simp [run_succ, step, runtimeArchiveLocatorMachine, moveHead, h0, h1]

theorem runtimeArchive_run_blank (T : List Bool) (p : Nat)
    (h0 : T.getD p false = false)
    (h1 : T.getD (p + 1) false = false) :
    run runtimeArchiveLocatorMachine 2 ⟨headerLo, p, T⟩ =
      ⟨done, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h0 h1
  simp [run_succ, step, runtimeArchiveLocatorMachine, moveHead, h0, h1]

/-- Scan any sequence of equal data pairs. -/
theorem runtimeArchive_run_dataPairs (T : List Bool) (q k : Nat)
    (h : ∀ i, i < k →
      T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run runtimeArchiveLocatorMachine (2 * k) ⟨dataLo, q, T⟩ =
      ⟨dataLo, q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hk := h k (by omega)
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, run_add,
        ih (fun i hi => h i (by omega)),
        runtimeArchive_run_dataPair T (q + 2 * k) (by
          simpa [Nat.add_assoc] using hk)]
      congr 1

/-- Boolean-list form of one fresh source block. -/
theorem flattenPairs_freshSourceBlock (bits : List Bool) :
    flattenPairs (freshSourceBlock bits) =
      [true, false] ++ encodeD bits := by
  change true :: false ::
      flattenPairs (dataPairs bits ++ [(false, true)]) =
    true :: false :: encodeD bits
  rw [flattenPairs_dataPairs]

theorem selectedTail_cons (bits : List Bool) (rest : List (List Bool)) :
    selectedTail (bits :: rest) =
      [true, false] ++ encodeD bits ++ selectedTail rest := by
  simp [selectedTail, flattenPairs_append, flattenPairs_freshSourceBlock]

theorem prefixed_block_header_lo (pre bits tail : List Bool) :
    (pre ++ [true, false] ++ encodeD bits ++ tail).getD pre.length false = true := by
  rw [List.getD_append (h := by simp)]
  simp

theorem prefixed_block_header_hi (pre bits tail : List Bool) :
    (pre ++ [true, false] ++ encodeD bits ++ tail).getD (pre.length + 1) false = false := by
  rw [List.getD_append (h := by simp)]
  simp

theorem prefixed_block_getD_data (pre bits tail : List Bool) (j : Nat)
    (hj : j < (encodeD bits).length) :
    (pre ++ [true, false] ++ encodeD bits ++ tail).getD
        (pre.length + 2 + j) false =
      (encodeD bits).getD j false := by
  rw [show pre ++ [true, false] ++ encodeD bits ++ tail =
      pre ++ ([true, false] ++ (encodeD bits ++ tail)) by
        simp [List.append_assoc]]
  rw [List.getD_append_right (h := by omega)]
  rw [show pre.length + 2 + j - pre.length = 2 + j by omega]
  rw [List.getD_append_right (h := by simp)]
  simp only [List.length_cons, List.length_nil]
  rw [show 2 + j - (0 + 1 + 1) = j by omega]
  rw [List.getD_append (h := hj)]

theorem prefixed_block_data_eq (pre bits tail : List Bool) (i : Nat)
    (hi : i < bits.length) :
    (pre ++ [true, false] ++ encodeD bits ++ tail).getD
        (pre.length + 2 + 2 * i) false =
      (pre ++ [true, false] ++ encodeD bits ++ tail).getD
        (pre.length + 2 + 2 * i + 1) false := by
  rw [show pre.length + 2 + 2 * i = pre.length + 2 + (2 * i) by omega,
    show pre.length + 2 + 2 * i + 1 = pre.length + 2 + (2 * i + 1) by omega,
    prefixed_block_getD_data pre bits tail (2 * i)
      (by rw [encodeD_length]; omega),
    prefixed_block_getD_data pre bits tail (2 * i + 1)
      (by rw [encodeD_length]; omega)]
  exact encodeD_data_eq bits i hi

theorem prefixed_block_term_lo (pre bits tail : List Bool) :
    (pre ++ [true, false] ++ encodeD bits ++ tail).getD
        (pre.length + 2 + 2 * bits.length) false = false := by
  rw [prefixed_block_getD_data pre bits tail (2 * bits.length)
    (by rw [encodeD_length]; omega)]
  exact encodeD_mark_lo bits

theorem prefixed_block_term_hi (pre bits tail : List Bool) :
    (pre ++ [true, false] ++ encodeD bits ++ tail).getD
        (pre.length + 2 + 2 * bits.length + 1) false = true := by
  rw [show pre.length + 2 + 2 * bits.length + 1 =
      pre.length + 2 + (2 * bits.length + 1) by omega,
    prefixed_block_getD_data pre bits tail (2 * bits.length + 1)
      (by rw [encodeD_length]; omega)]
  exact encodeD_mark_hi bits

/-- Exact traversal of one fresh archive block, preserving every cell. -/
theorem runtimeArchive_run_block (pre bits tail : List Bool) :
    let T := pre ++ [true, false] ++ encodeD bits ++ tail
    run runtimeArchiveLocatorMachine (2 * bits.length + 4)
        ⟨headerLo, pre.length, T⟩ =
      ⟨headerLo, pre.length + 2 * bits.length + 4, T⟩ := by
  dsimp only
  let T := pre ++ [true, false] ++ encodeD bits ++ tail
  have hh := runtimeArchive_run_header T pre.length
    (prefixed_block_header_lo pre bits tail)
    (prefixed_block_header_hi pre bits tail)
  have hd := runtimeArchive_run_dataPairs T (pre.length + 2)
    bits.length (fun i hi => prefixed_block_data_eq pre bits tail i hi)
  have ht := runtimeArchive_run_terminator T
    (pre.length + 2 + 2 * bits.length)
    (prefixed_block_term_lo pre bits tail)
    (prefixed_block_term_hi pre bits tail)
  rw [show 2 * bits.length + 4 = 2 + (2 * bits.length + 2) by omega,
    run_add, hh, run_add, hd]
  convert ht using 1 <;> simp [T, Nat.add_assoc, List.append_assoc] <;> omega

def runtimeArchiveLocatorClock : List (List Bool) → Nat
  | [] => 2
  | bits :: rest => 2 * bits.length + 4 + runtimeArchiveLocatorClock rest

theorem runtimeArchiveLocatorClock_eq (rest : List (List Bool)) :
    runtimeArchiveLocatorClock rest = (selectedTail rest).length + 2 := by
  induction rest with
  | nil => rfl
  | cons bits rest ih =>
      simp only [runtimeArchiveLocatorClock, selectedTail_cons,
        List.length_append, List.length_cons, List.length_nil,
        encodeD_length, ih]
      omega

/-- The fixed parser crosses the entire canonical future archive and detects
the blank pair immediately after it. -/
theorem runtimeArchiveLocator_run_prefixed
    (pre : List Bool) (rest : List (List Bool)) :
    let T := pre ++ selectedTail rest
    run runtimeArchiveLocatorMachine (runtimeArchiveLocatorClock rest)
        ⟨headerLo, pre.length, T⟩ =
      ⟨done, pre.length + (selectedTail rest).length + 2, T⟩ := by
  induction rest generalizing pre with
  | nil =>
      dsimp only [runtimeArchiveLocatorClock]
      simp only [selectedTail, List.flatMap_nil, flattenPairs]
      have h0 : pre.getD pre.length false = false := by simp
      have h1 : pre.getD (pre.length + 1) false = false := by simp
      simpa using runtimeArchive_run_blank pre pre.length h0 h1
  | cons bits rest ih =>
      rw [runtimeArchiveLocatorClock, selectedTail_cons]
      dsimp only
      let block := [true, false] ++ encodeD bits
      let tail := selectedTail rest
      let T := pre ++ block ++ tail
      have hb : run runtimeArchiveLocatorMachine (2 * bits.length + 4)
          ⟨headerLo, pre.length, T⟩ =
          ⟨headerLo, pre.length + 2 * bits.length + 4, T⟩ := by
        simpa [block, tail, T, List.append_assoc] using
          runtimeArchive_run_block pre bits tail
      have hr := ih (pre ++ block)
      simp only at hr
      have hT : (pre ++ block) ++ selectedTail rest = T := by
        simp [T, tail, List.append_assoc]
      rw [hT] at hr
      rw [show pre ++ ([true, false] ++ encodeD bits ++ selectedTail rest) = T by
        simp [T, block, tail, List.append_assoc]]
      rw [run_add]
      change run runtimeArchiveLocatorMachine (runtimeArchiveLocatorClock rest)
          (run runtimeArchiveLocatorMachine (2 * bits.length + 4)
            ⟨headerLo, pre.length, T⟩) =
        ⟨done, pre.length + (block ++ tail).length + 2, T⟩
      rw [hb]
      convert hr using 1 <;>
        simp [block, tail, encodeD_length, Nat.add_assoc] <;> omega

theorem runtimeArchiveLocator_run (rest : List (List Bool)) :
    run runtimeArchiveLocatorMachine (runtimeArchiveLocatorClock rest)
        (init runtimeArchiveLocatorMachine (selectedTail rest)) =
      ⟨done, (selectedTail rest).length + 2, selectedTail rest⟩ := by
  simpa using runtimeArchiveLocator_run_prefixed [] rest

theorem runtimeArchiveLocator_halted (rest : List (List Bool)) :
    runtimeArchiveLocatorMachine.halt
      (run runtimeArchiveLocatorMachine (runtimeArchiveLocatorClock rest)
        (init runtimeArchiveLocatorMachine (selectedTail rest))).st = true := by
  rw [runtimeArchiveLocator_run]
  rfl

/-- The same fixed parser runs directly on the genuine post-cashout tape.
For a nonterminal round it starts at the already-proved future-archive
boundary, crosses precisely the untouched remaining blocks, and halts without
changing any cell. -/
theorem scheduledRuntimeRelativeOutput_archiveLocate
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
    let T := sourceSelectorInput B t schedule
    let n := sourceRuntimeLookupClock (B - t) preBlocks w l
    let M := runtimeRelativeOutputSourceMachine B
    let clock := runtimeRelativeOutputRouteClock B out T n
    let rcf := run (acceptRouteMachine M) clock
      (init (acceptRouteMachine M) (outputCap B out ++ T))
    let R := 2 * B + 2 + pre.length + 2 * bits.length + 4
    run runtimeArchiveLocatorMachine (runtimeArchiveLocatorClock rest)
        ⟨headerLo, R, rcf.tp⟩ =
      ⟨done, R + (selectedTail rest).length + 2, rcf.tp⟩ := by
  dsimp only
  let B := (decodedLiterals x).length
  let schedule := literalTapeSchedule x w
  let preBlocks := schedule.take t
  let l := scheduledLiteral x t
  let bits := literalLookupTape w l
  let rest := schedule.drop (t + 1)
  let pre := selectedPrefix (B - t) preBlocks
  let out := (scheduledTruths x w).take t
  let T := sourceSelectorInput B t schedule
  let n := sourceRuntimeLookupClock (B - t) preBlocks w l
  let M := runtimeRelativeOutputSourceMachine B
  let clock := runtimeRelativeOutputRouteClock B out T n
  let rcf := run (acceptRouteMachine M) clock
    (init (acceptRouteMachine M) (outputCap B out ++ T))
  let R := 2 * B + 2 + pre.length + 2 * bits.length + 4
  have hfuture : rcf.tp.drop R = selectedTail rest := by
    simpa [B, schedule, preBlocks, l, bits, rest, pre, out, T, n, M,
      clock, rcf, R] using
      scheduledRuntimeRelativeOutput_futureArchive x w ht
  have hrestpos : 0 < (selectedTail rest).length := by
    have hslen : schedule.length = B := by
      simp [schedule, B, literalTapeSchedule]
    have hrs : 0 < rest.length := by
      simp [rest, hslen]
      omega
    obtain ⟨a, as, hr⟩ := List.exists_cons_of_ne_nil
      (List.ne_nil_of_length_pos hrs)
    rw [hr]
    simp [selectedTail, freshSourceBlock, flattenPairs_length]
  have hR : R ≤ rcf.tp.length := by
    have hlen := congrArg List.length hfuture
    simp only [List.length_drop] at hlen
    omega
  let front := rcf.tp.take R
  have hfront : front.length = R := by
    dsimp [front]
    rw [List.length_take, Nat.min_eq_left hR]
  have hshape : front ++ selectedTail rest = rcf.tp := by
    dsimp [front]
    rw [← hfuture]
    exact List.take_append_drop R rcf.tp
  have hr := runtimeArchiveLocator_run_prefixed front rest
  simpa [hfront, hshape] using hr

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveLocator

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveLocator.runtimeArchive_run_block
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveLocator.runtimeArchiveLocator_run_prefixed
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveLocator.scheduledRuntimeRelativeOutput_archiveLocate
