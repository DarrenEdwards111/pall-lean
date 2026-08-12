import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeMarkerDrivenClear

/-!
# Fixed reverse return to an on-tape progress mark

The outer universal shift loop cannot use an all-zero record: zero is also
the tape blank and supplies no physical exhaustion signal.  The sound record
uses `10` for an ordinary remaining pass and `01` for the final pass.  Neither
word occurs inside a passed block except its terminal `01`, and reverse scan
starts to the left of the trailing hole after crossing that terminal.

This file supplies the fixed reverse controller.  It scans pairwise to the
left, recognizes `10`, clears it to `00`, and halts at the consumed mark.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeProgressReturn

set_option maxHeartbeats 4000000

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal

inductive RuntimeProgressReturnState
  | enter
  | hi
  | lo (hiBit : Bool)
  | clearHi
  | done
  deriving DecidableEq, Fintype

/-- Fixed reverse pair scanner for the ordinary `10` progress word. -/
def runtimeProgressReturnMachine : Machine where
  State := RuntimeProgressReturnState
  fin := inferInstance
  dec := inferInstance
  start := .enter
  halt := fun s => decide (s = .done)
  δ := fun s b =>
    match s with
    | .enter => (.hi, none, 0)
    | .hi => (.lo b, none, 0)
    | .lo hiBit =>
        if b && !hiBit then (.clearHi, some false, 1)
        else (.hi, none, 0)
    | .clearHi => (.done, some false, 0)
    | .done => (.done, none, 2)
  accept := fun _ => false

private theorem progress_write_lo (pre tail : List Bool) :
    writeAt (pre ++ [true, false] ++ tail) pre.length false =
      pre ++ [false, false] ++ tail := by
  rw [PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr.writeAt_of_lt
    false (by simp)]
  simp

private theorem progress_write_hi (pre tail : List Bool) :
    writeAt (pre ++ [false, false] ++ tail) (pre.length + 1) false =
      pre ++ [false, false] ++ tail := by
  rw [PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr.writeAt_of_lt
    false (by simp)]
  simp

private theorem progress_hi_step (T : List Bool) (p : Nat) (b : Bool)
    (hread : T[p + 1]?.getD false = b) :
    step runtimeProgressReturnMachine
        ⟨RuntimeProgressReturnState.hi, p + 1, T⟩ =
      ⟨RuntimeProgressReturnState.lo b, p, T⟩ := by
  simp [step, runtimeProgressReturnMachine, moveHead, hread]

private theorem progress_lo_marker_step (T T' : List Bool) (p : Nat)
    (hread : T[p]?.getD false = true)
    (hwrite : writeAt T p false = T') :
    step runtimeProgressReturnMachine
        ⟨RuntimeProgressReturnState.lo false, p, T⟩ =
      ⟨RuntimeProgressReturnState.clearHi, p + 1, T'⟩ := by
  simp [step, runtimeProgressReturnMachine, moveHead, hread, hwrite]

private theorem progress_clear_step (T T' : List Bool) (p : Nat)
    (hwrite : writeAt T (p + 1) false = T') :
    step runtimeProgressReturnMachine
        ⟨RuntimeProgressReturnState.clearHi, p + 1, T⟩ =
      ⟨RuntimeProgressReturnState.done, p, T'⟩ := by
  simp [step, runtimeProgressReturnMachine, moveHead, hwrite]

/-- Enter reverse scanning from the low cell of the trailing hole. -/
theorem runtimeProgressReturn_enter (T : List Bool) (p : Nat) :
    run runtimeProgressReturnMachine 1
        ⟨runtimeProgressReturnMachine.start, p, T⟩ =
      ⟨RuntimeProgressReturnState.hi, p - 1, T⟩ := by
  rw [run_succ, run_zero]
  simp [step, runtimeProgressReturnMachine, moveHead]

/-- One non-marker pair is crossed right-to-left in two transitions. -/
theorem runtimeProgressReturn_nonmarker
    (pre tail : List Bool) (lo hi : Bool)
    (hnm : ¬ (lo = true ∧ hi = false)) :
    run runtimeProgressReturnMachine 2
        ⟨RuntimeProgressReturnState.hi, pre.length + 1,
          pre ++ [lo, hi] ++ tail⟩ =
      ⟨RuntimeProgressReturnState.hi, pre.length - 1,
        pre ++ [lo, hi] ++ tail⟩ := by
  rw [run_succ, run_succ, run_zero]
  cases lo <;> cases hi <;>
    simp_all [step, runtimeProgressReturnMachine, moveHead,
      List.getD_eq_getElem?_getD]

/-- Crossing a non-marker pair cannot enter `done` during either strict
prefix of its two-transition run. -/
theorem runtimeProgressReturn_nonmarker_no_early
    (pre tail : List Bool) (lo hi : Bool)
    (hnm : ¬ (lo = true ∧ hi = false)) :
    ∀ i < 2, runtimeProgressReturnMachine.halt
      (run runtimeProgressReturnMachine i
        ⟨RuntimeProgressReturnState.hi, pre.length + 1,
          pre ++ [lo, hi] ++ tail⟩).st = false := by
  intro i hi2
  interval_cases i <;>
    cases lo <;> cases hi <;>
      simp_all [run_succ, step, runtimeProgressReturnMachine,
        moveHead, List.getD_eq_getElem?_getD]

/-- Any nonempty list containing no `10` pair is crossed right-to-left by
one uninterrupted run, starting at the final high cell. -/
theorem runtimeProgressReturn_nonmarkerPairs
    (pre tail : List Bool) (ps : List (Bool × Bool))
    (hpos : 0 < ps.length)
    (hnm : ∀ p ∈ ps, ¬ (p.1 = true ∧ p.2 = false)) :
    run runtimeProgressReturnMachine (2 * ps.length)
        ⟨RuntimeProgressReturnState.hi,
          pre.length + 2 * ps.length - 1,
          pre ++ flattenPairs ps ++ tail⟩ =
      ⟨RuntimeProgressReturnState.hi, pre.length - 1,
        pre ++ flattenPairs ps ++ tail⟩ := by
  induction ps using List.reverseRecOn generalizing pre tail with
  | nil => simp at hpos
  | append_singleton ps p ih =>
      rcases p with ⟨lo, hi⟩
      have hp : ¬ (lo = true ∧ hi = false) := hnm (lo, hi) (by simp)
      by_cases hempty : ps = []
      · subst ps
        simpa [flattenPairs, List.append_assoc] using
          runtimeProgressReturn_nonmarker pre tail lo hi hp
      · have hpspos : 0 < ps.length := by
          cases ps with
          | nil => contradiction
          | cons => simp
        have hrest : ∀ q ∈ ps, ¬ (q.1 = true ∧ q.2 = false) := by
          intro q hq
          exact hnm q (by simp [hq])
        rw [show 2 * (ps ++ [(lo, hi)]).length = 2 + 2 * ps.length by
            simp; omega,
          run_add]
        have hlast := runtimeProgressReturn_nonmarker
          (pre ++ flattenPairs ps) tail lo hi hp
        have hlast' : run runtimeProgressReturnMachine 2
            ⟨RuntimeProgressReturnState.hi,
              pre.length + 2 * (ps ++ [(lo, hi)]).length - 1,
              pre ++ flattenPairs (ps ++ [(lo, hi)]) ++ tail⟩ =
          ⟨RuntimeProgressReturnState.hi,
            pre.length + 2 * ps.length - 1,
            pre ++ flattenPairs (ps ++ [(lo, hi)]) ++ tail⟩ := by
          simpa [flattenPairs_append, flattenPairs, flattenPairs_length,
            List.append_assoc] using hlast
        rw [show pre.length + (2 + 2 * ps.length) - 1 =
            pre.length + 2 * (ps ++ [(lo, hi)]).length - 1 by
          simp; omega,
          hlast']
        have hih := ih (pre := pre) (tail := [lo, hi] ++ tail) hpspos hrest
        simpa [flattenPairs_append, flattenPairs, List.append_assoc] using hih

/-- A nonempty aligned list of non-marker pairs cannot halt before its exact
right-to-left traversal clock. -/
theorem runtimeProgressReturn_nonmarkerPairs_no_early
    (pre tail : List Bool) (ps : List (Bool × Bool))
    (hpos : 0 < ps.length)
    (hnm : ∀ p ∈ ps, ¬ (p.1 = true ∧ p.2 = false)) :
    ∀ i < 2 * ps.length, runtimeProgressReturnMachine.halt
      (run runtimeProgressReturnMachine i
        ⟨RuntimeProgressReturnState.hi,
          pre.length + 2 * ps.length - 1,
          pre ++ flattenPairs ps ++ tail⟩).st = false := by
  induction ps using List.reverseRecOn generalizing pre tail with
  | nil => simp at hpos
  | append_singleton ps p ih =>
      rcases p with ⟨lo, hi⟩
      have hp : ¬ (lo = true ∧ hi = false) := hnm (lo, hi) (by simp)
      intro i hitotal
      by_cases hempty : ps = []
      · subst ps
        have hlocal := runtimeProgressReturn_nonmarker_no_early
          pre tail lo hi hp i
        simpa [flattenPairs, List.append_assoc] using hlocal (by simpa using hitotal)
      · have hpspos : 0 < ps.length := by
          cases ps with
          | nil => contradiction
          | cons => simp
        have hrest : ∀ q ∈ ps, ¬ (q.1 = true ∧ q.2 = false) := by
          intro q hq
          exact hnm q (by simp [hq])
        by_cases hi2 : i < 2
        · have hlocal := runtimeProgressReturn_nonmarker_no_early
            (pre ++ flattenPairs ps) tail lo hi hp i hi2
          simpa [flattenPairs_append, flattenPairs, flattenPairs_length,
            List.append_assoc] using hlocal
        · obtain ⟨j, rfl⟩ : ∃ j, i = 2 + j := by
            exact ⟨i - 2, by omega⟩
          rw [run_add]
          have hlast := runtimeProgressReturn_nonmarker
            (pre ++ flattenPairs ps) tail lo hi hp
          rw [show run runtimeProgressReturnMachine 2
              ⟨RuntimeProgressReturnState.hi,
                pre.length + 2 * (ps ++ [(lo, hi)]).length - 1,
                pre ++ flattenPairs (ps ++ [(lo, hi)]) ++ tail⟩ =
              ⟨RuntimeProgressReturnState.hi,
                pre.length + 2 * ps.length - 1,
                pre ++ flattenPairs (ps ++ [(lo, hi)]) ++ tail⟩ by
            simpa [flattenPairs_append, flattenPairs, flattenPairs_length,
              List.append_assoc] using hlast]
          have hj : j < 2 * ps.length := by simp at hitotal; omega
          have hih := ih (pre := pre) (tail := [lo, hi] ++ tail)
            hpspos hrest j hj
          simpa [flattenPairs_append, flattenPairs, List.append_assoc] using hih

/-- The canonical passed block contains no ordinary `10` progress word. -/
theorem passedSourceBlock_no_progressMark (bits : List Bool) :
    ∀ p ∈ passedSourceBlock bits,
      ¬ (p.1 = true ∧ p.2 = false) := by
  intro p hp
  have h := passedSourceBlock_noFresh bits p hp
  rcases p with ⟨lo, hi⟩
  cases lo <;> cases hi <;> simp_all

private theorem runtimeProgressReturn_marker_core (pre tail : List Bool) :
    run runtimeProgressReturnMachine 3
        ⟨RuntimeProgressReturnState.hi, pre.length + 1,
          pre ++ [true, false] ++ tail⟩ =
      ⟨RuntimeProgressReturnState.done, pre.length,
        pre ++ [false, false] ++ tail⟩ := by
  let T0 := pre ++ [true, false] ++ tail
  let T1 := pre ++ [false, false] ++ tail
  have hhi : T0[pre.length + 1]?.getD false = false := by simp [T0]
  have hlo : T0[pre.length]?.getD false = true := by simp [T0]
  have hw0 : writeAt T0 pre.length false = T1 := by
    simpa [T0, T1] using progress_write_lo pre tail
  have hw1 : writeAt T1 (pre.length + 1) false = T1 := by
    simpa [T1] using progress_write_hi pre tail
  change run runtimeProgressReturnMachine 3
      ⟨RuntimeProgressReturnState.hi, pre.length + 1, T0⟩ =
    ⟨RuntimeProgressReturnState.done, pre.length, T1⟩
  rw [show run runtimeProgressReturnMachine 3
      ⟨RuntimeProgressReturnState.hi, pre.length + 1, T0⟩ =
      step runtimeProgressReturnMachine
        (step runtimeProgressReturnMachine
          (step runtimeProgressReturnMachine
            ⟨RuntimeProgressReturnState.hi, pre.length + 1, T0⟩)) by rfl]
  rw [progress_hi_step T0 pre.length false hhi,
    progress_lo_marker_step T0 T1 pre.length hlo hw0,
    progress_clear_step T1 T1 pre.length hw1]

/-- The progress-marker branch first enters `done` on its third transition. -/
theorem runtimeProgressReturn_marker_no_early (pre tail : List Bool) :
    ∀ i < 3, runtimeProgressReturnMachine.halt
      (run runtimeProgressReturnMachine i
        ⟨RuntimeProgressReturnState.hi, pre.length + 1,
          pre ++ [true, false] ++ tail⟩).st = false := by
  intro i hi3
  interval_cases i <;>
    simp [run_succ, step, runtimeProgressReturnMachine, moveHead,
      List.getD_eq_getElem?_getD, writeAt]

/-- Starting at the trailing hole left cell, the fixed reverse controller
crosses the complete moved passed block and consumes the adjacent ordinary
progress word.  The endpoint is the consumed word's low cell. -/
theorem runtimeProgressReturn_passed_progress
    (pre tail bits : List Bool) :
    run runtimeProgressReturnMachine
        (1 + 2 * (passedSourceBlock bits).length + 3)
        ⟨runtimeProgressReturnMachine.start,
          pre.length + 2 + 2 * (passedSourceBlock bits).length,
          pre ++ [true, false] ++
            flattenPairs (passedSourceBlock bits) ++ [false, false] ++ tail⟩ =
      ⟨RuntimeProgressReturnState.done, pre.length,
        pre ++ [false, false] ++
          flattenPairs (passedSourceBlock bits) ++ [false, false] ++ tail⟩ := by
  let block := passedSourceBlock bits
  let T := pre ++ [true, false] ++ flattenPairs block ++
    [false, false] ++ tail
  rw [show 1 + 2 * (passedSourceBlock bits).length + 3 =
      1 + (2 * block.length + 3) by simp [block]; omega,
    run_add]
  have he := runtimeProgressReturn_enter T
    (pre.length + 2 + 2 * block.length)
  rw [show run runtimeProgressReturnMachine 1
      ⟨runtimeProgressReturnMachine.start,
        pre.length + 2 + 2 * block.length, T⟩ =
      ⟨RuntimeProgressReturnState.hi,
        pre.length + 2 + 2 * block.length - 1, T⟩ by
    simpa using he,
    run_add]
  have hb := runtimeProgressReturn_nonmarkerPairs
    (pre ++ [true, false]) ([false, false] ++ tail) block
    (by simp [block, passedSourceBlock])
    (by simpa [block] using passedSourceBlock_no_progressMark bits)
  rw [show run runtimeProgressReturnMachine (2 * block.length)
      ⟨RuntimeProgressReturnState.hi,
        pre.length + 2 + 2 * block.length - 1, T⟩ =
      ⟨RuntimeProgressReturnState.hi, pre.length + 1, T⟩ by
    simpa [T, block, flattenPairs_length, List.append_assoc] using hb]
  have hm := runtimeProgressReturn_marker_core pre
    (flattenPairs block ++ [false, false] ++ tail)
  simpa [T, block, List.append_assoc] using hm

/-- The complete reverse return first halts at its certified clock: entry,
the whole self-delimiting passed block, then the adjacent progress marker. -/
theorem runtimeProgressReturn_passed_progress_no_early
    (pre tail bits : List Bool) :
    ∀ i < 1 + 2 * (passedSourceBlock bits).length + 3,
      runtimeProgressReturnMachine.halt
        (run runtimeProgressReturnMachine i
          ⟨runtimeProgressReturnMachine.start,
            pre.length + 2 + 2 * (passedSourceBlock bits).length,
            pre ++ [true, false] ++
              flattenPairs (passedSourceBlock bits) ++
                [false, false] ++ tail⟩).st = false := by
  intro i hi
  let block := passedSourceBlock bits
  let T := pre ++ [true, false] ++ flattenPairs block ++
    [false, false] ++ tail
  by_cases hi1 : i < 1
  · have hiz : i = 0 := by omega
    subst i
    simp [runtimeProgressReturnMachine]
  · obtain ⟨j, rfl⟩ : ∃ j, i = 1 + j := by
      exact ⟨i - 1, by omega⟩
    rw [run_add]
    have he := runtimeProgressReturn_enter T
      (pre.length + 2 + 2 * block.length)
    rw [show run runtimeProgressReturnMachine 1
        ⟨runtimeProgressReturnMachine.start,
          pre.length + 2 + 2 * (passedSourceBlock bits).length,
          pre ++ [true, false] ++ flattenPairs (passedSourceBlock bits) ++
            [false, false] ++ tail⟩ =
        ⟨RuntimeProgressReturnState.hi,
          pre.length + 2 + 2 * block.length - 1, T⟩ by
      simpa [block, T] using he]
    by_cases hjblock : j < 2 * block.length
    · have hb := runtimeProgressReturn_nonmarkerPairs_no_early
        (pre ++ [true, false]) ([false, false] ++ tail) block
        (by simp [block, passedSourceBlock])
        (by simpa [block] using passedSourceBlock_no_progressMark bits)
        j hjblock
      simpa [T, block, flattenPairs_length, List.append_assoc] using hb
    · obtain ⟨k, rfl⟩ : ∃ k, j = 2 * block.length + k := by
        exact ⟨j - 2 * block.length, by omega⟩
      rw [run_add]
      have hb := runtimeProgressReturn_nonmarkerPairs
        (pre ++ [true, false]) ([false, false] ++ tail) block
        (by simp [block, passedSourceBlock])
        (by simpa [block] using passedSourceBlock_no_progressMark bits)
      rw [show run runtimeProgressReturnMachine (2 * block.length)
          ⟨RuntimeProgressReturnState.hi,
            pre.length + 2 + 2 * block.length - 1, T⟩ =
          ⟨RuntimeProgressReturnState.hi, pre.length + 1, T⟩ by
        simpa [T, block, flattenPairs_length, List.append_assoc] using hb]
      have hk : k < 3 := by
        simp [block] at hi
        omega
      have hm := runtimeProgressReturn_marker_no_early pre
        (flattenPairs block ++ [false, false] ++ tail) k hk
      simpa [T, block, List.append_assoc] using hm

/-- The ordinary `10` progress word is consumed to `00`; the controller
returns to its low cell and genuinely halts. -/
theorem runtimeProgressReturn_marker (pre tail : List Bool) :
    run runtimeProgressReturnMachine 3
        ⟨RuntimeProgressReturnState.hi, pre.length + 1,
          pre ++ [true, false] ++ tail⟩ =
      ⟨RuntimeProgressReturnState.done, pre.length,
        pre ++ [false, false] ++ tail⟩ := by
  exact runtimeProgressReturn_marker_core pre tail

/-- Consuming a progress word is left-safe even when the word begins at the
physical origin: the only left moves start from its high cell. -/
theorem runtimeProgressReturn_marker_leftSafe (pre tail : List Bool) :
    LeftSafeRun runtimeProgressReturnMachine
      ⟨RuntimeProgressReturnState.hi, pre.length + 1,
        pre ++ [true, false] ++ tail⟩ 3 := by
  intro i hi _ hmove
  interval_cases i <;>
    simp [run_succ, step, runtimeProgressReturnMachine, moveHead,
      List.getD_eq_getElem?_getD, writeAt] at hmove ⊢

/-! ## Fixed exhaustion branch -/

inductive RuntimeProgressExhaustState
  | start | check | clearSentinelLo | more | final
  deriving DecidableEq, Fintype

/-- Inspect the pair immediately left of a freshly consumed `00` hole.
An ordinary remaining `10` has high bit zero; the final `01` sentinel has
high bit one. -/
def runtimeProgressExhaustMachine : Machine where
  State := RuntimeProgressExhaustState
  fin := inferInstance
  dec := inferInstance
  start := .start
  halt := fun s => decide (s = .more ∨ s = .final)
  δ := fun s b =>
    match s with
    | .start => (.check, none, 0)
    | .check =>
        if b then (.clearSentinelLo, some false, 0)
        else (.more, none, 1)
    | .clearSentinelLo => (.final, some false, 1)
    | .more => (.more, none, 2)
    | .final => (.final, none, 2)
  accept := fun s => decide (s = .final)

/-- A preceding ordinary mark is detected and the head returns to the
consumed hole, ready for the next universal forward pass. -/
theorem runtimeProgressExhaust_more (pre tail : List Bool) :
    run runtimeProgressExhaustMachine 2
        ⟨runtimeProgressExhaustMachine.start, pre.length + 2,
          pre ++ [true, false, false, false] ++ tail⟩ =
      ⟨RuntimeProgressExhaustState.more, pre.length + 2,
        pre ++ [true, false, false, false] ++ tail⟩ := by
  rw [run_succ, run_succ, run_zero]
  simp [step, runtimeProgressExhaustMachine, moveHead,
    List.getD_eq_getElem?_getD]

/-- With no progress word remaining, the adjacent `01` sentinel is consumed
to `00` and the controller genuinely halts in its final state. -/
theorem runtimeProgressExhaust_final (pre tail : List Bool) :
    run runtimeProgressExhaustMachine 3
        ⟨runtimeProgressExhaustMachine.start, pre.length + 2,
          pre ++ [false, true, false, false] ++ tail⟩ =
      ⟨RuntimeProgressExhaustState.final, pre.length + 1,
        pre ++ [false, false, false, false] ++ tail⟩ := by
  rw [run_succ, run_succ, run_succ, run_zero]
  simp [step, runtimeProgressExhaustMachine, moveHead,
    List.getD_eq_getElem?_getD, writeAt]

theorem runtimeProgressExhaust_more_leftSafe (pre tail : List Bool) :
    LeftSafeRun runtimeProgressExhaustMachine
      ⟨runtimeProgressExhaustMachine.start, pre.length + 2,
        pre ++ [true, false, false, false] ++ tail⟩ 2 := by
  intro i hi _ hmove
  interval_cases i <;>
    simp [run_succ, step, runtimeProgressExhaustMachine, moveHead,
      List.getD_eq_getElem?_getD] at hmove ⊢

theorem runtimeProgressExhaust_final_leftSafe (pre tail : List Bool) :
    LeftSafeRun runtimeProgressExhaustMachine
      ⟨runtimeProgressExhaustMachine.start, pre.length + 2,
        pre ++ [false, true, false, false] ++ tail⟩ 3 := by
  intro i hi _ hmove
  interval_cases i <;>
    simp [run_succ, step, runtimeProgressExhaustMachine, moveHead,
      List.getD_eq_getElem?_getD, writeAt] at hmove ⊢

@[simp] theorem runtimeProgressExhaust_more_halts :
    runtimeProgressExhaustMachine.halt RuntimeProgressExhaustState.more = true := by
  simp [runtimeProgressExhaustMachine]

@[simp] theorem runtimeProgressExhaust_final_halts :
    runtimeProgressExhaustMachine.halt RuntimeProgressExhaustState.final = true := by
  simp [runtimeProgressExhaustMachine]

@[simp] theorem runtimeProgressReturn_done_halts :
    runtimeProgressReturnMachine.halt RuntimeProgressReturnState.done = true := by
  simp [runtimeProgressReturnMachine]

#print axioms runtimeProgressReturn_enter
#print axioms runtimeProgressReturn_nonmarker
#print axioms runtimeProgressReturn_nonmarkerPairs
#print axioms passedSourceBlock_no_progressMark
#print axioms runtimeProgressReturn_passed_progress
#print axioms runtimeProgressReturn_marker
#print axioms runtimeProgressReturn_nonmarker_no_early
#print axioms runtimeProgressReturn_nonmarkerPairs_no_early
#print axioms runtimeProgressReturn_marker_no_early
#print axioms runtimeProgressReturn_passed_progress_no_early
#print axioms runtimeProgressReturn_marker_leftSafe
#print axioms runtimeProgressExhaust_more
#print axioms runtimeProgressExhaust_final
#print axioms runtimeProgressExhaust_more_leftSafe
#print axioms runtimeProgressExhaust_final_leftSafe

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeProgressReturn
