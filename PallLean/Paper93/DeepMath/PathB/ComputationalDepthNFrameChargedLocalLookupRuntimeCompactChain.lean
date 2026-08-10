import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeContinuationDispatch

/-!
# Charged local lookup: certified marked-compaction bubble chains

This module isolates the physical marked-to-compact shifter primitives from
the large round-transition file.  A chain is a finite sequence of genuine
seven-step local machine runs; every link includes its exact tape rewrite and
its own physical left-boundary certificate.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeCompactChain

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeLeftSafety
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeContinuationDispatch
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect

private theorem compact_write0 (pre tail : List Bool)
    (a b c d w : Bool) :
    writeAt (pre ++ [a, b, c, d] ++ tail) pre.length w =
      pre ++ [w, b, c, d] ++ tail := by
  rw [PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr.writeAt_of_lt
    w (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)]
  simp

private theorem compact_write1 (pre tail : List Bool)
    (a b c d w : Bool) :
    writeAt (pre ++ [a, b, c, d] ++ tail) (pre.length + 1) w =
      pre ++ [a, w, c, d] ++ tail := by
  rw [PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr.writeAt_of_lt
    w (by simp)]
  simp

private theorem compact_write2 (pre tail : List Bool)
    (a b c d w : Bool) :
    writeAt (pre ++ [a, b, c, d] ++ tail) (pre.length + 2) w =
      pre ++ [a, b, w, d] ++ tail := by
  rw [PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr.writeAt_of_lt
    w (by simp)]
  simp

private theorem compact_write2' (pre tail : List Bool)
    (a b c d w : Bool) :
    writeAt (pre ++ [a, b, c, d] ++ tail) (pre.length + 1 + 1) w =
      pre ++ [a, b, w, d] ++ tail := by
  simpa only [show pre.length + 1 + 1 = pre.length + 2 by omega] using
    compact_write2 pre tail a b c d w

private theorem compact_write3 (pre tail : List Bool)
    (a b c d w : Bool) :
    writeAt (pre ++ [a, b, c, d] ++ tail) (pre.length + 3) w =
      pre ++ [a, b, c, w] ++ tail := by
  rw [PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr.writeAt_of_lt
    w (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)]
  simp

private theorem compact_write3' (pre tail : List Bool)
    (a b c d w : Bool) :
    writeAt (pre ++ [a, b, c, d] ++ tail) (pre.length + 1 + 1 + 1) w =
      pre ++ [a, b, c, w] ++ tail := by
  simpa only [show pre.length + 1 + 1 + 1 = pre.length + 3 by omega] using
    compact_write3 pre tail a b c d w

private theorem compact_get2 (pre tail : List Bool) (a b c d : Bool) :
    (pre ++ [a, b, c, d] ++ tail).getD (pre.length + 1 + 1) false = c := by
  rw [show pre.length + 1 + 1 = pre.length + 2 by omega]
  rw [getD_append_middle pre [a, b, c, d] tail 2 (by simp)]
  simp

private theorem compact_get3 (pre tail : List Bool) (a b c d : Bool) :
    (pre ++ [a, b, c, d] ++ tail).getD
        (pre.length + 1 + 1 + 1) false = d := by
  rw [show pre.length + 1 + 1 + 1 = pre.length + 3 by omega]
  rw [getD_append_middle pre [a, b, c, d] tail 3 (by simp)]
  simp

private theorem compact_getElem2 (pre tail : List Bool) (a b c d : Bool) :
    ((pre ++ [a, b, c, d] ++ tail)[pre.length + 1 + 1]?).getD false = c := by
  rw [← List.getD_eq_getElem?_getD]
  exact compact_get2 pre tail a b c d

private theorem compact_getElem3 (pre tail : List Bool) (a b c d : Bool) :
    ((pre ++ [a, b, c, d] ++ tail)[pre.length + 1 + 1 + 1]?).getD false = d := by
  rw [← List.getD_eq_getElem?_getD]
  exact compact_get3 pre tail a b c d

private theorem compact_bubble_after_clear (pre tail : List Bool)
    (lo hi : Bool) :
    writeAt
        (writeAt
          (writeAt (pre ++ [false, false, lo, false] ++ tail)
            (pre.length + 1 + 1) false)
          (pre.length + 1) hi)
        pre.length lo =
      pre ++ [lo, hi, false, false] ++ tail := by
  rw [compact_write2', compact_write1, compact_write0]

/-- One exact local compaction step: an aligned `00` hole moves right across
one arbitrary encoded pair. -/
theorem runtimeCompactBubble_run (pre tail : List Bool) (lo hi : Bool) :
    run runtimeCompactBubbleMachine 7
        ⟨runtimeCompactBubbleMachine.start, pre.length,
          pre ++ [false, false, lo, hi] ++ tail⟩ =
      ⟨RuntimeCompactBubbleState.done, pre.length,
        pre ++ [lo, hi, false, false] ++ tail⟩ := by
  let T0 := pre ++ [false, false, lo, hi] ++ tail
  let T1 := pre ++ [false, false, lo, false] ++ tail
  let T2 := pre ++ [false, false, false, false] ++ tail
  let T3 := pre ++ [false, hi, false, false] ++ tail
  let T4 := pre ++ [lo, hi, false, false] ++ tail
  have h1 : step runtimeCompactBubbleMachine
      ⟨RuntimeCompactBubbleState.holeLo, pre.length, T0⟩ =
      ⟨RuntimeCompactBubbleState.holeHi, pre.length + 1, T0⟩ := by
    simp [step, runtimeCompactBubbleMachine, moveHead]
  have h2 : step runtimeCompactBubbleMachine
      ⟨RuntimeCompactBubbleState.holeHi, pre.length + 1, T0⟩ =
      ⟨RuntimeCompactBubbleState.readLo, pre.length + 2, T0⟩ := by
    simp [step, runtimeCompactBubbleMachine, moveHead]
  have h3 : step runtimeCompactBubbleMachine
      ⟨RuntimeCompactBubbleState.readLo, pre.length + 2, T0⟩ =
      ⟨RuntimeCompactBubbleState.readHi lo, pre.length + 3, T0⟩ := by
    simp only [step, runtimeCompactBubbleMachine, moveHead, Machine.δ,
      Machine.halt, Cfg.st, Cfg.hd, Cfg.tp]
    rw [List.getD_eq_getElem?_getD, compact_getElem2]
    simp
  have h4 : step runtimeCompactBubbleMachine
      ⟨RuntimeCompactBubbleState.readHi lo, pre.length + 3, T0⟩ =
      ⟨RuntimeCompactBubbleState.clearLo lo hi, pre.length + 2, T1⟩ := by
    simp only [step, runtimeCompactBubbleMachine, moveHead, Machine.δ,
      Machine.halt, Cfg.st, Cfg.hd, Cfg.tp]
    rw [List.getD_eq_getElem?_getD, compact_getElem3, compact_write3']
    simp [T0, T1]
  have h5 : step runtimeCompactBubbleMachine
      ⟨RuntimeCompactBubbleState.clearLo lo hi, pre.length + 2, T1⟩ =
      ⟨RuntimeCompactBubbleState.writeHi lo hi, pre.length + 1, T2⟩ := by
    simp only [step, runtimeCompactBubbleMachine, moveHead, Machine.δ,
      Machine.halt, Cfg.st, Cfg.hd, Cfg.tp]
    rw [compact_write2']
    simp [T1, T2]
  have h6 : step runtimeCompactBubbleMachine
      ⟨RuntimeCompactBubbleState.writeHi lo hi, pre.length + 1, T2⟩ =
      ⟨RuntimeCompactBubbleState.writeLo lo, pre.length, T3⟩ := by
    simp only [step, runtimeCompactBubbleMachine, moveHead, Machine.δ,
      Machine.halt, Cfg.st, Cfg.hd, Cfg.tp]
    rw [compact_write1]
    simp [T2, T3]
  have h7 : step runtimeCompactBubbleMachine
      ⟨RuntimeCompactBubbleState.writeLo lo, pre.length, T3⟩ =
      ⟨RuntimeCompactBubbleState.done, pre.length, T4⟩ := by
    simp only [step, runtimeCompactBubbleMachine, moveHead, Machine.δ,
      Machine.halt, Cfg.st, Cfg.hd, Cfg.tp]
    rw [compact_write0]
    simp [T3, T4]
  change run runtimeCompactBubbleMachine 7
      ⟨RuntimeCompactBubbleState.holeLo, pre.length, T0⟩ = _
  rw [show 7 = 6 + 1 by omega, run_succ,
    show 6 = 5 + 1 by omega, run_succ,
    show 5 = 4 + 1 by omega, run_succ,
    show 4 = 3 + 1 by omega, run_succ,
    show 3 = 2 + 1 by omega, run_succ,
    show 2 = 1 + 1 by omega, run_succ,
    show 1 = 0 + 1 by omega, run_succ, run_zero,
    h1, h2, h3, h4, h5, h6, h7]

set_option maxHeartbeats 4000000 in
/-- Every local bubble run stays to the right of the physical boundary. -/
theorem runtimeCompactBubble_leftSafe (pre tail : List Bool) (lo hi : Bool) :
    LeftSafeRun runtimeCompactBubbleMachine
      ⟨runtimeCompactBubbleMachine.start, pre.length,
        pre ++ [false, false, lo, hi] ++ tail⟩ 7 := by
  intro i hlt hlive hmove
  interval_cases i <;>
    cases lo <;> cases hi <;>
    simp [run_succ, step, runtimeCompactBubbleMachine, moveHead, writeAt]
      at hlive hmove ⊢ <;> omega

/-- A certified left-to-right pass across an arbitrary aligned pair list. -/
inductive RuntimeCompactBubbleChain (tail : List Bool) :
    List Bool → List (Bool × Bool) → Prop
  | nil (pre : List Bool) : RuntimeCompactBubbleChain tail pre []
  | cons (pre : List Bool) (lo hi : Bool) (ps : List (Bool × Bool))
      (hrun :
        run runtimeCompactBubbleMachine 7
            ⟨runtimeCompactBubbleMachine.start, pre.length,
              pre ++ [false, false, lo, hi] ++ flattenPairs ps ++ tail⟩ =
          ⟨RuntimeCompactBubbleState.done, pre.length,
            pre ++ [lo, hi, false, false] ++ flattenPairs ps ++ tail⟩)
      (hsafe :
        LeftSafeRun runtimeCompactBubbleMachine
          ⟨runtimeCompactBubbleMachine.start, pre.length,
            pre ++ [false, false, lo, hi] ++ flattenPairs ps ++ tail⟩ 7)
      (hrest : RuntimeCompactBubbleChain tail (pre ++ [lo, hi]) ps) :
      RuntimeCompactBubbleChain tail pre ((lo, hi) :: ps)

/-- No correctness, endpoint, or safety witness is required to build the
finite bubble chain. -/
theorem runtimeCompactBubble_chain
    (pre tail : List Bool) (ps : List (Bool × Bool)) :
    RuntimeCompactBubbleChain tail pre ps := by
  induction ps generalizing pre with
  | nil => exact .nil pre
  | cons p ps ih =>
      rcases p with ⟨lo, hi⟩
      apply RuntimeCompactBubbleChain.cons pre lo hi ps
      · simpa [List.append_assoc] using
          runtimeCompactBubble_run pre (flattenPairs ps ++ tail) lo hi
      · simpa [List.append_assoc] using
          runtimeCompactBubble_leftSafe pre (flattenPairs ps ++ tail) lo hi
      · exact ih (pre := pre ++ [lo, hi])

/-! ## Restart-free bubble passes -/

/-- Looping form of the bubble primitive.  Unlike the halting diagnostic
primitive, an eight-step round finishes in `holeLo` at the newly-created hole,
ready to consume the next workspace pair without a state or head restart. -/
inductive RuntimeCompactBubbleLoopState
  | holeLo | holeHi | readLo | readHi (lo : Bool)
  | clearLo (lo hi : Bool) | writeHi (lo hi : Bool)
  | writeLo (lo : Bool) | advance
  deriving DecidableEq, Fintype

def runtimeCompactBubbleLoopMachine : Machine where
  State := RuntimeCompactBubbleLoopState
  fin := inferInstance
  dec := inferInstance
  start := .holeLo
  halt := fun _ => false
  δ := fun s b =>
    match s with
    | .holeLo => (.holeHi, none, 1)
    | .holeHi => (.readLo, none, 1)
    | .readLo => (.readHi b, none, 1)
    | .readHi lo => (.clearLo lo b, some false, 0)
    | .clearLo lo hi => (.writeHi lo hi, some false, 0)
    | .writeHi lo hi => (.writeLo lo, some hi, 0)
    | .writeLo lo => (.advance, some lo, 1)
    | .advance => (.holeLo, none, 1)
  accept := fun _ => false

/-- One restart-free bubble round ends at the moved hole. -/
theorem runtimeCompactBubbleLoop_round
    (pre tail : List Bool) (lo hi : Bool) :
    run runtimeCompactBubbleLoopMachine 8
        ⟨runtimeCompactBubbleLoopMachine.start, pre.length,
          pre ++ [false, false, lo, hi] ++ tail⟩ =
      ⟨runtimeCompactBubbleLoopMachine.start, pre.length + 2,
        pre ++ [lo, hi, false, false] ++ tail⟩ := by
  let T0 := pre ++ [false, false, lo, hi] ++ tail
  let T1 := pre ++ [false, false, lo, false] ++ tail
  let T2 := pre ++ [false, false, false, false] ++ tail
  let T3 := pre ++ [false, hi, false, false] ++ tail
  let T4 := pre ++ [lo, hi, false, false] ++ tail
  have h1 : step runtimeCompactBubbleLoopMachine
      ⟨RuntimeCompactBubbleLoopState.holeLo, pre.length, T0⟩ =
      ⟨RuntimeCompactBubbleLoopState.holeHi, pre.length + 1, T0⟩ := by
    simp [step, runtimeCompactBubbleLoopMachine, moveHead]
  have h2 : step runtimeCompactBubbleLoopMachine
      ⟨RuntimeCompactBubbleLoopState.holeHi, pre.length + 1, T0⟩ =
      ⟨RuntimeCompactBubbleLoopState.readLo, pre.length + 2, T0⟩ := by
    simp [step, runtimeCompactBubbleLoopMachine, moveHead]
  have h3 : step runtimeCompactBubbleLoopMachine
      ⟨RuntimeCompactBubbleLoopState.readLo, pre.length + 2, T0⟩ =
      ⟨RuntimeCompactBubbleLoopState.readHi lo, pre.length + 3, T0⟩ := by
    simp only [step, runtimeCompactBubbleLoopMachine, moveHead]
    rw [List.getD_eq_getElem?_getD, compact_getElem2]
    simp
  have h4 : step runtimeCompactBubbleLoopMachine
      ⟨RuntimeCompactBubbleLoopState.readHi lo, pre.length + 3, T0⟩ =
      ⟨RuntimeCompactBubbleLoopState.clearLo lo hi, pre.length + 2, T1⟩ := by
    simp only [step, runtimeCompactBubbleLoopMachine, moveHead]
    rw [List.getD_eq_getElem?_getD, compact_getElem3, compact_write3']
    simp [T0, T1]
  have h5 : step runtimeCompactBubbleLoopMachine
      ⟨RuntimeCompactBubbleLoopState.clearLo lo hi, pre.length + 2, T1⟩ =
      ⟨RuntimeCompactBubbleLoopState.writeHi lo hi, pre.length + 1, T2⟩ := by
    simp only [step, runtimeCompactBubbleLoopMachine, moveHead]
    rw [compact_write2']
    simp [T1, T2]
  have h6 : step runtimeCompactBubbleLoopMachine
      ⟨RuntimeCompactBubbleLoopState.writeHi lo hi, pre.length + 1, T2⟩ =
      ⟨RuntimeCompactBubbleLoopState.writeLo lo, pre.length, T3⟩ := by
    simp only [step, runtimeCompactBubbleLoopMachine, moveHead]
    rw [compact_write1]
    simp [T2, T3]
  have h7 : step runtimeCompactBubbleLoopMachine
      ⟨RuntimeCompactBubbleLoopState.writeLo lo, pre.length, T3⟩ =
      ⟨RuntimeCompactBubbleLoopState.advance, pre.length + 1, T4⟩ := by
    simp only [step, runtimeCompactBubbleLoopMachine, moveHead]
    rw [compact_write0]
    simp [T3, T4]
  have h8 : step runtimeCompactBubbleLoopMachine
      ⟨RuntimeCompactBubbleLoopState.advance, pre.length + 1, T4⟩ =
      ⟨RuntimeCompactBubbleLoopState.holeLo, pre.length + 2, T4⟩ := by
    simp [step, runtimeCompactBubbleLoopMachine, moveHead]
  change run runtimeCompactBubbleLoopMachine 8
      ⟨RuntimeCompactBubbleLoopState.holeLo, pre.length, T0⟩ = _
  rw [show 8 = 7 + 1 by omega, run_succ,
    show 7 = 6 + 1 by omega, run_succ,
    show 6 = 5 + 1 by omega, run_succ,
    show 5 = 4 + 1 by omega, run_succ,
    show 4 = 3 + 1 by omega, run_succ,
    show 3 = 2 + 1 by omega, run_succ,
    show 2 = 1 + 1 by omega, run_succ,
    show 1 = 0 + 1 by omega, run_succ, run_zero,
    h1, h2, h3, h4, h5, h6, h7, h8]
  simp [runtimeCompactBubbleLoopMachine, T4]

/-- An entire workspace pass is one uninterrupted physical run. -/
theorem runtimeCompactBubbleLoop_run
    (pre tail : List Bool) (ps : List (Bool × Bool)) :
    run runtimeCompactBubbleLoopMachine (8 * ps.length)
        ⟨runtimeCompactBubbleLoopMachine.start, pre.length,
          pre ++ [false, false] ++ flattenPairs ps ++ tail⟩ =
      ⟨runtimeCompactBubbleLoopMachine.start, pre.length + 2 * ps.length,
        pre ++ flattenPairs ps ++ [false, false] ++ tail⟩ := by
  induction ps generalizing pre with
  | nil => simp [runtimeCompactBubbleLoopMachine, flattenPairs]
  | cons p ps ih =>
      rcases p with ⟨lo, hi⟩
      have hround : run runtimeCompactBubbleLoopMachine 8
          ⟨runtimeCompactBubbleLoopMachine.start, pre.length,
            pre ++ [false, false] ++ flattenPairs ((lo, hi) :: ps) ++ tail⟩ =
        ⟨runtimeCompactBubbleLoopMachine.start, pre.length + 2,
          pre ++ [lo, hi, false, false] ++ flattenPairs ps ++ tail⟩ := by
        simpa [flattenPairs, List.append_assoc] using
          runtimeCompactBubbleLoop_round pre (flattenPairs ps ++ tail) lo hi
      rw [show 8 * (((lo, hi) :: ps).length) = 8 + 8 * ps.length by
          simp only [List.length_cons]
          omega,
        run_add, hround]
      have hih := ih (pre := pre ++ [lo, hi])
      convert hih using 1 <;>
        simp [flattenPairs, List.append_assoc, flattenPairs_length] <;> omega

set_option maxHeartbeats 4000000 in
/-- The uninterrupted workspace pass is physically left-safe. -/
theorem runtimeCompactBubbleLoop_leftSafe
    (pre tail : List Bool) (ps : List (Bool × Bool)) :
    LeftSafeRun runtimeCompactBubbleLoopMachine
      ⟨runtimeCompactBubbleLoopMachine.start, pre.length,
        pre ++ [false, false] ++ flattenPairs ps ++ tail⟩
      (8 * ps.length) := by
  induction ps generalizing pre with
  | nil => simp [LeftSafeRun]
  | cons p ps ih =>
      rcases p with ⟨lo, hi⟩
      have hround : run runtimeCompactBubbleLoopMachine 8
          ⟨runtimeCompactBubbleLoopMachine.start, pre.length,
            pre ++ [false, false] ++ flattenPairs ((lo, hi) :: ps) ++ tail⟩ =
        ⟨runtimeCompactBubbleLoopMachine.start, pre.length + 2,
          pre ++ [lo, hi, false, false] ++ flattenPairs ps ++ tail⟩ := by
        simpa [flattenPairs, List.append_assoc] using
          runtimeCompactBubbleLoop_round pre (flattenPairs ps ++ tail) lo hi
      rw [show 8 * (((lo, hi) :: ps).length) = 8 + 8 * ps.length by
        simp only [List.length_cons]
        omega]
      apply leftSafeRun_add
      · intro i hlt hlive hmove
        interval_cases i <;>
          simp [run_succ, step, runtimeCompactBubbleLoopMachine, moveHead,
            writeAt] at hlive hmove ⊢ <;> omega
      · rw [hround]
        simpa [flattenPairs, List.append_assoc] using
          ih (pre := pre ++ [lo, hi])

/-! ## Physical between-pass rewind -/

/-- Clocked no-write rewind controller. -/
def runtimeCompactRewindMachine : Machine where
  State := Unit
  fin := inferInstance
  dec := inferInstance
  start := ()
  halt := fun _ => false
  δ := fun _ _ => ((), none, 0)
  accept := fun _ => false

/-- Rewinding `n` cells from `pre.length + n` returns exactly to the end of
`pre` and preserves the whole tape. -/
theorem runtimeCompactRewind_run
    (pre tail : List Bool) (n : Nat) :
    run runtimeCompactRewindMachine n
        ⟨runtimeCompactRewindMachine.start, pre.length + n, pre ++ tail⟩ =
      ⟨(), pre.length, pre ++ tail⟩ := by
  induction n with
  | zero => simp [runtimeCompactRewindMachine]
  | succ n ih =>
      rw [show n + 1 = 1 + n by omega, run_add]
      have hstep : run runtimeCompactRewindMachine 1
          ⟨runtimeCompactRewindMachine.start, pre.length + (1 + n),
            pre ++ tail⟩ =
        ⟨(), pre.length + n, pre ++ tail⟩ := by
        rw [run_succ, run_zero]
        simp [step, runtimeCompactRewindMachine, moveHead]
        omega
      rw [hstep]
      simpa [runtimeCompactRewindMachine] using ih

/-- The exact rewind is physically left-safe: every left move begins at a
strictly positive head. -/
theorem runtimeCompactRewind_leftSafe
    (pre tail : List Bool) (n : Nat) :
    LeftSafeRun runtimeCompactRewindMachine
      ⟨runtimeCompactRewindMachine.start, pre.length + n, pre ++ tail⟩ n := by
  induction n with
  | zero => simp [LeftSafeRun]
  | succ n ih =>
      rw [show n + 1 = 1 + n by omega]
      apply leftSafeRun_add
      · exact leftSafeRun_one_of_positive (by simp)
      · have hstep : run runtimeCompactRewindMachine 1
            ⟨runtimeCompactRewindMachine.start, pre.length + (1 + n),
              pre ++ tail⟩ =
          ⟨(), pre.length + n, pre ++ tail⟩ := by
            rw [run_succ, run_zero]
            simp [step, runtimeCompactRewindMachine, moveHead]
            omega
        rw [hstep]
        simpa [runtimeCompactRewindMachine] using ih

structure RuntimeCompactPassRewindCertificate
    (pre : List Bool) (workspace : List (Bool × Bool))
    (tail : List Bool) : Prop where
  passRun :
    run runtimeCompactBubbleLoopMachine (8 * workspace.length)
        ⟨runtimeCompactBubbleLoopMachine.start, pre.length + 2,
          pre ++ [false, false, false, false] ++
            flattenPairs workspace ++ tail⟩ =
      ⟨runtimeCompactBubbleLoopMachine.start,
        pre.length + 2 + 2 * workspace.length,
        pre ++ [false, false] ++ flattenPairs workspace ++
          [false, false] ++ tail⟩
  passSafe : LeftSafeRun runtimeCompactBubbleLoopMachine
    ⟨runtimeCompactBubbleLoopMachine.start, pre.length + 2,
      pre ++ [false, false, false, false] ++ flattenPairs workspace ++ tail⟩
    (8 * workspace.length)
  rewindRun :
    run runtimeCompactRewindMachine (2 * (workspace.length + 1))
        ⟨runtimeCompactRewindMachine.start,
          pre.length + 2 + 2 * workspace.length,
          pre ++ [false, false] ++ flattenPairs workspace ++
            [false, false] ++ tail⟩ =
      ⟨(), pre.length,
        pre ++ [false, false] ++ flattenPairs workspace ++
          [false, false] ++ tail⟩
  rewindSafe : LeftSafeRun runtimeCompactRewindMachine
    ⟨runtimeCompactRewindMachine.start,
      pre.length + 2 + 2 * workspace.length,
      pre ++ [false, false] ++ flattenPairs workspace ++
        [false, false] ++ tail⟩ (2 * (workspace.length + 1))

/-- One complete nonfinal compaction pass followed by its physical rewind
lands exactly on the preceding hole. -/
theorem runtimeCompactPassRewind_certificate
    (pre tail : List Bool) (workspace : List (Bool × Bool)) :
    RuntimeCompactPassRewindCertificate pre workspace tail := by
  let shifted := [false, false] ++ flattenPairs workspace ++
    [false, false] ++ tail
  have hpass := runtimeCompactBubbleLoop_run
    (pre ++ [false, false]) tail workspace
  have hpassSafe := runtimeCompactBubbleLoop_leftSafe
    (pre ++ [false, false]) tail workspace
  have hrewind := runtimeCompactRewind_run pre shifted
    (2 * (workspace.length + 1))
  have hrewindSafe := runtimeCompactRewind_leftSafe pre shifted
    (2 * (workspace.length + 1))
  constructor
  · simpa [List.append_assoc, flattenPairs_length] using hpass
  · simpa [List.append_assoc] using hpassSafe
  · simpa [shifted, runtimeCompactRewindMachine, List.append_assoc,
      Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrewind
  · simpa [shifted, runtimeCompactRewindMachine, List.append_assoc,
      Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrewindSafe

/-! ## Complete physical pass schedule -/

/-- A physical schedule for moving every cleared stale pair across the
workspace.  `one` performs the final pass without rewinding; `more` performs
one pass+rewind bridge and continues with one fewer leading hole and one more
trailing hole. -/
inductive RuntimeCompactAllPasses
    (retained : List Bool) (workspace : List (Bool × Bool)) :
    List Bool → Nat → Prop
  | one (tail : List Bool)
      (finalRun :
        run runtimeCompactBubbleLoopMachine (8 * workspace.length)
            ⟨runtimeCompactBubbleLoopMachine.start, retained.length,
              retained ++ [false, false] ++ flattenPairs workspace ++ tail⟩ =
          ⟨runtimeCompactBubbleLoopMachine.start,
            retained.length + 2 * workspace.length,
            retained ++ flattenPairs workspace ++ [false, false] ++ tail⟩)
      (finalSafe : LeftSafeRun runtimeCompactBubbleLoopMachine
        ⟨runtimeCompactBubbleLoopMachine.start, retained.length,
          retained ++ [false, false] ++ flattenPairs workspace ++ tail⟩
        (8 * workspace.length)) :
      RuntimeCompactAllPasses retained workspace tail 1
  | more (tail : List Bool) (n : Nat)
      (bridge : RuntimeCompactPassRewindCertificate
        (retained ++ flattenPairs (List.replicate n (false, false)))
        workspace tail)
      (rest : RuntimeCompactAllPasses retained workspace
        ([false, false] ++ tail) (n + 1)) :
      RuntimeCompactAllPasses retained workspace tail (n + 2)

/-- Every positive number of cleared stale pairs has a complete physical
pass schedule, with rewind omitted exactly after the final pass. -/
theorem runtimeCompactAllPasses_certificate
    (retained tail : List Bool) (workspace : List (Bool × Bool))
    {k : Nat} (hk : 0 < k) :
    RuntimeCompactAllPasses retained workspace tail k := by
  induction k generalizing tail with
  | zero => omega
  | succ k ih =>
      cases k with
      | zero =>
          exact .one tail
            (runtimeCompactBubbleLoop_run retained tail workspace)
            (runtimeCompactBubbleLoop_leftSafe retained tail workspace)
      | succ n =>
          exact .more tail n
            (runtimeCompactPassRewind_certificate
              (retained ++ flattenPairs (List.replicate n (false, false)))
              tail workspace)
            (ih (tail := [false, false] ++ tail) (by omega))

/-- Scheduled specialization: the exact `d + 3` stale pairs produced by the
marked clear phase all cross the workspace, and the final pass does not
rewind away from the compact archive-side endpoint. -/
theorem runtimeMarkedAllPasses_certificate
    (retained tail : List Bool) (workspace : List (Bool × Bool)) (d : Nat) :
    RuntimeCompactAllPasses retained workspace tail (d + 3) := by
  exact runtimeCompactAllPasses_certificate retained tail workspace (by omega)

/-- Repeated marked-compaction passes.  At stage `n + 1`, the rightmost
remaining `00` hole is bubbled across the whole workspace pair list.  The
resulting hole is appended to the protected tail, and the construction
continues with the remaining `n` holes. -/
inductive RuntimeCompactBubblePasses
    (retained : List Bool) (workspace : List (Bool × Bool)) :
    List Bool → Nat → Prop
  | zero (tail : List Bool) :
      RuntimeCompactBubblePasses retained workspace tail 0
  | succ (tail : List Bool) (n : Nat)
      (hpass : RuntimeCompactBubbleChain tail
        (retained ++ flattenPairs (List.replicate n (false, false))) workspace)
      (hrest : RuntimeCompactBubblePasses retained workspace
        ([false, false] ++ tail) n) :
      RuntimeCompactBubblePasses retained workspace tail (n + 1)

/-- Every finite aligned stale region, once cleared to `00` pairs, admits a
complete sequence of certified workspace-shifting passes.  No run, endpoint,
or left-safety witness is supplied by the caller. -/
theorem runtimeCompactBubble_passes
    (retained tail : List Bool) (workspace : List (Bool × Bool)) (n : Nat) :
    RuntimeCompactBubblePasses retained workspace tail n := by
  induction n generalizing tail with
  | zero => exact .zero tail
  | succ n ih =>
      exact .succ tail n
        (runtimeCompactBubble_chain
          (retained ++ flattenPairs (List.replicate n (false, false)))
          tail workspace)
        (ih (tail := [false, false] ++ tail))

/-! ## Physical stale-pair clearing -/

/-- Two-step primitive that destructively clears one arbitrary aligned pair
and returns to its low cell. -/
inductive RuntimeCompactClearState
  | lo | hi | done
  deriving DecidableEq, Fintype

def runtimeCompactClearMachine : Machine where
  State := RuntimeCompactClearState
  fin := inferInstance
  dec := inferInstance
  start := .lo
  halt := fun s => decide (s = .done)
  δ := fun s _ =>
    match s with
    | .lo => (.hi, some false, 1)
    | .hi => (.done, some false, 0)
    | .done => (.done, none, 2)
  accept := fun _ => false

/-- Restart-free stale clearing controller.  Its clock is the exact stale
cell count; every transition clears the current cell and advances right. -/
def runtimeCompactClearLoopMachine : Machine where
  State := Unit
  fin := inferInstance
  dec := inferInstance
  start := ()
  halt := fun _ => false
  δ := fun _ _ => ((), some false, 1)
  accept := fun _ => false

private theorem clearLoop_write_head
    (pre tail : List Bool) (b : Bool) :
    writeAt (pre ++ b :: tail) pre.length false =
      pre ++ false :: tail := by
  rw [PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr.writeAt_of_lt
    false (by simp)]
  simp

/-- One physical run clears an arbitrary contiguous cell block and ends
immediately after it; there are no semantic state or head restarts. -/
theorem runtimeCompactClearLoop_run
    (pre cells tail : List Bool) :
    run runtimeCompactClearLoopMachine cells.length
        ⟨runtimeCompactClearLoopMachine.start, pre.length,
          pre ++ cells ++ tail⟩ =
      ⟨(), pre.length + cells.length,
        pre ++ List.replicate cells.length false ++ tail⟩ := by
  induction cells generalizing pre with
  | nil => simp [runtimeCompactClearLoopMachine]
  | cons b cells ih =>
      rw [show (b :: cells).length = 1 + cells.length by simp [Nat.add_comm],
        run_add]
      have hstep : run runtimeCompactClearLoopMachine 1
          ⟨runtimeCompactClearLoopMachine.start, pre.length,
            pre ++ (b :: cells) ++ tail⟩ =
        ⟨(), pre.length + 1, pre ++ false :: cells ++ tail⟩ := by
        rw [run_succ, run_zero]
        simp [step, runtimeCompactClearLoopMachine, moveHead,
          clearLoop_write_head]
      rw [hstep]
      have hih := ih (pre := pre ++ [false])
      rw [show List.replicate (1 + cells.length) false =
          false :: List.replicate cells.length false by
            rw [Nat.add_comm]
            rfl]
      simpa [runtimeCompactClearLoopMachine,
        List.append_assoc, Nat.add_assoc] using hih

/-- The restart-free clearer never moves left. -/
theorem runtimeCompactClearLoop_leftSafe
    (pre cells tail : List Bool) :
    LeftSafeRun runtimeCompactClearLoopMachine
      ⟨runtimeCompactClearLoopMachine.start, pre.length,
        pre ++ cells ++ tail⟩ cells.length := by
  intro i hlt hlive hmove
  simp [runtimeCompactClearLoopMachine] at hmove

private theorem clear_write0 (pre tail : List Bool) (lo hi : Bool) :
    writeAt (pre ++ [lo, hi] ++ tail) pre.length false =
      pre ++ [false, hi] ++ tail := by
  rw [PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr.writeAt_of_lt
    false (by simp)]
  simp

private theorem clear_write1 (pre tail : List Bool) (hi : Bool) :
    writeAt (pre ++ [false, hi] ++ tail) (pre.length + 1) false =
      pre ++ [false, false] ++ tail := by
  rw [PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr.writeAt_of_lt
    false (by simp)]
  simp

/-- Exact physical clearing of one arbitrary aligned pair. -/
theorem runtimeCompactClear_run
    (pre tail : List Bool) (lo hi : Bool) :
    run runtimeCompactClearMachine 2
        ⟨runtimeCompactClearMachine.start, pre.length,
          pre ++ [lo, hi] ++ tail⟩ =
      ⟨RuntimeCompactClearState.done, pre.length,
        pre ++ [false, false] ++ tail⟩ := by
  rw [run_succ, run_succ, run_zero]
  have h1 : step runtimeCompactClearMachine
      ⟨RuntimeCompactClearState.lo, pre.length,
        pre ++ [lo, hi] ++ tail⟩ =
      ⟨RuntimeCompactClearState.hi, pre.length + 1,
        pre ++ [false, hi] ++ tail⟩ := by
    simp only [step, runtimeCompactClearMachine, moveHead]
    rw [clear_write0]
    simp
  change step runtimeCompactClearMachine
      (step runtimeCompactClearMachine
        ⟨RuntimeCompactClearState.lo, pre.length,
          pre ++ [lo, hi] ++ tail⟩) = _
  rw [h1]
  simp only [step, runtimeCompactClearMachine, moveHead]
  rw [clear_write1]
  simp

/-- Clearing one pair never crosses the physical left boundary. -/
theorem runtimeCompactClear_leftSafe
    (pre tail : List Bool) (lo hi : Bool) :
    LeftSafeRun runtimeCompactClearMachine
      ⟨runtimeCompactClearMachine.start, pre.length,
        pre ++ [lo, hi] ++ tail⟩ 2 := by
  intro i hlt hlive hmove
  interval_cases i <;>
    simp [run_succ, step, runtimeCompactClearMachine, moveHead, writeAt]
      at hlive hmove ⊢ <;> omega

/-- Certified left-to-right clearing of an arbitrary aligned pair list. -/
inductive RuntimeCompactClearChain (tail : List Bool) :
    List Bool → List (Bool × Bool) → Prop
  | nil (pre : List Bool) : RuntimeCompactClearChain tail pre []
  | cons (pre : List Bool) (lo hi : Bool) (ps : List (Bool × Bool))
      (hrun :
        run runtimeCompactClearMachine 2
            ⟨runtimeCompactClearMachine.start, pre.length,
              pre ++ [lo, hi] ++ flattenPairs ps ++ tail⟩ =
          ⟨RuntimeCompactClearState.done, pre.length,
            pre ++ [false, false] ++ flattenPairs ps ++ tail⟩)
      (hsafe :
        LeftSafeRun runtimeCompactClearMachine
          ⟨runtimeCompactClearMachine.start, pre.length,
            pre ++ [lo, hi] ++ flattenPairs ps ++ tail⟩ 2)
      (hrest : RuntimeCompactClearChain tail
        (pre ++ [false, false]) ps) :
      RuntimeCompactClearChain tail pre ((lo, hi) :: ps)

theorem runtimeCompactClear_chain
    (pre tail : List Bool) (ps : List (Bool × Bool)) :
    RuntimeCompactClearChain tail pre ps := by
  induction ps generalizing pre with
  | nil => exact .nil pre
  | cons p ps ih =>
      rcases p with ⟨lo, hi⟩
      exact .cons pre lo hi ps
        (by simpa [List.append_assoc] using
          runtimeCompactClear_run pre (flattenPairs ps ++ tail) lo hi)
        (by simpa [List.append_assoc] using
          runtimeCompactClear_leftSafe pre (flattenPairs ps ++ tail) lo hi)
        (ih (pre := pre ++ [false, false]))

/-- The exact post-cashout stale region in aligned-pair form: two routing
marker pairs, `d` obsolete unary selector pairs, and the final selector
delimiter pair. -/
def runtimeMarkedStalePairs (d : Nat) : List (Bool × Bool) :=
  [(false, false), (false, false)] ++
    List.replicate d (true, true) ++ [(false, true)]

theorem runtimeMarkedStalePairs_length (d : Nat) :
    (runtimeMarkedStalePairs d).length = d + 3 := by
  simp [runtimeMarkedStalePairs]

structure RuntimeMarkedPhysicalClearCertificate
    (retained workspace tail : List Bool) (d : Nat) : Prop where
  run_eq :
    run runtimeCompactClearLoopMachine (2 * (d + 3))
        ⟨runtimeCompactClearLoopMachine.start, retained.length,
          retained ++ flattenPairs (runtimeMarkedStalePairs d) ++
            workspace ++ tail⟩ =
      ⟨(), retained.length + 2 * (d + 3),
        retained ++ List.replicate (2 * (d + 3)) false ++
          workspace ++ tail⟩
  leftSafe : LeftSafeRun runtimeCompactClearLoopMachine
    ⟨runtimeCompactClearLoopMachine.start, retained.length,
      retained ++ flattenPairs (runtimeMarkedStalePairs d) ++
        workspace ++ tail⟩ (2 * (d + 3))

/-- The exact marked stale region is cleared by one contiguous physical run,
with the head returned at the first workspace cell. -/
theorem runtimeMarkedPhysicalClear_certificate
    (retained workspace tail : List Bool) (d : Nat) :
    RuntimeMarkedPhysicalClearCertificate retained workspace tail d := by
  have hlen : (flattenPairs (runtimeMarkedStalePairs d)).length =
      2 * (d + 3) := by
    rw [flattenPairs_length, runtimeMarkedStalePairs_length]
  constructor
  · simpa [hlen, List.append_assoc] using
      runtimeCompactClearLoop_run retained
        (flattenPairs (runtimeMarkedStalePairs d)) (workspace ++ tail)
  · simpa [hlen, List.append_assoc] using
      runtimeCompactClearLoop_leftSafe retained
        (flattenPairs (runtimeMarkedStalePairs d)) (workspace ++ tail)

/-- Complete certified marked-to-compact plan: physically clear the exact
stale marker/selector block, then move all `d + 3` resulting holes across the
completed workspace. -/
structure RuntimeMarkedCompactCertificate
    (retained : List Bool) (workspace : List (Bool × Bool))
    (tail : List Bool) (d : Nat) : Prop where
  clear : RuntimeCompactClearChain (flattenPairs workspace ++ tail)
    retained (runtimeMarkedStalePairs d)
  shift : RuntimeCompactBubblePasses retained workspace tail (d + 3)

theorem runtimeMarkedCompact_certificate
    (retained tail : List Bool) (workspace : List (Bool × Bool)) (d : Nat) :
    RuntimeMarkedCompactCertificate retained workspace tail d := by
  exact ⟨runtimeCompactClear_chain retained (flattenPairs workspace ++ tail)
      (runtimeMarkedStalePairs d),
    runtimeCompactBubble_passes retained tail workspace (d + 3)⟩

/-! ## Exact-clock halting adapter -/

/-- Add a finite exact clock to a machine.  The wrapped machine performs
exactly `n` transitions of `M`, then halts without changing the tape or head.
This is the control adapter needed to place the restart-free clear, bubble,
and rewind loops inside `headSeqMachine`. -/
def exactClockMachine (M : Machine) (n : Nat) : Machine where
  State := Fin (n + 1) × M.State
  fin := inferInstance
  dec := inferInstance
  start := (⟨0, by omega⟩, M.start)
  halt := fun s => decide (s.1.val = n)
  δ := fun s b =>
    let tr := M.δ s.2 b
    let next : Fin (n + 1) :=
      if h : s.1.val < n then ⟨s.1.val + 1, by omega⟩ else s.1
    ((next, tr.1), tr.2.1, tr.2.2)
  accept := fun s => M.accept s.2

/-- Embed an underlying configuration at clock value `t ≤ n`. -/
def exactClockCfg (M : Machine) (n t : Nat) (ht : t ≤ n)
    (c : Cfg M) : Cfg (exactClockMachine M n) :=
  ⟨(⟨t, by omega⟩, c.st), c.hd, c.tp⟩

@[simp] theorem exactClockMachine_halt_at (M : Machine) (n : Nat)
    (s : M.State) :
    (exactClockMachine M n).halt (⟨n, by omega⟩, s) = true := by
  simp [exactClockMachine]

/-- Below the exact clock, one wrapped step is precisely one underlying
step, with the clock incremented.  The underlying machines used here are
nonhalting loops, which is stated explicitly rather than hidden. -/
theorem exactClockMachine_step (M : Machine) (n t : Nat) (ht : t < n)
    (c : Cfg M) (hlive : M.halt c.st = false) :
    step (exactClockMachine M n) (exactClockCfg M n t (by omega) c) =
      exactClockCfg M n (t + 1) (by omega) (step M c) := by
  simp only [step, exactClockCfg, exactClockMachine, Machine.halt, Cfg.st,
    Bool.decide_eq_true, Cfg.tp, Cfg.hd, Machine.δ]
  have hne : t ≠ n := by omega
  simp [ht, hne, hlive]

/-- A clock segment starting at counter `k` mirrors the corresponding
underlying run as long as it remains strictly below the terminal count. -/
theorem exactClockMachine_run_segment (M : Machine) (n k t : Nat)
    (hkt : k + t ≤ n) (c : Cfg M)
    (hlive : ∀ i < t, M.halt (run M i c).st = false) :
    run (exactClockMachine M n) t (exactClockCfg M n k (by omega) c) =
      exactClockCfg M n (k + t) hkt (run M t c) := by
  induction t generalizing k c with
  | zero => rfl
  | succ t ih =>
      rw [run_succ]
      have hprefix := ih (k := k) (c := c) (by omega)
        (fun i hi => hlive i (by omega))
      rw [hprefix]
      have hs := exactClockMachine_step M n (k + t) (by omega)
        (run M t c) (hlive t (by omega))
      rw [← run_succ] at hs
      simpa only [Nat.add_assoc] using hs

/-- Running the adapter for its full clock gives exactly the underlying
`n`-step configuration and a genuinely halting wrapper state. -/
theorem exactClockMachine_run (M : Machine) (n : Nat) (c : Cfg M)
    (hlive : ∀ t < n, M.halt (run M t c).st = false) :
    run (exactClockMachine M n) n (exactClockCfg M n 0 (Nat.zero_le _) c) =
      exactClockCfg M n n (le_rfl) (run M n c) := by
  simpa using exactClockMachine_run_segment M n 0 n (by omega) c hlive

/-- The exact-clock wrapper around each compaction loop has no early halt:
its unique halt occurs precisely at the terminal counter. -/
theorem exactClockMachine_not_halted_before (M : Machine) (n t : Nat)
    (ht : t < n) (s : M.State) :
    (exactClockMachine M n).halt (⟨t, by omega⟩, s) = false := by
  simp [exactClockMachine, show t ≠ n by omega]

/-- Physical adjacency between restart-free clearing and the first bubble
pass.  Clearing stops at the first workspace cell, so exactly two no-write
left moves place the head on the low cell of the rightmost cleared hole.
The tape is unchanged and the bridge is physically left-safe. -/
structure RuntimeMarkedClearFirstHoleBridge
    (retained : List Bool) (workspace : List (Bool × Bool))
    (tail : List Bool) (d : Nat) : Prop where
  clearRun :
    run runtimeCompactClearLoopMachine (2 * (d + 3))
        ⟨runtimeCompactClearLoopMachine.start, retained.length,
          retained ++ flattenPairs (runtimeMarkedStalePairs d) ++
            flattenPairs workspace ++ tail⟩ =
      ⟨(), retained.length + 2 * (d + 3),
        retained ++ List.replicate (2 * (d + 3)) false ++
          flattenPairs workspace ++ tail⟩
  rewindRun :
    run runtimeCompactRewindMachine 2
        ⟨runtimeCompactRewindMachine.start,
          retained.length + 2 * (d + 3),
          retained ++ List.replicate (2 * (d + 3)) false ++
            flattenPairs workspace ++ tail⟩ =
      ⟨(), retained.length + 2 * (d + 2),
        retained ++ List.replicate (2 * (d + 3)) false ++
          flattenPairs workspace ++ tail⟩
  clearSafe : LeftSafeRun runtimeCompactClearLoopMachine
    ⟨runtimeCompactClearLoopMachine.start, retained.length,
      retained ++ flattenPairs (runtimeMarkedStalePairs d) ++
        flattenPairs workspace ++ tail⟩ (2 * (d + 3))
  rewindSafe : LeftSafeRun runtimeCompactRewindMachine
    ⟨runtimeCompactRewindMachine.start,
      retained.length + 2 * (d + 3),
      retained ++ List.replicate (2 * (d + 3)) false ++
        flattenPairs workspace ++ tail⟩ 2

theorem runtimeMarkedClearFirstHoleBridge_certificate
    (retained tail : List Bool) (workspace : List (Bool × Bool)) (d : Nat) :
    RuntimeMarkedClearFirstHoleBridge retained workspace tail d := by
  have hc := runtimeMarkedPhysicalClear_certificate retained
    (flattenPairs workspace) tail d
  have hr := runtimeCompactRewind_run
    (retained ++ List.replicate (2 * (d + 2)) false)
    ([false, false] ++ flattenPairs workspace ++ tail) 2
  have hrs := runtimeCompactRewind_leftSafe
    (retained ++ List.replicate (2 * (d + 2)) false)
    ([false, false] ++ flattenPairs workspace ++ tail) 2
  have hstart :
      (retained ++ List.replicate (2 * (d + 2)) false).length + 2 =
        retained.length + 2 * (d + 3) := by simp; omega
  have hend :
      (retained ++ List.replicate (2 * (d + 2)) false).length =
        retained.length + 2 * (d + 2) := by simp
  have htape :
      retained ++ List.replicate (2 * (d + 2)) false ++
          ([false, false] ++ flattenPairs workspace ++ tail) =
        retained ++ List.replicate (2 * (d + 3)) false ++
          flattenPairs workspace ++ tail := by
    simp [List.replicate_add, List.append_assoc, Nat.mul_add]
  constructor
  · exact hc.run_eq
  · simpa only [hstart, hend, htape] using hr
  · exact hc.leftSafe
  · simpa only [hstart, htape] using hrs

#print axioms runtimeCompactBubble_run
#print axioms runtimeCompactBubble_leftSafe
#print axioms runtimeCompactBubble_chain
#print axioms runtimeCompactBubble_passes
#print axioms runtimeCompactBubbleLoop_round
#print axioms runtimeCompactBubbleLoop_run
#print axioms runtimeCompactBubbleLoop_leftSafe
#print axioms runtimeCompactRewind_run
#print axioms runtimeCompactRewind_leftSafe
#print axioms runtimeCompactPassRewind_certificate
#print axioms runtimeCompactAllPasses_certificate
#print axioms runtimeMarkedAllPasses_certificate
#print axioms runtimeCompactClear_run
#print axioms runtimeCompactClear_leftSafe
#print axioms runtimeCompactClear_chain
#print axioms runtimeCompactClearLoop_run
#print axioms runtimeCompactClearLoop_leftSafe
#print axioms runtimeMarkedPhysicalClear_certificate
#print axioms runtimeMarkedCompact_certificate
#print axioms exactClockMachine_run
#print axioms runtimeMarkedClearFirstHoleBridge_certificate

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeCompactChain
