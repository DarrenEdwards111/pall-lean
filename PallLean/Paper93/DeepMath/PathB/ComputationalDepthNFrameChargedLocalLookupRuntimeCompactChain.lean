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
  cases lo <;> cases hi <;>
    simp only [run_succ, step, runtimeCompactBubbleMachine, moveHead,
      Machine.halt, Machine.δ, Cfg.st, Cfg.head, Cfg.tape]
  all_goals
    rw [compact_getElem3, compact_getElem2, compact_write3',
      compact_bubble_after_clear]

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

#print axioms runtimeCompactBubble_run
#print axioms runtimeCompactBubble_leftSafe
#print axioms runtimeCompactBubble_chain

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeCompactChain
