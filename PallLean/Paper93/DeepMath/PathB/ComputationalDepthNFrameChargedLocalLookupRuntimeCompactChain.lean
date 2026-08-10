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

#print axioms runtimeCompactBubble_run
#print axioms runtimeCompactBubble_leftSafe
#print axioms runtimeCompactBubble_chain
#print axioms runtimeCompactBubble_passes
#print axioms runtimeCompactClear_run
#print axioms runtimeCompactClear_leftSafe
#print axioms runtimeCompactClear_chain
#print axioms runtimeCompactClearLoop_run
#print axioms runtimeCompactClearLoop_leftSafe
#print axioms runtimeMarkedPhysicalClear_certificate
#print axioms runtimeMarkedCompact_certificate

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeCompactChain
