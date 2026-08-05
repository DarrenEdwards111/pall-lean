import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeSourceSelect

/-!
# Charged local lookup: fixed in-place source compaction

The fixed source selector halts at a payload stored as `encodeD bits`.  This
file supplies the next physical component.  One fixed finite-control machine
uses the selected block's `10` header as a moving boundary and repeatedly
performs

    out ++ 10 ++ b b ++ encodeD rest
      ↦ (out ++ [b]) ++ 10 ++ encodeD rest ++ 1.

Thus every round decodes one doubled source pair and shifts only the remainder
of the selected block.  Later archive blocks are never moved or rewritten;
the vacated cell is retained as a `1` immediately before that untouched tail.
At termination the exact raw payload is contiguous at the former selected
header position.  The transition table has no input-dependent parameters.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinRoundInvariant
open PallLean.Paper93.DeepMath.PathB.CookLevinInP
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect

inductive SourceCompactState
  | backHi
  | backLo
  | markerLo
  | markerHi
  | sourceLo
  | sourceHi (lo : Bool)
  | rewriteDataLo (b : Bool)
  | rewriteMarkerHi (b : Bool)
  | rewriteMarkerLo (b : Bool)
  | goMarkerHi
  | goMarkerLo
  | holeLo
  | readLo
  | writeLo (lo : Bool)
  | holeHi (lo : Bool)
  | readHi (lo : Bool)
  | writeHi (lo hi : Bool)
  | returnStart
  | returnHi
  | returnLo (hi : Bool)
  | done
  deriving Fintype, DecidableEq

open SourceCompactState

/-- Fixed in-place decoder/compactor.  It starts at the first cell of the
selected doubled payload, two cells to the right of its `10` header. -/
def sourceCompactMachine : Machine where
  State := SourceCompactState
  fin := inferInstance
  dec := inferInstance
  start := backHi
  halt
    | done => true
    | _ => false
  δ s b := match s with
    | backHi => (backLo, none, 0)
    | backLo => (markerLo, none, 0)
    | markerLo => (markerHi, none, 1)
    | markerHi => (sourceLo, none, 1)
    | sourceLo => (sourceHi b, none, 1)
    | sourceHi lo =>
        if !lo && b then (done, none, 2)
        else (rewriteDataLo lo, none, 0)
    | rewriteDataLo bv => (rewriteMarkerHi bv, some false, 0)
    | rewriteMarkerHi bv => (rewriteMarkerLo bv, some true, 0)
    | rewriteMarkerLo bv => (goMarkerHi, some bv, 1)
    | goMarkerHi => (goMarkerLo, none, 1)
    | goMarkerLo => (holeLo, none, 1)
    | holeLo => (readLo, none, 1)
    | readLo => (writeLo b, none, 0)
    | writeLo lo => (holeHi lo, some lo, 1)
    | holeHi lo => (readHi lo, none, 1)
    | readHi lo => (writeHi lo b, none, 0)
    | writeHi lo hi =>
        if !lo && hi then (returnStart, some hi, 1)
        else (holeLo, some hi, 1)
    | returnStart => (returnHi, none, 0)
    | returnHi => (returnLo b, none, 0)
    | returnLo hi =>
        if b && !hi then (markerLo, none, 2)
        else (returnHi, none, 0)
    | done => (done, none, 2)
  accept := fun _ => false

/-- Round invariant.  `garbage` consists of the cells vacated by earlier
left shifts; the intended run specializes it to a run of `true` cells. -/
def compactTape (pre out rest garbage tail : List Bool) : List Bool :=
  pre ++ out ++ [true, false] ++ encodeD rest ++ garbage ++ tail

def bubbleTape (A done : List Bool) (carry : Bool)
    (todo tail : List Bool) : List Bool :=
  A ++ done ++ carry :: todo ++ tail

private theorem getD_boundary (P R : List Bool) (b : Bool) :
    (P ++ b :: R).getD P.length false = b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    Nat.sub_self]
  rfl

private theorem writeAt_boundary (P R : List Bool) (b w : Bool) :
    writeAt (P ++ b :: R) P.length w = P ++ w :: R := by
  rw [writeAt_of_lt w (by simp)]
  simp

private theorem getD_two_prefix (a b : Bool) (xs : List Bool)
    (i : Nat) (d : Bool) :
    (a :: b :: xs).getD (i + 2) d = xs.getD i d := by
  simp [List.getD_eq_getElem?_getD]

theorem step_markerLo (p : Nat) (T : List Bool) :
    step sourceCompactMachine ⟨markerLo, p, T⟩ =
      ⟨markerHi, p + 1, T⟩ := by
  simp [step, sourceCompactMachine, moveHead]

theorem step_markerHi (p : Nat) (T : List Bool) :
    step sourceCompactMachine ⟨markerHi, p, T⟩ =
      ⟨sourceLo, p + 1, T⟩ := by
  simp [step, sourceCompactMachine, moveHead]

theorem step_sourceLo (p : Nat) (T : List Bool) (b : Bool)
    (h : T.getD p false = b) :
    step sourceCompactMachine ⟨sourceLo, p, T⟩ =
      ⟨sourceHi b, p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, sourceCompactMachine, moveHead, h]

theorem step_sourceHi_data (p : Nat) (T : List Bool) (b : Bool)
    (h : T.getD p false = b) :
    step sourceCompactMachine ⟨sourceHi b, p, T⟩ =
      ⟨rewriteDataLo b, p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  cases b <;> simp [step, sourceCompactMachine, moveHead, h]

theorem step_sourceHi_finish (p : Nat) (T : List Bool)
    (h : T.getD p false = true) :
    step sourceCompactMachine ⟨sourceHi false, p, T⟩ =
      ⟨done, p, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, sourceCompactMachine, moveHead, h]

theorem step_rewriteDataLo (p : Nat) (T : List Bool) (b : Bool) :
    step sourceCompactMachine ⟨rewriteDataLo b, p, T⟩ =
      ⟨rewriteMarkerHi b, p - 1, writeAt T p false⟩ := by
  simp [step, sourceCompactMachine, moveHead]

theorem step_rewriteMarkerHi (p : Nat) (T : List Bool) (b : Bool) :
    step sourceCompactMachine ⟨rewriteMarkerHi b, p, T⟩ =
      ⟨rewriteMarkerLo b, p - 1, writeAt T p true⟩ := by
  simp [step, sourceCompactMachine, moveHead]

theorem step_rewriteMarkerLo (p : Nat) (T : List Bool) (b : Bool) :
    step sourceCompactMachine ⟨rewriteMarkerLo b, p, T⟩ =
      ⟨goMarkerHi, p + 1, writeAt T p b⟩ := by
  simp [step, sourceCompactMachine, moveHead]

theorem step_goMarkerHi (p : Nat) (T : List Bool) :
    step sourceCompactMachine ⟨goMarkerHi, p, T⟩ =
      ⟨goMarkerLo, p + 1, T⟩ := by
  simp [step, sourceCompactMachine, moveHead]

theorem step_goMarkerLo (p : Nat) (T : List Bool) :
    step sourceCompactMachine ⟨goMarkerLo, p, T⟩ =
      ⟨holeLo, p + 1, T⟩ := by
  simp [step, sourceCompactMachine, moveHead]

theorem step_holeLo (p : Nat) (T : List Bool) :
    step sourceCompactMachine ⟨holeLo, p, T⟩ =
      ⟨readLo, p + 1, T⟩ := by
  simp [step, sourceCompactMachine, moveHead]

theorem step_readLo (p : Nat) (T : List Bool) (b : Bool)
    (h : T.getD p false = b) :
    step sourceCompactMachine ⟨readLo, p, T⟩ =
      ⟨writeLo b, p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, sourceCompactMachine, moveHead, h]

theorem step_writeLo (p : Nat) (T : List Bool) (b : Bool) :
    step sourceCompactMachine ⟨writeLo b, p, T⟩ =
      ⟨holeHi b, p + 1, writeAt T p b⟩ := by
  simp [step, sourceCompactMachine, moveHead]

theorem step_holeHi (p : Nat) (T : List Bool) (lo : Bool) :
    step sourceCompactMachine ⟨holeHi lo, p, T⟩ =
      ⟨readHi lo, p + 1, T⟩ := by
  simp [step, sourceCompactMachine, moveHead]

theorem step_readHi (p : Nat) (T : List Bool) (lo hi : Bool)
    (h : T.getD p false = hi) :
    step sourceCompactMachine ⟨readHi lo, p, T⟩ =
      ⟨writeHi lo hi, p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, sourceCompactMachine, moveHead, h]

theorem step_writeHi_continue (p : Nat) (T : List Bool)
    (lo hi : Bool) (hn : ¬(!lo && hi)) :
    step sourceCompactMachine ⟨writeHi lo hi, p, T⟩ =
      ⟨holeLo, p + 1, writeAt T p hi⟩ := by
  simp [step, sourceCompactMachine, moveHead, hn]

theorem step_writeHi_finish (p : Nat) (T : List Bool) :
    step sourceCompactMachine ⟨writeHi false true, p, T⟩ =
      ⟨returnStart, p + 1, writeAt T p true⟩ := by
  simp [step, sourceCompactMachine, moveHead]

theorem step_returnHi (p : Nat) (T : List Bool) (hi : Bool)
    (h : T.getD p false = hi) :
    step sourceCompactMachine ⟨returnHi, p, T⟩ =
      ⟨returnLo hi, p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, sourceCompactMachine, moveHead, h]

theorem step_returnLo_continue (p : Nat) (T : List Bool)
    (lo hi : Bool) (h : T.getD p false = lo) (hn : ¬(lo && !hi)) :
    step sourceCompactMachine ⟨returnLo hi, p, T⟩ =
      ⟨returnHi, p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, sourceCompactMachine, moveHead, h, hn]

theorem step_returnLo_finish (p : Nat) (T : List Bool)
    (h : T.getD p false = true) :
    step sourceCompactMachine ⟨returnLo false, p, T⟩ =
      ⟨markerLo, p, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, sourceCompactMachine, moveHead, h]

theorem sourceCompact_start (pre out rest garbage tail : List Bool) :
    run sourceCompactMachine 2
        ⟨backHi, pre.length + out.length + 2,
          compactTape pre out rest garbage tail⟩ =
      ⟨markerLo, pre.length + out.length,
        compactTape pre out rest garbage tail⟩ := by
  rw [run_succ, run_succ, run_zero]
  simp [step, sourceCompactMachine, moveHead]

theorem sourceCompact_finish (pre out garbage tail : List Bool) :
    run sourceCompactMachine 4
        ⟨markerLo, pre.length + out.length,
          compactTape pre out [] garbage tail⟩ =
      ⟨done, pre.length + out.length + 3,
        compactTape pre out [] garbage tail⟩ := by
  let Q := pre ++ out
  let R := garbage ++ tail
  have hlo : (compactTape pre out [] garbage tail).getD
      (Q.length + 2) false = false := by
    rw [show compactTape pre out [] garbage tail =
      (Q ++ [true, false]) ++ false :: true :: R by
        simp [compactTape, encodeD, Q, R, List.append_assoc]]
    simpa using getD_boundary (Q ++ [true, false]) (true :: R) false
  have hhi : (compactTape pre out [] garbage tail).getD
      (Q.length + 3) false = true := by
    rw [show compactTape pre out [] garbage tail =
      (Q ++ [true, false, false]) ++ true :: R by
        simp [compactTape, encodeD, Q, R, List.append_assoc]]
    simpa using getD_boundary (Q ++ [true, false, false]) R true
  let T := compactTape pre out [] garbage tail
  have h1 : run sourceCompactMachine 1
      ⟨markerLo, pre.length + out.length, T⟩ =
      ⟨markerHi, pre.length + out.length + 1, T⟩ := by
    rw [run_succ, run_zero, step_markerLo]
  have h2 : run sourceCompactMachine 1
      ⟨markerHi, pre.length + out.length + 1, T⟩ =
      ⟨sourceLo, pre.length + out.length + 2, T⟩ := by
    rw [run_succ, run_zero, step_markerHi]
  have h3 : run sourceCompactMachine 1
      ⟨sourceLo, pre.length + out.length + 2, T⟩ =
      ⟨sourceHi false, pre.length + out.length + 3, T⟩ := by
    rw [run_succ, run_zero]
    apply step_sourceLo
    simpa [T, Q] using hlo
  have h4 : run sourceCompactMachine 1
      ⟨sourceHi false, pre.length + out.length + 3, T⟩ =
      ⟨done, pre.length + out.length + 3, T⟩ := by
    rw [run_succ, run_zero]
    apply step_sourceHi_finish
    simpa [T, Q] using hhi
  rw [show 4 = 1 + (1 + (1 + 1)) by omega, run_add, h1,
    run_add, h2, run_add, h3, h4]

theorem sourceCompact_rewrite (pre out rest garbage tail : List Bool)
    (b : Bool) :
    run sourceCompactMachine 9
        ⟨markerLo, pre.length + out.length,
          compactTape pre out (b :: rest) garbage tail⟩ =
      ⟨holeLo, (pre ++ out ++ [b, true, false]).length,
        bubbleTape (pre ++ out ++ [b, true, false]) [] b
          (encodeD rest) (garbage ++ tail)⟩ := by
  let Q := pre ++ out
  let R := encodeD rest ++ garbage ++ tail
  let T0 := Q ++ [true, false, b, b] ++ R
  let T1 := Q ++ [true, false, false, b] ++ R
  let T2 := Q ++ [true, true, false, b] ++ R
  let T3 := Q ++ [b, true, false, b] ++ R
  have hT : compactTape pre out (b :: rest) garbage tail = T0 := by
    simp [compactTape, encodeD, T0, Q, R, List.append_assoc]
  have hlo : T0.getD (Q.length + 2) false = b := by
    rw [show T0 = (Q ++ [true, false]) ++ b :: (b :: R) by
      simp [T0]]
    simpa using getD_boundary (Q ++ [true, false]) (b :: R) b
  have hhi : T0.getD (Q.length + 3) false = b := by
    rw [show T0 = (Q ++ [true, false, b]) ++ b :: R by
      simp [T0]]
    simpa using getD_boundary (Q ++ [true, false, b]) R b
  have hread : run sourceCompactMachine 4
      ⟨markerLo, pre.length + out.length, T0⟩ =
      ⟨rewriteDataLo b, Q.length + 2, T0⟩ := by
    have h1 : run sourceCompactMachine 1
        ⟨markerLo, pre.length + out.length, T0⟩ =
        ⟨markerHi, Q.length + 1, T0⟩ := by
      rw [run_succ, run_zero, step_markerLo]
      simp [Q]
    have h2 : run sourceCompactMachine 1
        ⟨markerHi, Q.length + 1, T0⟩ =
      ⟨sourceLo, Q.length + 2, T0⟩ := by
      rw [run_succ, run_zero, step_markerHi]
    have h3 : run sourceCompactMachine 1
        ⟨sourceLo, Q.length + 2, T0⟩ =
        ⟨sourceHi b, Q.length + 3, T0⟩ := by
      rw [run_succ, run_zero, step_sourceLo _ _ b hlo]
    have h4 : run sourceCompactMachine 1
        ⟨sourceHi b, Q.length + 3, T0⟩ =
        ⟨rewriteDataLo b, Q.length + 2, T0⟩ := by
      rw [run_succ, run_zero, step_sourceHi_data _ _ b hhi]
      congr 1 <;> omega
    rw [show 4 = 1 + (1 + (1 + 1)) by omega, run_add, h1,
      run_add, h2, run_add, h3, h4]
  have hw1 : writeAt T0 (Q.length + 2) false = T1 := by
    simpa [T0, T1] using
      writeAt_boundary (Q ++ [true, false]) (b :: R) b false
  have hw2 : writeAt T1 (Q.length + 1) true = T2 := by
    simpa [T1, T2] using
      writeAt_boundary (Q ++ [true]) (false :: b :: R) false true
  have hw3 : writeAt T2 Q.length b = T3 := by
    simpa [T2, T3] using
      writeAt_boundary Q (true :: false :: b :: R) true b
  have h5 : run sourceCompactMachine 1
      ⟨rewriteDataLo b, Q.length + 2, T0⟩ =
      ⟨rewriteMarkerHi b, Q.length + 1, T1⟩ := by
    rw [run_succ, run_zero, step_rewriteDataLo, hw1]
    congr 1 <;> omega
  have h6 : run sourceCompactMachine 1
      ⟨rewriteMarkerHi b, Q.length + 1, T1⟩ =
      ⟨rewriteMarkerLo b, Q.length, T2⟩ := by
    rw [run_succ, run_zero, step_rewriteMarkerHi, hw2]
    congr 1 <;> omega
  have h7 : run sourceCompactMachine 1
      ⟨rewriteMarkerLo b, Q.length, T2⟩ =
      ⟨goMarkerHi, Q.length + 1, T3⟩ := by
    rw [run_succ, run_zero, step_rewriteMarkerLo, hw3]
  have h8 : run sourceCompactMachine 1
      ⟨goMarkerHi, Q.length + 1, T3⟩ =
      ⟨goMarkerLo, Q.length + 2, T3⟩ := by
    rw [run_succ, run_zero, step_goMarkerHi]
  have h9 : run sourceCompactMachine 1
      ⟨goMarkerLo, Q.length + 2, T3⟩ =
      ⟨holeLo, Q.length + 3, T3⟩ := by
    rw [run_succ, run_zero, step_goMarkerLo]
  rw [hT, show 9 = 4 + (1 + (1 + (1 + (1 + 1)))) by omega,
    run_add, hread, run_add, h5, run_add, h6, run_add, h7,
    run_add, h8, h9]
  simp [T3, Q, R, bubbleTape, List.append_assoc] <;> omega

theorem sourceCompact_copy_lo (A done : List Bool) (carry lo : Bool)
    (todo tail : List Bool) :
    run sourceCompactMachine 3
        ⟨holeLo, A.length + done.length,
          bubbleTape A done carry (lo :: todo) tail⟩ =
      ⟨holeHi lo, A.length + done.length + 1,
        bubbleTape A (done ++ [lo]) lo todo tail⟩ := by
  let P := A ++ done
  let T := bubbleTape A done carry (lo :: todo) tail
  have hlo : T.getD (P.length + 1) false = lo := by
    rw [show T = (P ++ [carry]) ++ lo :: (todo ++ tail) by
      simp [T, P, bubbleTape, List.append_assoc]]
    simpa using getD_boundary (P ++ [carry]) (todo ++ tail) lo
  have hw : writeAt T P.length lo =
      bubbleTape A (done ++ [lo]) lo todo tail := by
    rw [show T = P ++ carry :: (lo :: todo ++ tail) by
      simp [T, P, bubbleTape, List.append_assoc], writeAt_boundary]
    simp [P, bubbleTape, List.append_assoc]
  rw [show 3 = 1 + (1 + 1) by omega, run_add,
    show run sourceCompactMachine 1
      ⟨holeLo, A.length + done.length, T⟩ =
      ⟨readLo, A.length + done.length + 1, T⟩ by
        rw [run_succ, run_zero, step_holeLo],
    run_add]
  rw [show run sourceCompactMachine 1
      ⟨readLo, A.length + done.length + 1, T⟩ =
      ⟨writeLo lo, A.length + done.length, T⟩ by
        rw [run_succ, run_zero]
        have := step_readLo (P.length + 1) T lo hlo
        simpa [P] using this,
    run_succ, run_zero, step_writeLo]
  congr 1
  simpa [P] using hw

theorem sourceCompact_copy_hi_continue (A done : List Bool)
    (carry lo hi : Bool) (todo tail : List Bool)
    (hn : ¬(!lo && hi)) :
    run sourceCompactMachine 3
        ⟨holeHi lo, A.length + done.length,
          bubbleTape A done carry (hi :: todo) tail⟩ =
      ⟨holeLo, A.length + done.length + 1,
        bubbleTape A (done ++ [hi]) hi todo tail⟩ := by
  let P := A ++ done
  let T := bubbleTape A done carry (hi :: todo) tail
  have hhi : T.getD (P.length + 1) false = hi := by
    rw [show T = (P ++ [carry]) ++ hi :: (todo ++ tail) by
      simp [T, P, bubbleTape, List.append_assoc]]
    simpa using getD_boundary (P ++ [carry]) (todo ++ tail) hi
  have hw : writeAt T P.length hi =
      bubbleTape A (done ++ [hi]) hi todo tail := by
    rw [show T = P ++ carry :: (hi :: todo ++ tail) by
      simp [T, P, bubbleTape, List.append_assoc], writeAt_boundary]
    simp [P, bubbleTape, List.append_assoc]
  rw [show 3 = 1 + (1 + 1) by omega, run_add,
    show run sourceCompactMachine 1
      ⟨holeHi lo, A.length + done.length, T⟩ =
      ⟨readHi lo, A.length + done.length + 1, T⟩ by
        rw [run_succ, run_zero, step_holeHi],
    run_add]
  rw [show run sourceCompactMachine 1
      ⟨readHi lo, A.length + done.length + 1, T⟩ =
      ⟨writeHi lo hi, A.length + done.length, T⟩ by
        rw [run_succ, run_zero]
        have := step_readHi (P.length + 1) T lo hi hhi
        simpa [P] using this,
    run_succ, run_zero, step_writeHi_continue _ _ lo hi hn]
  congr 1
  simpa [P] using hw

theorem sourceCompact_copy_hi_finish (A done : List Bool)
    (carry : Bool) (todo tail : List Bool) :
    run sourceCompactMachine 3
        ⟨holeHi false, A.length + done.length,
          bubbleTape A done carry (true :: todo) tail⟩ =
      ⟨returnStart, A.length + done.length + 1,
        bubbleTape A (done ++ [true]) true todo tail⟩ := by
  let P := A ++ done
  let T := bubbleTape A done carry (true :: todo) tail
  have hhi : T.getD (P.length + 1) false = true := by
    rw [show T = (P ++ [carry]) ++ true :: (todo ++ tail) by
      simp [T, P, bubbleTape, List.append_assoc]]
    simpa using getD_boundary (P ++ [carry]) (todo ++ tail) true
  have hw : writeAt T P.length true =
      bubbleTape A (done ++ [true]) true todo tail := by
    rw [show T = P ++ carry :: (true :: todo ++ tail) by
      simp [T, P, bubbleTape, List.append_assoc], writeAt_boundary]
    simp [P, bubbleTape, List.append_assoc]
  rw [show 3 = 1 + (1 + 1) by omega, run_add,
    show run sourceCompactMachine 1
      ⟨holeHi false, A.length + done.length, T⟩ =
      ⟨readHi false, A.length + done.length + 1, T⟩ by
        rw [run_succ, run_zero, step_holeHi],
    run_add]
  rw [show run sourceCompactMachine 1
      ⟨readHi false, A.length + done.length + 1, T⟩ =
      ⟨writeHi false true, A.length + done.length, T⟩ by
        rw [run_succ, run_zero]
        have := step_readHi (P.length + 1) T false true hhi
        simpa [P] using this,
    run_succ, run_zero, step_writeHi_finish]
  congr 1
  simpa [P] using hw

def shiftPairsClock (ps : List (Bool × Bool)) : Nat := 6 * ps.length

theorem sourceCompact_shift_pairs (A done : List Bool) (carry : Bool)
    (ps : List (Bool × Bool)) (ending suffix : List Bool)
    (hvalid : ∀ p ∈ ps, ¬(!p.1 && p.2)) :
    run sourceCompactMachine (shiftPairsClock ps)
        ⟨holeLo, A.length + done.length,
          bubbleTape A done carry (flattenPairs ps ++ ending) suffix⟩ =
      ⟨holeLo, A.length + done.length + 2 * ps.length,
        bubbleTape A (done ++ flattenPairs ps)
          ((flattenPairs ps).getD (2 * ps.length - 1) carry) ending suffix⟩ := by
  induction ps generalizing done carry with
  | nil => simp [shiftPairsClock, bubbleTape, flattenPairs]
  | cons p ps ih =>
      rcases p with ⟨lo, hi⟩
      have hp : ¬(!lo && hi) := hvalid (lo, hi) (by simp)
      have hps : ∀ p ∈ ps, ¬(!p.1 && p.2) := by
        intro p hm
        exact hvalid p (by simp [hm])
      rw [shiftPairsClock, List.length_cons,
        show 6 * (ps.length + 1) = 3 + 3 + 6 * ps.length by omega,
        run_add, run_add]
      simp only [flattenPairs]
      have hlo := sourceCompact_copy_lo A done carry lo
        (hi :: flattenPairs ps ++ ending) suffix
      have hhi := sourceCompact_copy_hi_continue A (done ++ [lo]) lo lo hi
        (flattenPairs ps ++ ending) suffix hp
      have hlo' : run sourceCompactMachine 3
          ⟨holeLo, A.length + done.length,
            bubbleTape A done carry
              (lo :: hi :: flattenPairs ps ++ ending) suffix⟩ =
          ⟨holeHi lo, A.length + done.length + 1,
            bubbleTape A (done ++ [lo]) lo
              (hi :: flattenPairs ps ++ ending) suffix⟩ := by
        simpa [List.append_assoc] using hlo
      have hhi' : run sourceCompactMachine 3
          ⟨holeHi lo, A.length + done.length + 1,
            bubbleTape A (done ++ [lo]) lo
              (hi :: flattenPairs ps ++ ending) suffix⟩ =
          ⟨holeLo, A.length + done.length + 2,
            bubbleTape A (done ++ [lo, hi]) hi
              (flattenPairs ps ++ ending) suffix⟩ := by
        simpa [List.append_assoc] using hhi
      rw [hlo', hhi']
      have hih := ih (done ++ [lo, hi]) hi hps
      simp only [shiftPairsClock] at hih
      have hih' : run sourceCompactMachine (6 * ps.length)
          ⟨holeLo, A.length + done.length + 2,
            bubbleTape A (done ++ [lo, hi]) hi
              (flattenPairs ps ++ ending) suffix⟩ =
          ⟨holeLo, A.length + done.length + 2 + 2 * ps.length,
            bubbleTape A (done ++ [lo, hi] ++ flattenPairs ps)
              ((flattenPairs ps).getD (2 * ps.length - 1) hi)
              ending suffix⟩ := by
        simpa using hih
      rw [hih']
      have hhead : A.length + done.length + 2 + 2 * ps.length =
          A.length + done.length + 2 * (ps.length + 1) := by omega
      have hcarry : (flattenPairs ps).getD (2 * ps.length - 1) hi =
          (lo :: hi :: flattenPairs ps).getD
            (2 * (ps.length + 1) - 1) carry := by
        cases ps with
        | nil => simp [flattenPairs]
        | cons p ps =>
            rcases p with ⟨plo, phi⟩
            simp only [List.length_cons, flattenPairs]
            rw [show 2 * (ps.length + 1 + 1) - 1 =
                  (2 * (ps.length + 1) - 1) + 2 by omega,
                getD_two_prefix]
            have hlt : 2 * (ps.length + 1) - 1 <
                (plo :: phi :: flattenPairs ps).length := by
              rw [show (plo :: phi :: flattenPairs ps).length =
                2 + 2 * ps.length by
                  simp [flattenPairs_length]
                  omega]
              omega
            rw [List.getD_eq_getElem (plo :: phi :: flattenPairs ps) hi hlt,
              List.getD_eq_getElem (plo :: phi :: flattenPairs ps) carry hlt]
      have htape :
          bubbleTape A (done ++ [lo, hi] ++ flattenPairs ps)
              ((flattenPairs ps).getD (2 * ps.length - 1) hi) ending suffix =
            bubbleTape A (done ++ lo :: hi :: flattenPairs ps)
              ((lo :: hi :: flattenPairs ps).getD
                (2 * (ps.length + 1) - 1) carry) ending suffix := by
        unfold bubbleTape
        rw [hcarry]
        simp [List.append_assoc]
      rw [hhead, htape]

def returnScanClock (revps : List (Bool × Bool)) : Nat :=
  2 * revps.length + 2

/-- Backward pair scan.  `revps` lists the physical pairs from right to left;
the tape therefore contains `revps.reverse` in forward order. -/
theorem sourceCompact_return_scan : ∀ (pre out : List Bool)
    (revps : List (Bool × Bool)) (garbage tail : List Bool),
    (∀ p ∈ revps, ¬(p.1 && !p.2)) →
    run sourceCompactMachine (returnScanClock revps)
      ⟨returnHi,
        (pre ++ out ++ [true, false] ++
          flattenPairs revps.reverse).length - 1,
        pre ++ out ++ [true, false] ++
          flattenPairs revps.reverse ++ garbage ++ tail⟩ =
      ⟨markerLo, pre.length + out.length,
        pre ++ out ++ [true, false] ++
          flattenPairs revps.reverse ++ garbage ++ tail⟩
  | pre, out, [], garbage, tail, _ => by
      rw [returnScanClock]
      simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.reverse_nil,
        flattenPairs, List.append_nil]
      let Q := pre ++ out
      let T := pre ++ out ++ [true, false] ++ garbage ++ tail
      have hf : T.getD (Q.length + 1) false = false := by
        rw [show T = (Q ++ [true]) ++ false :: (garbage ++ tail) by
          simp [T, Q, List.append_assoc]]
        simpa using getD_boundary (Q ++ [true]) (garbage ++ tail) false
      have ht : T.getD Q.length false = true := by
        rw [show T = Q ++ true :: (false :: garbage ++ tail) by
          simp [T, Q, List.append_assoc]]
        exact getD_boundary Q (false :: garbage ++ tail) true
      have h1 : run sourceCompactMachine 1 ⟨returnHi, Q.length + 1, T⟩ =
          ⟨returnLo false, Q.length, T⟩ := by
        rw [run_succ, run_zero, step_returnHi _ _ false hf]
        congr 1 <;> omega
      have h2 : run sourceCompactMachine 1 ⟨returnLo false, Q.length, T⟩ =
          ⟨markerLo, Q.length, T⟩ := by
        rw [run_succ, run_zero, step_returnLo_finish _ _ ht]
      rw [show (pre ++ out ++ [true, false]).length - 1 = Q.length + 1 by
        simp [Q]; omega]
      change run sourceCompactMachine 2 ⟨returnHi, Q.length + 1, T⟩ = _
      rw [show 2 = 1 + 1 by omega, run_add, h1, h2]
      simp [Q, T]
  | pre, out, (lo, hi) :: revps, garbage, tail, hvalid => by
      have hp : ¬(lo && !hi) := hvalid (lo, hi) (by simp)
      have hps : ∀ p ∈ revps, ¬(p.1 && !p.2) := by
        intro p hm
        exact hvalid p (by simp [hm])
      rw [returnScanClock, List.length_cons,
        show 2 * (revps.length + 1) + 2 =
          2 + (2 * revps.length + 2) by omega,
        run_add]
      have hshape : flattenPairs ((lo, hi) :: revps).reverse =
          flattenPairs revps.reverse ++ [lo, hi] := by
        simp [flattenPairs_append, flattenPairs]
      rw [hshape]
      let A := pre ++ out ++ [true, false] ++ flattenPairs revps.reverse
      have htwo : run sourceCompactMachine 2
          ⟨returnHi, (A ++ [lo, hi]).length - 1,
            A ++ [lo, hi] ++ garbage ++ tail⟩ =
          ⟨returnHi, A.length - 1,
            A ++ [lo, hi] ++ garbage ++ tail⟩ := by
        let T := A ++ [lo, hi] ++ garbage ++ tail
        have hhi : T.getD (A.length + 1) false = hi := by
          rw [show T = (A ++ [lo]) ++ hi :: (garbage ++ tail) by
            simp [T, List.append_assoc]]
          simpa using getD_boundary (A ++ [lo]) (garbage ++ tail) hi
        have hlo : T.getD A.length false = lo := by
          rw [show T = A ++ lo :: (hi :: garbage ++ tail) by
            simp [T, List.append_assoc]]
          exact getD_boundary A (hi :: garbage ++ tail) lo
        have h1 : run sourceCompactMachine 1
            ⟨returnHi, A.length + 1, T⟩ =
            ⟨returnLo hi, A.length, T⟩ := by
          rw [run_succ, run_zero, step_returnHi _ _ hi hhi]
          congr 1 <;> omega
        have h2 : run sourceCompactMachine 1
            ⟨returnLo hi, A.length, T⟩ =
            ⟨returnHi, A.length - 1, T⟩ := by
          rw [run_succ, run_zero,
            step_returnLo_continue _ _ lo hi hlo hp]
        rw [show (A ++ [lo, hi]).length - 1 = A.length + 1 by simp]
        change run sourceCompactMachine 2 ⟨returnHi, A.length + 1, T⟩ = _
        rw [show 2 = 1 + 1 by omega, run_add, h1, h2]
      have htwo' : run sourceCompactMachine 2
          ⟨returnHi,
            (pre ++ out ++ [true, false] ++
              (flattenPairs revps.reverse ++ [lo, hi])).length - 1,
            pre ++ out ++ [true, false] ++
              (flattenPairs revps.reverse ++ [lo, hi]) ++ garbage ++ tail⟩ =
          ⟨returnHi, A.length - 1,
            A ++ [lo, hi] ++ garbage ++ tail⟩ := by
        simpa [A, List.append_assoc] using htwo
      rw [htwo']
      have ih := sourceCompact_return_scan pre out revps
        (lo :: hi :: garbage) tail hps
      simp only [returnScanClock] at ih
      have ih' : run sourceCompactMachine (2 * revps.length + 2)
          ⟨returnHi, A.length - 1,
            A ++ [lo, hi] ++ garbage ++ tail⟩ =
          ⟨markerLo, pre.length + out.length,
            pre ++ out ++ [true, false] ++
              (flattenPairs revps.reverse ++ [lo, hi]) ++ garbage ++ tail⟩ := by
        simpa [A, List.append_assoc] using ih
      rw [ih']

def returnPairsClock (ps : List (Bool × Bool)) : Nat :=
  2 * ps.length + 3

theorem sourceCompact_return_pairs (pre out : List Bool)
    (ps : List (Bool × Bool)) (garbage tail : List Bool)
    (hvalid : ∀ p ∈ ps, ¬(p.1 && !p.2)) :
    run sourceCompactMachine (returnPairsClock ps)
      ⟨returnStart,
        (pre ++ out ++ [true, false] ++ flattenPairs ps).length,
        pre ++ out ++ [true, false] ++ flattenPairs ps ++ garbage ++ tail⟩ =
      ⟨markerLo, pre.length + out.length,
        pre ++ out ++ [true, false] ++ flattenPairs ps ++ garbage ++ tail⟩ := by
  rw [returnPairsClock,
    show 2 * ps.length + 3 = 1 + returnScanClock ps.reverse by
      simp [returnScanClock]; omega,
    run_add, run_succ, run_zero]
  simp only [step, sourceCompactMachine, moveHead]
  have hs := sourceCompact_return_scan pre out ps.reverse garbage tail (by
    intro p hp
    exact hvalid p (by simpa using hp))
  simpa [returnScanClock] using hs

theorem dataPairs_not_01 (bits : List Bool) :
    ∀ p ∈ dataPairs bits, ¬(!p.1 && p.2) := by
  intro p hp
  simp only [dataPairs, List.mem_map] at hp
  rcases hp with ⟨b, hb, rfl⟩
  cases b <;> simp

theorem dataTermPairs_not_10 (bits : List Bool) :
    ∀ p ∈ dataPairs bits ++ [(false, true)], ¬(p.1 && !p.2) := by
  intro p hp
  rw [List.mem_append] at hp
  rcases hp with hp | hp
  · simp only [dataPairs, List.mem_map] at hp
    rcases hp with ⟨b, hb, rfl⟩
    cases b <;> simp
  · simp only [List.mem_singleton] at hp
    subst p
    simp

def sourceCompactRoundClock (rest : List Bool) : Nat :=
  9 + shiftPairsClock (dataPairs rest) + 6 +
    returnPairsClock (dataPairs rest ++ [(false, true)])

/-- One exact decoding round.  The later archive tail is untouched; the one
cell vacated by the left shift is accumulated immediately before it. -/
theorem sourceCompact_round (pre out rest garbage tail : List Bool)
    (b : Bool) :
    run sourceCompactMachine (sourceCompactRoundClock rest)
        ⟨markerLo, pre.length + out.length,
          compactTape pre out (b :: rest) garbage tail⟩ =
      ⟨markerLo, pre.length + (out ++ [b]).length,
        compactTape pre (out ++ [b]) rest (true :: garbage) tail⟩ := by
  let A := pre ++ out ++ [b, true, false]
  have hr := sourceCompact_rewrite pre out rest garbage tail b
  have hs := sourceCompact_shift_pairs A [] b (dataPairs rest)
    [false, true] (garbage ++ tail) (dataPairs_not_01 rest)
  have hlo := sourceCompact_copy_lo A (flattenPairs (dataPairs rest))
    ((flattenPairs (dataPairs rest)).getD
      (2 * (dataPairs rest).length - 1) b)
    false [true] (garbage ++ tail)
  have hhi := sourceCompact_copy_hi_finish A
    (flattenPairs (dataPairs rest) ++ [false]) false []
    (garbage ++ tail)
  let ps := dataPairs rest ++ [(false, true)]
  have hret := sourceCompact_return_pairs pre (out ++ [b]) ps
    [true] (garbage ++ tail) (dataTermPairs_not_10 rest)
  have hflat : flattenPairs (dataPairs rest) ++ [false, true] =
      encodeD rest := by
    simpa [flattenPairs_append, flattenPairs] using flattenPairs_dataPairs rest
  have hs' := hs
  simp only [List.length_nil, Nat.add_zero, List.nil_append] at hs'
  rw [sourceCompactRoundClock,
    show 9 + shiftPairsClock (dataPairs rest) + 6 +
        returnPairsClock ps =
      9 + (shiftPairsClock (dataPairs rest) +
        (3 + (3 + returnPairsClock ps))) by omega,
    run_add, hr]
  rw [← hflat, run_add, hs']
  have hlo' := hlo
  simp only [flattenPairs_length, List.length_append, List.length_singleton]
    at hlo'
  rw [run_add, hlo']
  have hhi' := hhi
  simp only [flattenPairs_length, List.length_append, List.length_singleton]
    at hhi'
  have hhi'' : run sourceCompactMachine 3
      ⟨holeHi false, A.length + 2 * (dataPairs rest).length + 1,
        bubbleTape A (flattenPairs (dataPairs rest) ++ [false]) false [true]
          (garbage ++ tail)⟩ =
      ⟨returnStart, A.length + 2 * (dataPairs rest).length + 2,
        bubbleTape A (flattenPairs (dataPairs rest) ++ [false, true]) true []
          (garbage ++ tail)⟩ := by
    simpa [List.append_assoc] using hhi'
  rw [run_add, hhi'']
  have hpos : A.length + 2 * (dataPairs rest).length + 2 =
      (pre ++ (out ++ [b]) ++ [true, false] ++
        flattenPairs (dataPairs rest ++ [(false, true)])).length := by
    simp [A, dataPairs, flattenPairs_length]
    omega
  rw [hpos]
  simpa [ps, A, hflat, compactTape, bubbleTape, flattenPairs_append,
    flattenPairs, List.append_assoc] using hret

def sourceCompactRoundsClock : List Bool → Nat
  | [] => 0
  | _ :: rest => sourceCompactRoundClock rest + sourceCompactRoundsClock rest

theorem sourceCompact_rounds (pre garbage tail : List Bool) :
    ∀ (out rest : List Bool),
    run sourceCompactMachine (sourceCompactRoundsClock rest)
        ⟨markerLo, pre.length + out.length,
          compactTape pre out rest garbage tail⟩ =
      ⟨markerLo, pre.length + (out ++ rest).length,
        compactTape pre (out ++ rest) []
          (List.replicate rest.length true ++ garbage) tail⟩
  | out, [] => by simp [sourceCompactRoundsClock, compactTape]
  | out, b :: rest => by
      rw [sourceCompactRoundsClock, run_add,
        sourceCompact_round pre out rest garbage tail b]
      have ih := sourceCompact_rounds pre (true :: garbage) tail
        (out ++ [b]) rest
      rw [ih]
      have hout : out ++ [b] ++ rest = out ++ b :: rest := by simp
      have hg : List.replicate rest.length true ++ true :: garbage =
          List.replicate (b :: rest).length true ++ garbage := by
        rw [show true :: garbage = [true] ++ garbage by rfl,
          show [true] = List.replicate 1 true by rfl,
          ← List.append_assoc,
          ← List.replicate_add rest.length 1 true]
        simp
      rw [hout, hg]

def sourceCompactClock (bits : List Bool) : Nat :=
  2 + sourceCompactRoundsClock bits + 4

/-- Complete fixed in-place decoding from the selector's halting head. -/
theorem sourceCompact_run (pre bits tail : List Bool) :
    run sourceCompactMachine (sourceCompactClock bits)
        ⟨backHi, pre.length + 2,
          pre ++ [true, false] ++ encodeD bits ++ tail⟩ =
      ⟨done, pre.length + bits.length + 3,
        pre ++ bits ++ [true, false] ++ encodeD [] ++
          List.replicate bits.length true ++ tail⟩ := by
  rw [sourceCompactClock,
    show 2 + sourceCompactRoundsClock bits + 4 =
      2 + (sourceCompactRoundsClock bits + 4) by omega,
    run_add]
  have hstart := sourceCompact_start pre [] bits [] tail
  simp only [List.length_nil, Nat.add_zero, compactTape, List.nil_append,
    List.append_nil] at hstart
  have hrounds := sourceCompact_rounds pre [] tail [] bits
  simp only [List.length_nil, Nat.add_zero, compactTape, List.nil_append,
    List.append_nil] at hrounds
  rw [hstart, run_add, hrounds]
  exact sourceCompact_finish pre bits (List.replicate bits.length true) tail

theorem sourceCompact_halted (pre bits tail : List Bool) :
    sourceCompactMachine.halt
      (run sourceCompactMachine (sourceCompactClock bits)
        ⟨backHi, pre.length + 2,
          pre ++ [true, false] ++ encodeD bits ++ tail⟩).st = true := by
  rw [sourceCompact_run]
  rfl

/-! ## Head-preserving composition with the fixed selector -/

/-- Sequential composition whose handoff preserves the current head.  This is
the correct interface here because the selector already halts at the selected
payload origin. -/
def headSeqMachine (M1 M2 : Machine) : Machine where
  State := M1.State ⊕ M2.State
  fin := letI := M1.fin; letI := M2.fin; inferInstance
  dec := letI := M1.dec; letI := M2.dec; inferInstance
  start := Sum.inl M1.start
  halt := fun s => match s with
    | .inl _ => false
    | .inr s2 => M2.halt s2
  δ := fun s b => match s with
    | .inl s1 =>
        if M1.halt s1 then (Sum.inr M2.start, none, 2)
        else (Sum.inl (M1.δ s1 b).1, (M1.δ s1 b).2.1,
          (M1.δ s1 b).2.2)
    | .inr s2 =>
        (Sum.inr (M2.δ s2 b).1, (M2.δ s2 b).2.1,
          (M2.δ s2 b).2.2)
  accept := fun _ => false

def headInlCfg (M1 M2 : Machine) (c : Cfg M1) : Cfg (headSeqMachine M1 M2) :=
  ⟨Sum.inl c.st, c.hd, c.tp⟩

def headInrCfg (M1 M2 : Machine) (c : Cfg M2) : Cfg (headSeqMachine M1 M2) :=
  ⟨Sum.inr c.st, c.hd, c.tp⟩

theorem headSeq_step_inl (M1 M2 : Machine) (c : Cfg M1)
    (h : M1.halt c.st = false) :
    step (headSeqMachine M1 M2) (headInlCfg M1 M2 c) =
      headInlCfg M1 M2 (step M1 c) := by
  simp [step, headSeqMachine, headInlCfg, h]

theorem headSeq_step_handoff (M1 M2 : Machine) (c : Cfg M1)
    (h : M1.halt c.st = true) :
    step (headSeqMachine M1 M2) (headInlCfg M1 M2 c) =
      headInrCfg M1 M2 ⟨M2.start, c.hd, c.tp⟩ := by
  simp [step, headSeqMachine, headInlCfg, headInrCfg, h, moveHead]

theorem headSeq_step_inr (M1 M2 : Machine) (c : Cfg M2) :
    step (headSeqMachine M1 M2) (headInrCfg M1 M2 c) =
      headInrCfg M1 M2 (step M2 c) := by
  by_cases h : M2.halt c.st = true
  · rw [step_of_halted M2 h]
    apply step_of_halted
    simpa [headSeqMachine, headInrCfg] using h
  · have h' : M2.halt c.st = false := by simpa using h
    simp [step, headSeqMachine, headInrCfg, h']

theorem headSeq_run_inr (M1 M2 : Machine) (c : Cfg M2) (t : Nat) :
    run (headSeqMachine M1 M2) t (headInrCfg M1 M2 c) =
      headInrCfg M1 M2 (run M2 t c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, ih, headSeq_step_inr, ← run_succ]

theorem headSeq_run_inl (M1 M2 : Machine) (c : Cfg M1) (t : Nat)
    (h : ∀ s < t, M1.halt (run M1 s c).st = false) :
    run (headSeqMachine M1 M2) t (headInlCfg M1 M2 c) =
      headInlCfg M1 M2 (run M1 t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, ih (fun s hs => h s (by omega)),
        headSeq_step_inl M1 M2 _ (h t (by omega)), ← run_succ]

/-- Exact head-preserving composition, with early-halting slack absorbed by
the model's frozen halt semantics. -/
theorem headSeq_run (M1 M2 : Machine) (T0 T1 T2 : List Bool)
    (t1 t2 p1 p2 : Nat) (s1 : M1.State) (s2 : M2.State)
    (h1 : run M1 t1 (init M1 T0) = ⟨s1, p1, T1⟩)
    (hh1 : M1.halt s1 = true)
    (h2 : run M2 t2 ⟨M2.start, p1, T1⟩ = ⟨s2, p2, T2⟩)
    (hh2 : M2.halt s2 = true) :
    run (headSeqMachine M1 M2) (t1 + 1 + t2)
        (init (headSeqMachine M1 M2) T0) =
      ⟨Sum.inr s2, p2, T2⟩ := by
  have hex : ∃ t, M1.halt (run M1 t (init M1 T0)).st = true :=
    ⟨t1, by rw [h1]; exact hh1⟩
  let tm := Nat.find hex
  have htm : M1.halt (run M1 tm (init M1 T0)).st = true :=
    Nat.find_spec hex
  have htmle : tm ≤ t1 := Nat.find_le (by rw [h1]; exact hh1)
  have hfrozen : run M1 tm (init M1 T0) = ⟨s1, p1, T1⟩ := by
    rw [← run_stable M1 T0 htmle htm, h1]
  have hno : ∀ s < tm, M1.halt (run M1 s (init M1 T0)).st = false := by
    intro s hs
    simpa using Nat.find_min hex hs
  have hleft := headSeq_run_inl M1 M2 (init M1 T0) tm hno
  rw [hfrozen] at hleft
  have hright := headSeq_run_inr M1 M2
    (⟨M2.start, p1, T1⟩ : Cfg M2) t2
  rw [h2] at hright
  have hhalt : (headSeqMachine M1 M2).halt
      (Sum.inr s2) = true := by simpa [headSeqMachine] using hh2
  rw [show t1 + 1 + t2 = tm + (1 + (t2 + (t1 - tm))) by omega,
    run_add]
  rw [show init (headSeqMachine M1 M2) T0 =
      headInlCfg M1 M2 (init M1 T0) from rfl]
  rw [hleft, run_add]
  have hswitch := headSeq_step_handoff M1 M2
    (⟨s1, p1, T1⟩ : Cfg M1) hh1
  rw [show run (headSeqMachine M1 M2) 1
      (headInlCfg M1 M2 (⟨s1, p1, T1⟩ : Cfg M1)) =
      headInrCfg M1 M2 ⟨M2.start, p1, T1⟩ by
        rw [run_succ, run_zero]; exact hswitch,
    run_add, hright]
  exact run_of_halted (headSeqMachine M1 M2) hhalt _

def selectedPrefixPairs (d : Nat) (preBlocks : List (List Bool)) :
    List (Bool × Bool) :=
  List.replicate preBlocks.length (true, true) ++
    List.replicate d (true, true) ++ [(false, true)] ++
    preBlocks.flatMap passedSourceBlock

def selectedPrefix (d : Nat) (preBlocks : List (List Bool)) : List Bool :=
  flattenPairs (selectedPrefixPairs d preBlocks)

def selectedTail (rest : List (List Bool)) : List Bool :=
  flattenPairs (rest.flatMap freshSourceBlock)

theorem selected_progress_shape (d : Nat) (preBlocks : List (List Bool))
    (bits : List Bool) (rest : List (List Bool)) :
    flattenPairs (progressPairs d preBlocks [] (bits :: rest)) =
      selectedPrefix d preBlocks ++ [true, false] ++ encodeD bits ++
        selectedTail rest := by
  simp [progressPairs, selectedPrefix, selectedPrefixPairs, selectedTail,
    freshSourceBlock, flattenPairs_append, flattenPairs,
    flattenPairs_dataPairs, List.append_assoc]
  simpa [List.append_assoc] using congrArg
    (fun z => z ++ selectedTail rest) (flattenPairs_dataPairs bits)

theorem selected_progress_head (d : Nat)
    (preBlocks : List (List Bool)) :
    2 * (preBlocks.length + d + 1 +
        (preBlocks.flatMap passedSourceBlock).length + 1) =
      (selectedPrefix d preBlocks).length + 2 := by
  simp [selectedPrefix, selectedPrefixPairs]
  omega

def sourceSelectCompactMachine : Machine :=
  headSeqMachine sourceSelectMachine sourceCompactMachine

def sourceSelectCompactClock (d : Nat) (preBlocks : List (List Bool))
    (bits : List Bool) : Nat :=
  sourceSelectClock d preBlocks + 1 + sourceCompactClock bits

/-- The fixed selector and fixed in-place compactor form one fixed machine.
Its final tape contains the exact raw selected payload contiguously at the
former selected-header position, followed by only local garbage and the
untouched later archive. -/
theorem sourceSelectCompact_run (d : Nat) (preBlocks : List (List Bool))
    (bits : List Bool) (rest : List (List Bool)) :
    run sourceSelectCompactMachine
        (sourceSelectCompactClock d preBlocks bits)
        (init sourceSelectCompactMachine
          (flattenPairs (progressPairs d [] preBlocks (bits :: rest)))) =
      ⟨Sum.inr done,
        (selectedPrefix d preBlocks).length + bits.length + 3,
        selectedPrefix d preBlocks ++ bits ++ [true, false] ++ encodeD [] ++
          List.replicate bits.length true ++ selectedTail rest⟩ := by
  have hsel := sourceSelect_run d preBlocks bits rest
  rw [selected_progress_shape, selected_progress_head] at hsel
  have hcomp := sourceCompact_run (selectedPrefix d preBlocks) bits
    (selectedTail rest)
  exact headSeq_run sourceSelectMachine sourceCompactMachine
    (flattenPairs (progressPairs d [] preBlocks (bits :: rest)))
    (selectedPrefix d preBlocks ++ [true, false] ++ encodeD bits ++
      selectedTail rest)
    (selectedPrefix d preBlocks ++ bits ++ [true, false] ++ encodeD [] ++
      List.replicate bits.length true ++ selectedTail rest)
    (sourceSelectClock d preBlocks) (sourceCompactClock bits)
    ((selectedPrefix d preBlocks).length + 2)
    ((selectedPrefix d preBlocks).length + bits.length + 3)
    SourceSelectState.done done hsel rfl hcomp rfl

theorem sourceSelectCompact_payload (d : Nat)
    (preBlocks : List (List Bool)) (bits : List Bool)
    (rest : List (List Bool)) :
    let cf := run sourceSelectCompactMachine
      (sourceSelectCompactClock d preBlocks bits)
      (init sourceSelectCompactMachine
        (flattenPairs (progressPairs d [] preBlocks (bits :: rest))))
    cf.tp.drop (selectedPrefix d preBlocks).length =
      bits ++ [true, false] ++ encodeD [] ++
        List.replicate bits.length true ++ selectedTail rest := by
  rw [sourceSelectCompact_run]
  simp

/-! ## Canonical scheduled-literal specialization -/

theorem literalLookupTape_append_roundInv (w : List Bool) (l : Lit)
    (suffix : List Bool) :
    RoundInv (literalLookupTape w l ++ suffix) l.1
      (signedLookupAssignment w l.1 l.2).length := by
  let A := signedLookupAssignment w l.1 l.2
  have hfresh : RoundInv (literalLookupTape w l) l.1 A.length := by
    simpa [literalLookupTape, A] using encode_roundInv A l.1
  have hlen : (literalLookupTape w l).length = 4 * l.1 + 8 := by
    simp [literalLookupTape, encode, signedLookupAssignment_length,
      PallLean.Paper93.DeepMath.PathB.CookLevinInP.double_length]
    ring
  have hAlen : A.length = l.1 + 1 := by
    dsimp only [A]
    exact signedLookupAssignment_length _ _ _
  have hread : ∀ p, p < (literalLookupTape w l).length →
      (literalLookupTape w l ++ suffix).getD p false =
        (literalLookupTape w l).getD p false := by
    intro p hp
    exact List.getD_append (literalLookupTape w l) suffix false p hp
  change RoundInv (literalLookupTape w l ++ suffix) l.1 A.length
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi1 hi2
    rw [hread (2 * i) ?_, hread (2 * i + 1) ?_]
    exact hfresh.ctr i hi1 hi2
    all_goals rw [hlen]; omega
  · rw [hread (2 * l.1 + 2) ?_]
    exact hfresh.seplo
    rw [hlen]; omega
  · rw [hread (2 * l.1 + 3) ?_]
    exact hfresh.sephi
    rw [hlen]; omega
  · intro j hj
    rw [hread (2 * l.1 + 4 + 2 * j) ?_,
      hread (2 * l.1 + 5 + 2 * j) ?_]
    exact hfresh.dat j hj
    all_goals rw [hlen]; omega
  · rw [hread (2 * l.1 + 4 + 2 * A.length) ?_]
    exact hfresh.rendlo
    rw [hlen, hAlen]; omega
  · rw [hread (2 * l.1 + 5 + 2 * A.length) ?_]
    exact hfresh.rendhi
    rw [hlen, hAlen]; omega
  · rw [hread 1 ?_]
    exact hfresh.lsent
    rw [hlen]; omega

/-- Canonical specialization: one fixed machine selects from the tape archive,
decodes the selected doubled block in place, and exposes the exact raw lookup
payload. -/
theorem sourceSelectCompact_scheduled (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let preBlocks := schedule.take t
    let bits := literalLookupTape w (scheduledLiteral x t)
    let rest := schedule.drop (t + 1)
    let pre := selectedPrefix (B - t) preBlocks
    let cf := run sourceSelectCompactMachine
      (sourceSelectCompactClock (B - t) preBlocks bits)
      (init sourceSelectCompactMachine (sourceSelectorInput B t schedule))
    cf.st = Sum.inr done ∧
      cf.tp.drop pre.length =
        bits ++ [true, false] ++ encodeD [] ++
          List.replicate bits.length true ++ selectedTail rest ∧
      RoundInv (cf.tp.drop pre.length)
        (scheduledLiteral x t).1
        (signedLookupAssignment w (scheduledLiteral x t).1
          (scheduledLiteral x t).2).length := by
  dsimp only
  let B := (decodedLiterals x).length
  let schedule := literalTapeSchedule x w
  let bits := literalLookupTape w (scheduledLiteral x t)
  let preBlocks := schedule.take t
  let rest := schedule.drop (t + 1)
  let pre := selectedPrefix (B - t) preBlocks
  have hget : schedule.getD t [] = bits := by
    dsimp only [schedule, bits]
    exact literalTapeSchedule_getD x w ht
  have hslen : schedule.length = B := by
    simp [schedule, B, literalTapeSchedule]
  have hts : t < schedule.length := by simpa [hslen] using ht
  have hbit : schedule[t] = bits := by
    rw [← hget, List.getD_eq_getElem schedule [] hts]
  have hsplit : schedule = preBlocks ++ bits :: rest := by
    dsimp only [preBlocks, rest]
    conv_lhs => rw [← List.take_append_drop t schedule]
    rw [List.drop_eq_getElem_cons hts, hbit]
  have hprelen : preBlocks.length = t := by
    dsimp only [preBlocks]
    rw [List.length_take, Nat.min_eq_left hts.le]
  have hinput : sourceSelectorInput B t schedule =
      flattenPairs (progressPairs (B - t) [] preBlocks (bits :: rest)) := by
    rw [sourceSelectorInput, progressPairs, sourceArchive, hsplit]
    simp [hprelen, List.append_assoc]
  rw [hinput, sourceSelectCompact_run]
  dsimp only [pre]
  constructor
  · rfl
  constructor
  · simp [List.append_assoc, rest, schedule]
  · have hdrop :
        (selectedPrefix (B - t) preBlocks ++ bits ++ [true, false] ++
          encodeD [] ++ List.replicate bits.length true ++
          selectedTail rest).drop (selectedPrefix (B - t) preBlocks).length =
        bits ++ [true, false] ++ encodeD [] ++
          List.replicate bits.length true ++ selectedTail rest := by
        simp [List.append_assoc]
    rw [hdrop]
    simpa [bits, List.append_assoc] using
      (literalLookupTape_append_roundInv w (scheduledLiteral x t)
        ([true, false] ++ encodeD [] ++ List.replicate bits.length true ++
          selectedTail rest))

theorem sourceSelectCompact_scheduled_halts (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let preBlocks := schedule.take t
    let bits := literalLookupTape w (scheduledLiteral x t)
    (sourceSelectCompactMachine.halt
      (run sourceSelectCompactMachine
        (sourceSelectCompactClock (B - t) preBlocks bits)
        (init sourceSelectCompactMachine
          (sourceSelectorInput B t schedule))).st) = true := by
  dsimp only
  have h := sourceSelectCompact_scheduled x w ht
  rw [h.1]
  rfl

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact.sourceCompact_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact.headSeq_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact.sourceSelectCompact_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact.sourceSelectCompact_payload
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact.sourceSelectCompact_scheduled
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact.sourceSelectCompact_scheduled_halts
