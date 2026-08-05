import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeRelativePrefix

/-!
# Left-boundary safety calculus for runtime lookup composition

The fixed runtime lookup is assembled from head-preserving sequential
compositors.  This file proves that `LeftSafeRun` composes through their left
phase, one-step handoff, right phase, early halt, and unused frozen slack.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeLeftSafety

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled

/-- The fixed source selector never issues a left move at all; its backward
control transfer is an explicit reset. -/
theorem sourceSelect_no_left (s : SourceSelectState) (b : Bool) :
    (sourceSelectMachine.δ s b).2.2 ≠ 0 := by
  cases s <;> simp [sourceSelectMachine] <;> split_ifs <;> simp_all

theorem sourceSelect_leftSafe_any (c : Cfg sourceSelectMachine) (n : Nat) :
    LeftSafeRun sourceSelectMachine c n := by
  intro i _ _ hmove
  exact absurd hmove (sourceSelect_no_left _ _)

open SourceRewindState

theorem sourceRewind_boot_leftSafe (pre : List Bool)
    (mid : List (Bool × Bool)) (tail : List Bool) :
    LeftSafeRun sourceRewindMachine
      ⟨back0, pre.length + (rewindRaw mid).length + 3,
        rewindTape pre mid ([true, false, false, true] ++ tail)⟩ 4 := by
  intro i hi _ _
  interval_cases i <;>
    simp [run_succ, step, sourceRewindMachine, moveHead, rewindRaw]

theorem sourceRewind_pair_leftSafe (P : List Bool) (lo hi : Bool)
    (R : List Bool) (seen : Bool) (hP : 0 < P.length) :
    LeftSafeRun sourceRewindMachine
      ⟨scanHi seen, (P ++ [lo, hi]).length - 1,
        P ++ [lo, hi] ++ R⟩ 2 := by
  let T := P ++ [lo, hi] ++ R
  have hhi : T.getD (P.length + 1) false = hi := by
    simp [T, List.getD_eq_getElem?_getD]
  have hstep : run sourceRewindMachine 1
      ⟨scanHi seen, (P ++ [lo, hi]).length - 1, T⟩ =
      ⟨scanLo seen hi, P.length, T⟩ := by
    rw [run_succ, run_zero]
    rw [show (P ++ [lo, hi]).length - 1 = P.length + 1 by simp]
    rw [List.getD_eq_getElem?_getD] at hhi
    simp [step, sourceRewindMachine, moveHead, hhi]
  intro i hiN _ _
  have hiCases : i = 0 ∨ i = 1 := by omega
  rcases hiCases with rfl | rfl
  · simpa [T] using (show 0 < (P ++ [lo, hi]).length - 1 by simp)
  · rw [hstep]
    exact hP

theorem sourceRewind_take_end_leftSafe (P R : List Bool)
    (hP : 0 < P.length) :
    LeftSafeRun sourceRewindMachine
      ⟨scanHi false, (P ++ [true, false]).length - 1,
        P ++ [true, false] ++ R⟩ 2 :=
  sourceRewind_pair_leftSafe P true false R false hP

theorem sourceRewind_finish_leftSafe (pre R : List Bool) :
    LeftSafeRun sourceRewindMachine
      ⟨scanHi true, (pre ++ [true, false]).length - 1,
        pre ++ [true, false] ++ R⟩ 2 := by
  let T := pre ++ [true, false] ++ R
  have hhi : T.getD (pre.length + 1) false = false := by
    simp [T, List.getD_eq_getElem?_getD]
  have hlo : T.getD pre.length false = true := by
    simp [T, List.getD_eq_getElem?_getD]
  have hstep : run sourceRewindMachine 1
      ⟨scanHi true, (pre ++ [true, false]).length - 1, T⟩ =
      ⟨scanLo true false, pre.length, T⟩ := by
    rw [run_succ, run_zero]
    rw [show (pre ++ [true, false]).length - 1 = pre.length + 1 by simp]
    rw [List.getD_eq_getElem?_getD] at hhi
    simp [step, sourceRewindMachine, moveHead, hhi]
  intro i hiN _ hmove
  have hiCases : i = 0 ∨ i = 1 := by omega
  rcases hiCases with rfl | rfl
  · simp
  · rw [hstep] at hmove ⊢
    rw [List.getD_eq_getElem?_getD] at hlo
    simp [sourceRewindMachine, hlo] at hmove

theorem sourceRewind_pairs_leftSafe : ∀ (pre : List Bool)
    (revps : List (Bool × Bool)) (tail : List Bool),
    NoRendPair revps →
    LeftSafeRun sourceRewindMachine
      ⟨scanHi true,
        (pre ++ [true, false] ++ flattenPairs revps.reverse).length - 1,
        pre ++ [true, false] ++ flattenPairs revps.reverse ++ tail⟩
      (sourceRewindPairsClock revps)
  | pre, [], tail, _ => by simp [sourceRewindPairsClock, LeftSafeRun]
  | pre, (lo, hi) :: revps, tail, hvalid => by
      have hp : ¬(lo && !hi) := hvalid (lo, hi) (by simp)
      have hps : NoRendPair revps := by
        intro p hp'
        exact hvalid p (by simp [hp'])
      rw [sourceRewindPairsClock, List.length_cons]
      rw [show 2 * (revps.length + 1) =
        2 + sourceRewindPairsClock revps by
          simp [sourceRewindPairsClock]; omega]
      let P := pre ++ [true, false] ++ flattenPairs revps.reverse
      have hsPair : LeftSafeRun sourceRewindMachine
          ⟨scanHi true, (P ++ [lo, hi]).length - 1,
            P ++ [lo, hi] ++ tail⟩ 2 :=
        sourceRewind_pair_leftSafe P lo hi tail true (by simp [P])
      have hpRun := sourceRewind_pair P lo hi tail true hp
      have hsRest := sourceRewind_pairs_leftSafe pre revps
        (lo :: hi :: tail) hps
      have hshape : flattenPairs ((lo, hi) :: revps).reverse =
          flattenPairs revps.reverse ++ [lo, hi] := by
        simp [flattenPairs_append, flattenPairs]
      rw [hshape]
      have hsPair' : LeftSafeRun sourceRewindMachine
          ⟨scanHi true,
            (pre ++ [true, false] ++
              (flattenPairs revps.reverse ++ [lo, hi])).length - 1,
            pre ++ [true, false] ++
              (flattenPairs revps.reverse ++ [lo, hi]) ++ tail⟩ 2 := by
        simpa [P, List.append_assoc] using hsPair
      have hpRun' : run sourceRewindMachine 2
          ⟨scanHi true,
            (pre ++ [true, false] ++
              (flattenPairs revps.reverse ++ [lo, hi])).length - 1,
            pre ++ [true, false] ++
              (flattenPairs revps.reverse ++ [lo, hi]) ++ tail⟩ =
          ⟨scanHi true, P.length - 1, P ++ [lo, hi] ++ tail⟩ := by
        simpa [P, List.append_assoc] using hpRun
      apply leftSafeRun_add hsPair'
      rw [hpRun']
      simpa [P, List.append_assoc] using hsRest

/-- The complete canonical rewind never crosses its own tape origin, even
when the protected archive prefix is empty. -/
theorem sourceRewind_run_leftSafe (pre : List Bool)
    (mid : List (Bool × Bool)) (tail : List Bool) (hmid : NoRendPair mid) :
    LeftSafeRun sourceRewindMachine
      ⟨back0, pre.length + (rewindRaw mid).length + 3,
        rewindTape pre mid ([true, false, false, true] ++ tail)⟩
      (sourceRewindClock mid) := by
  have hsBoot := sourceRewind_boot_leftSafe pre mid tail
  have hb := sourceRewind_boot pre mid tail
  let P := pre ++ [true, false] ++ flattenPairs mid
  let R := [true, false, false, true] ++ tail
  have hsEnd := sourceRewind_take_end_leftSafe P R (by simp [P])
  have he := sourceRewind_take_end P R
  have hsPairs := sourceRewind_pairs_leftSafe pre mid.reverse
    ([true, false] ++ R) (by
      intro p hp
      exact hmid p (by simpa using hp))
  have hpairs := sourceRewind_pairs pre mid.reverse
    ([true, false] ++ R) (by
      intro p hp
      exact hmid p (by simpa using hp))
  have hsFinish := sourceRewind_finish_leftSafe pre
    (flattenPairs mid ++ [true, false] ++ R)
  rw [sourceRewindClock, show 8 + 2 * mid.length =
    4 + (2 + (2 * mid.length + 2)) by omega]
  apply leftSafeRun_add hsBoot
  rw [hb]
  apply leftSafeRun_add (by simpa [P, R, rewindTape, rewindRaw,
    List.append_assoc] using hsEnd)
  rw [show run sourceRewindMachine 2
      ⟨scanHi false, pre.length + (rewindRaw mid).length - 1,
        rewindTape pre mid ([true, false, false, true] ++ tail)⟩ =
      ⟨scanHi true, P.length - 1, P ++ [true, false] ++ R⟩ by
        simpa [P, R, rewindTape, rewindRaw, List.append_assoc] using he]
  have hsPairs' : LeftSafeRun sourceRewindMachine
      ⟨scanHi true, P.length - 1, P ++ [true, false] ++ R⟩
      (2 * mid.length) := by
    convert hsPairs using 1 <;>
      simp [P, R, sourceRewindPairsClock, List.append_assoc] <;> omega
  apply leftSafeRun_add hsPairs'
  rw [show run sourceRewindMachine (2 * mid.length)
      ⟨scanHi true, P.length - 1, P ++ [true, false] ++ R⟩ =
      ⟨scanHi true, (pre ++ [true, false]).length - 1,
        pre ++ [true, false] ++ flattenPairs mid ++ [true, false] ++ R⟩ by
        simpa [sourceRewindPairsClock, P, List.append_assoc] using hpairs]
  simpa [R, List.append_assoc] using hsFinish

open SourceCompactState

theorem sourceCompact_return_pair_leftSafe (P : List Bool)
    (lo hi : Bool) (R : List Bool) (hP : 0 < P.length) :
    LeftSafeRun sourceCompactMachine
      ⟨returnHi, (P ++ [lo, hi]).length - 1, P ++ [lo, hi] ++ R⟩ 2 := by
  let T := P ++ [lo, hi] ++ R
  have hhi : T.getD (P.length + 1) false = hi := by
    simp [T, List.getD_eq_getElem?_getD]
  have hstep : run sourceCompactMachine 1
      ⟨returnHi, (P ++ [lo, hi]).length - 1, T⟩ =
      ⟨returnLo hi, P.length, T⟩ := by
    rw [run_succ, run_zero]
    rw [show (P ++ [lo, hi]).length - 1 = P.length + 1 by simp]
    exact step_returnHi _ _ hi hhi
  intro i hiN _ _
  have hiCases : i = 0 ∨ i = 1 := by omega
  rcases hiCases with rfl | rfl
  · simp
  · rw [hstep]
    exact hP

theorem sourceCompact_return_finish_leftSafe (Q garbage tail : List Bool) :
    LeftSafeRun sourceCompactMachine
      ⟨returnHi, (Q ++ [true, false]).length - 1,
        Q ++ [true, false] ++ garbage ++ tail⟩ 2 := by
  let T := Q ++ [true, false] ++ garbage ++ tail
  have hhi : T.getD (Q.length + 1) false = false := by
    simp [T, List.getD_eq_getElem?_getD]
  have hlo : T.getD Q.length false = true := by
    simp [T, List.getD_eq_getElem?_getD]
  have hstep : run sourceCompactMachine 1
      ⟨returnHi, (Q ++ [true, false]).length - 1, T⟩ =
      ⟨returnLo false, Q.length, T⟩ := by
    rw [run_succ, run_zero]
    rw [show (Q ++ [true, false]).length - 1 = Q.length + 1 by simp]
    exact step_returnHi _ _ false hhi
  intro i hiN _ hmove
  have hiCases : i = 0 ∨ i = 1 := by omega
  rcases hiCases with rfl | rfl
  · simp
  · rw [hstep] at hmove ⊢
    simp only [sourceCompactMachine] at hmove
    rw [hlo] at hmove
    simp at hmove

theorem sourceCompact_return_scan_leftSafe : ∀ (pre out : List Bool)
    (revps : List (Bool × Bool)) (garbage tail : List Bool),
    (∀ p ∈ revps, ¬(p.1 && !p.2)) →
    LeftSafeRun sourceCompactMachine
      ⟨returnHi,
        (pre ++ out ++ [true, false] ++
          flattenPairs revps.reverse).length - 1,
        pre ++ out ++ [true, false] ++
          flattenPairs revps.reverse ++ garbage ++ tail⟩
      (returnScanClock revps)
  | pre, out, [], garbage, tail, _ => by
      simpa [returnScanClock] using
        sourceCompact_return_finish_leftSafe (pre ++ out) garbage tail
  | pre, out, (lo, hi) :: revps, garbage, tail, hvalid => by
      have hp : ¬(lo && !hi) := hvalid (lo, hi) (by simp)
      have hps : ∀ p ∈ revps, ¬(p.1 && !p.2) := by
        intro p hm
        exact hvalid p (by simp [hm])
      rw [returnScanClock, List.length_cons,
        show 2 * (revps.length + 1) + 2 =
          2 + returnScanClock revps by simp [returnScanClock]; omega]
      let P := pre ++ out ++ [true, false] ++ flattenPairs revps.reverse
      have hsPair := sourceCompact_return_pair_leftSafe P lo hi
        (garbage ++ tail) (by simp [P])
      have hpRun := sourceCompact_return_scan pre out ((lo, hi) :: revps)
        garbage tail hvalid
      have htwo := sourceCompact_return_pair_leftSafe P lo hi
        (garbage ++ tail) (by simp [P])
      have hpairRun : run sourceCompactMachine 2
          ⟨returnHi, (P ++ [lo, hi]).length - 1,
            P ++ [lo, hi] ++ garbage ++ tail⟩ =
          ⟨returnHi, P.length - 1,
            P ++ [lo, hi] ++ garbage ++ tail⟩ := by
        have hrun := sourceCompact_return_scan pre out ((lo, hi) :: revps)
          garbage tail hvalid
        -- The public recursive scan theorem exposes the same first pair
        -- through its proof equation; use the primitive pair steps directly.
        let T := P ++ [lo, hi] ++ garbage ++ tail
        have hhi : T.getD (P.length + 1) false = hi := by
          simp [T, List.getD_eq_getElem?_getD]
        have hlo : T.getD P.length false = lo := by
          simp [T, List.getD_eq_getElem?_getD]
        have h1 : run sourceCompactMachine 1
            ⟨returnHi, (P ++ [lo, hi]).length - 1,
              P ++ [lo, hi] ++ garbage ++ tail⟩ =
            ⟨returnLo hi, P.length,
              P ++ [lo, hi] ++ garbage ++ tail⟩ := by
          rw [run_succ, run_zero]
          rw [show (P ++ [lo, hi]).length - 1 = P.length + 1 by simp]
          exact step_returnHi _ _ hi hhi
        rw [show 2 = 1 + 1 by omega, run_add, h1, run_succ, run_zero,
          step_returnLo_continue _ _ lo hi hlo hp]
      have hsRest := sourceCompact_return_scan_leftSafe pre out revps
        (lo :: hi :: garbage) tail hps
      have hshape : flattenPairs ((lo, hi) :: revps).reverse =
          flattenPairs revps.reverse ++ [lo, hi] := by
        simp [flattenPairs_append, flattenPairs]
      rw [hshape]
      have hsPair' : LeftSafeRun sourceCompactMachine
          ⟨returnHi,
            (pre ++ out ++ [true, false] ++
              (flattenPairs revps.reverse ++ [lo, hi])).length - 1,
            pre ++ out ++ [true, false] ++
              (flattenPairs revps.reverse ++ [lo, hi]) ++ garbage ++ tail⟩
          2 := by
        simpa [P, List.append_assoc] using hsPair
      apply leftSafeRun_add hsPair'
      have hpairRun' : run sourceCompactMachine 2
          ⟨returnHi,
            (pre ++ out ++ [true, false] ++
              (flattenPairs revps.reverse ++ [lo, hi])).length - 1,
            pre ++ out ++ [true, false] ++
              (flattenPairs revps.reverse ++ [lo, hi]) ++ garbage ++ tail⟩ =
          ⟨returnHi, P.length - 1,
            P ++ [lo, hi] ++ garbage ++ tail⟩ := by
        simpa [P, List.append_assoc] using hpairRun
      rw [hpairRun']
      simpa [P, List.append_assoc] using hsRest

theorem sourceCompact_return_pairs_leftSafe (pre out : List Bool)
    (ps : List (Bool × Bool)) (garbage tail : List Bool)
    (hvalid : ∀ p ∈ ps, ¬(p.1 && !p.2)) :
    LeftSafeRun sourceCompactMachine
      ⟨returnStart,
        (pre ++ out ++ [true, false] ++ flattenPairs ps).length,
        pre ++ out ++ [true, false] ++ flattenPairs ps ++ garbage ++ tail⟩
      (returnPairsClock ps) := by
  have hs0 : LeftSafeRun sourceCompactMachine
      ⟨returnStart,
        (pre ++ out ++ [true, false] ++ flattenPairs ps).length,
        pre ++ out ++ [true, false] ++ flattenPairs ps ++ garbage ++ tail⟩
      1 := leftSafeRun_one_of_positive (by simp)
  have hstep : run sourceCompactMachine 1
      ⟨returnStart,
        (pre ++ out ++ [true, false] ++ flattenPairs ps).length,
        pre ++ out ++ [true, false] ++ flattenPairs ps ++ garbage ++ tail⟩ =
      ⟨returnHi,
        (pre ++ out ++ [true, false] ++ flattenPairs ps).length - 1,
        pre ++ out ++ [true, false] ++ flattenPairs ps ++ garbage ++ tail⟩ := by
    rw [run_succ, run_zero]
    simp [step, sourceCompactMachine, moveHead]
  rw [returnPairsClock, show 2 * ps.length + 3 =
    1 + returnScanClock ps.reverse by simp [returnScanClock]; omega]
  apply leftSafeRun_add hs0
  rw [hstep]
  have hs := sourceCompact_return_scan_leftSafe pre out ps.reverse
    garbage tail (by
      intro p hp
      exact hvalid p (by simpa using hp))
  simpa [returnScanClock] using hs

theorem sourceCompact_start_leftSafe (pre out rest garbage tail : List Bool) :
    LeftSafeRun sourceCompactMachine
      ⟨backHi, pre.length + out.length + 2,
        compactTape pre out rest garbage tail⟩ 2 := by
  intro i hi _ _
  have hiCases : i = 0 ∨ i = 1 := by omega
  rcases hiCases with rfl | rfl <;>
    simp [run_succ, step, sourceCompactMachine, moveHead]

theorem sourceCompact_rewrite_leftSafe (pre out rest garbage tail : List Bool)
    (b : Bool) :
    LeftSafeRun sourceCompactMachine
      ⟨markerLo, pre.length + out.length,
        compactTape pre out (b :: rest) garbage tail⟩ 9 := by
  let Q := pre ++ out
  let R := encodeD rest ++ garbage ++ tail
  let T0 := Q ++ [true, false, b, b] ++ R
  let T1 := Q ++ [true, false, false, b] ++ R
  let T2 := Q ++ [true, true, false, b] ++ R
  let T3 := Q ++ [b, true, false, b] ++ R
  have hT : compactTape pre out (b :: rest) garbage tail = T0 := by
    simp [compactTape, encodeD, T0, Q, R, List.append_assoc]
  have hlo : T0.getD (Q.length + 2) false = b := by
    simp [T0, List.getD_eq_getElem?_getD]
  have hhi : T0.getD (Q.length + 3) false = b := by
    simp [T0, List.getD_eq_getElem?_getD]
  have hw1 : writeAt T0 (Q.length + 2) false = T1 := by
    simp [T0, T1, writeAt]
  have hw2 : writeAt T1 (Q.length + 1) true = T2 := by
    simp [T1, T2, writeAt]
  have hw3 : writeAt T2 Q.length b = T3 := by
    simp [T2, T3, writeAt]
  have h1 : run sourceCompactMachine 1 ⟨markerLo, Q.length, T0⟩ =
      ⟨markerHi, Q.length + 1, T0⟩ := by
    rw [run_succ, run_zero, step_markerLo]
  have h2 : run sourceCompactMachine 1 ⟨markerHi, Q.length + 1, T0⟩ =
      ⟨sourceLo, Q.length + 2, T0⟩ := by
    rw [run_succ, run_zero, step_markerHi]
  have h3 : run sourceCompactMachine 1 ⟨sourceLo, Q.length + 2, T0⟩ =
      ⟨sourceHi b, Q.length + 3, T0⟩ := by
    rw [run_succ, run_zero, step_sourceLo _ _ b hlo]
  have h4 : run sourceCompactMachine 1 ⟨sourceHi b, Q.length + 3, T0⟩ =
      ⟨rewriteDataLo b, Q.length + 2, T0⟩ := by
    rw [run_succ, run_zero, step_sourceHi_data _ _ b hhi]
    congr 1 <;> omega
  have h5 : run sourceCompactMachine 1 ⟨rewriteDataLo b, Q.length + 2, T0⟩ =
      ⟨rewriteMarkerHi b, Q.length + 1, T1⟩ := by
    rw [run_succ, run_zero, step_rewriteDataLo, hw1]
    congr 1 <;> omega
  have h6 : run sourceCompactMachine 1 ⟨rewriteMarkerHi b, Q.length + 1, T1⟩ =
      ⟨rewriteMarkerLo b, Q.length, T2⟩ := by
    rw [run_succ, run_zero, step_rewriteMarkerHi, hw2]
    congr 1 <;> omega
  have h7 : run sourceCompactMachine 1 ⟨rewriteMarkerLo b, Q.length, T2⟩ =
      ⟨goMarkerHi, Q.length + 1, T3⟩ := by
    rw [run_succ, run_zero, step_rewriteMarkerLo, hw3]
  have h8 : run sourceCompactMachine 1 ⟨goMarkerHi, Q.length + 1, T3⟩ =
      ⟨goMarkerLo, Q.length + 2, T3⟩ := by
    rw [run_succ, run_zero, step_goMarkerHi]
  have hs1 : LeftSafeRun sourceCompactMachine ⟨markerLo, Q.length, T0⟩ 1 :=
    leftSafeRun_one_of_not_left (by simp [sourceCompactMachine])
  have hs2 : LeftSafeRun sourceCompactMachine ⟨markerHi, Q.length + 1, T0⟩ 1 :=
    leftSafeRun_one_of_positive (by simp)
  have hs3 : LeftSafeRun sourceCompactMachine ⟨sourceLo, Q.length + 2, T0⟩ 1 :=
    leftSafeRun_one_of_positive (by simp)
  have hs4 : LeftSafeRun sourceCompactMachine ⟨sourceHi b, Q.length + 3, T0⟩ 1 :=
    leftSafeRun_one_of_positive (by simp)
  have hs5 : LeftSafeRun sourceCompactMachine ⟨rewriteDataLo b, Q.length + 2, T0⟩ 1 :=
    leftSafeRun_one_of_positive (by simp)
  have hs6 : LeftSafeRun sourceCompactMachine ⟨rewriteMarkerHi b, Q.length + 1, T1⟩ 1 :=
    leftSafeRun_one_of_positive (by simp)
  have hs7 : LeftSafeRun sourceCompactMachine ⟨rewriteMarkerLo b, Q.length, T2⟩ 1 :=
    leftSafeRun_one_of_not_left (by simp [sourceCompactMachine])
  have hs8 : LeftSafeRun sourceCompactMachine ⟨goMarkerHi, Q.length + 1, T3⟩ 1 :=
    leftSafeRun_one_of_positive (by simp)
  have hs9 : LeftSafeRun sourceCompactMachine ⟨goMarkerLo, Q.length + 2, T3⟩ 1 :=
    leftSafeRun_one_of_positive (by simp)
  rw [hT]
  rw [show pre.length + out.length = Q.length by simp [Q]]
  change LeftSafeRun sourceCompactMachine ⟨markerLo, Q.length, T0⟩ 9
  rw [show 9 = 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))) by omega]
  apply leftSafeRun_add hs1; rw [h1]
  apply leftSafeRun_add hs2; rw [h2]
  apply leftSafeRun_add hs3; rw [h3]
  apply leftSafeRun_add hs4; rw [h4]
  apply leftSafeRun_add hs5; rw [h5]
  apply leftSafeRun_add hs6; rw [h6]
  apply leftSafeRun_add hs7; rw [h7]
  apply leftSafeRun_add hs8; rw [h8]
  exact hs9

theorem sourceCompact_copy_lo_leftSafe (A done : List Bool)
    (carry lo : Bool) (todo tail : List Bool) :
    LeftSafeRun sourceCompactMachine
      ⟨holeLo, A.length + done.length,
        bubbleTape A done carry (lo :: todo) tail⟩ 3 := by
  intro i hi _ hmove
  interval_cases i <;>
    simp [run_succ, step, sourceCompactMachine, moveHead, bubbleTape,
      List.getD_eq_getElem?_getD] at hmove ⊢ <;>
    split_ifs at hmove <;> simp_all

theorem sourceCompact_copy_hi_leftSafe (A done : List Bool)
    (carry lo hi : Bool) (todo tail : List Bool) :
    LeftSafeRun sourceCompactMachine
      ⟨holeHi lo, A.length + done.length,
        bubbleTape A done carry (hi :: todo) tail⟩ 3 := by
  intro i hiN _ hmove
  interval_cases i <;>
    simp [run_succ, step, sourceCompactMachine, moveHead, bubbleTape,
      List.getD_eq_getElem?_getD] at hmove ⊢ <;>
    split_ifs at hmove <;> simp_all

theorem sourceCompact_shift_pairs_leftSafe : ∀ (A written : List Bool)
    (carry : Bool) (ps : List (Bool × Bool)) (ending suffix : List Bool),
    (∀ p ∈ ps, ¬(!p.1 && p.2)) →
    LeftSafeRun sourceCompactMachine
      ⟨holeLo, A.length + written.length,
        bubbleTape A written carry (flattenPairs ps ++ ending) suffix⟩
      (shiftPairsClock ps)
  | A, written, carry, [], ending, suffix, _ => by
      simp [shiftPairsClock, LeftSafeRun]
  | A, written, carry, (lo, hi) :: ps, ending, suffix, hvalid => by
      have hp : ¬(!lo && hi) := hvalid (lo, hi) (by simp)
      have hps : ∀ p ∈ ps, ¬(!p.1 && p.2) := by
        intro p hm
        exact hvalid p (by simp [hm])
      rw [shiftPairsClock, List.length_cons,
        show 6 * (ps.length + 1) = 3 + (3 + shiftPairsClock ps) by
          simp [shiftPairsClock]; omega]
      have hsLo := sourceCompact_copy_lo_leftSafe A written carry lo
        (hi :: flattenPairs ps ++ ending) suffix
      have hLo := sourceCompact_copy_lo A written carry lo
        (hi :: flattenPairs ps ++ ending) suffix
      have hsHi := sourceCompact_copy_hi_leftSafe A (written ++ [lo])
        lo lo hi (flattenPairs ps ++ ending) suffix
      have hHi := sourceCompact_copy_hi_continue A (written ++ [lo])
        lo lo hi (flattenPairs ps ++ ending) suffix hp
      have hsRest := sourceCompact_shift_pairs_leftSafe A
        (written ++ [lo, hi]) hi ps ending suffix hps
      simp only [flattenPairs]
      apply leftSafeRun_add (by simpa [List.append_assoc] using hsLo)
      rw [show run sourceCompactMachine 3
          ⟨holeLo, A.length + written.length,
            bubbleTape A written carry
              (lo :: hi :: flattenPairs ps ++ ending) suffix⟩ =
          ⟨holeHi lo, A.length + written.length + 1,
            bubbleTape A (written ++ [lo]) lo
              (hi :: flattenPairs ps ++ ending) suffix⟩ by
        simpa [List.append_assoc] using hLo]
      apply leftSafeRun_add (by simpa [List.append_assoc] using hsHi)
      rw [show run sourceCompactMachine 3
          ⟨holeHi lo, A.length + written.length + 1,
            bubbleTape A (written ++ [lo]) lo
              (hi :: flattenPairs ps ++ ending) suffix⟩ =
          ⟨holeLo, A.length + written.length + 2,
            bubbleTape A (written ++ [lo, hi]) hi
              (flattenPairs ps ++ ending) suffix⟩ by
        simpa [List.append_assoc] using hHi]
      simpa using hsRest

theorem sourceCompact_finish_leftSafe (pre out garbage tail : List Bool) :
    LeftSafeRun sourceCompactMachine
      ⟨markerLo, pre.length + out.length,
        compactTape pre out [] garbage tail⟩ 4 := by
  let Q := pre ++ out
  let T := compactTape pre out [] garbage tail
  have hlo : T.getD (Q.length + 2) false = false := by
    rw [show T = (Q ++ [true, false]) ++ false :: true :: (garbage ++ tail) by
      simp [T, Q, compactTape, encodeD, List.append_assoc]]
    simp [List.getD_eq_getElem?_getD]
  have h1 : run sourceCompactMachine 1
      ⟨markerLo, Q.length, T⟩ = ⟨markerHi, Q.length + 1, T⟩ := by
    rw [run_succ, run_zero, step_markerLo]
  have h2 : run sourceCompactMachine 1
      ⟨markerHi, Q.length + 1, T⟩ = ⟨sourceLo, Q.length + 2, T⟩ := by
    rw [run_succ, run_zero, step_markerHi]
  have h3 : run sourceCompactMachine 1
      ⟨sourceLo, Q.length + 2, T⟩ = ⟨sourceHi false, Q.length + 3, T⟩ := by
    rw [run_succ, run_zero, step_sourceLo _ _ false hlo]
  have hs1 : LeftSafeRun sourceCompactMachine ⟨markerLo, Q.length, T⟩ 1 :=
    leftSafeRun_one_of_not_left (by simp [sourceCompactMachine])
  have hs2 : LeftSafeRun sourceCompactMachine ⟨markerHi, Q.length + 1, T⟩ 1 :=
    leftSafeRun_one_of_positive (by simp)
  have hs3 : LeftSafeRun sourceCompactMachine ⟨sourceLo, Q.length + 2, T⟩ 1 :=
    leftSafeRun_one_of_positive (by simp)
  have hs4 : LeftSafeRun sourceCompactMachine ⟨sourceHi false, Q.length + 3, T⟩ 1 :=
    leftSafeRun_one_of_positive (by simp)
  rw [show pre.length + out.length = Q.length by simp [Q]]
  change LeftSafeRun sourceCompactMachine ⟨markerLo, Q.length, T⟩ 4
  rw [show 4 = 1 + (1 + (1 + 1)) by omega]
  apply leftSafeRun_add hs1; rw [h1]
  apply leftSafeRun_add hs2; rw [h2]
  apply leftSafeRun_add hs3; rw [h3]
  exact hs4

theorem sourceCompact_round_leftSafe (pre out rest garbage tail : List Bool)
    (b : Bool) :
    LeftSafeRun sourceCompactMachine
      ⟨markerLo, pre.length + out.length,
        compactTape pre out (b :: rest) garbage tail⟩
      (sourceCompactRoundClock rest) := by
  let A := pre ++ out ++ [b, true, false]
  let ps := dataPairs rest ++ [(false, true)]
  have hsRewrite := sourceCompact_rewrite_leftSafe pre out rest garbage tail b
  have hRewrite := sourceCompact_rewrite pre out rest garbage tail b
  have hsShift := sourceCompact_shift_pairs_leftSafe A [] b
    (dataPairs rest) [false, true] (garbage ++ tail)
    (dataPairs_not_01 rest)
  have hShift := sourceCompact_shift_pairs A [] b (dataPairs rest)
    [false, true] (garbage ++ tail) (dataPairs_not_01 rest)
  have hsLo := sourceCompact_copy_lo_leftSafe A
    (flattenPairs (dataPairs rest))
    ((flattenPairs (dataPairs rest)).getD
      (2 * (dataPairs rest).length - 1) b)
    false [true] (garbage ++ tail)
  have hLo := sourceCompact_copy_lo A (flattenPairs (dataPairs rest))
    ((flattenPairs (dataPairs rest)).getD
      (2 * (dataPairs rest).length - 1) b)
    false [true] (garbage ++ tail)
  have hsHi := sourceCompact_copy_hi_leftSafe A
    (flattenPairs (dataPairs rest) ++ [false]) false false true []
    (garbage ++ tail)
  have hHi := sourceCompact_copy_hi_finish A
    (flattenPairs (dataPairs rest) ++ [false]) false []
    (garbage ++ tail)
  have hsRet := sourceCompact_return_pairs_leftSafe pre (out ++ [b]) ps
    [true] (garbage ++ tail) (dataTermPairs_not_10 rest)
  have hflat : flattenPairs (dataPairs rest) ++ [false, true] =
      encodeD rest := by
    simpa [flattenPairs_append, flattenPairs] using flattenPairs_dataPairs rest
  rw [sourceCompactRoundClock,
    show 9 + shiftPairsClock (dataPairs rest) + 6 + returnPairsClock ps =
      9 + (shiftPairsClock (dataPairs rest) +
        (3 + (3 + returnPairsClock ps))) by omega]
  apply leftSafeRun_add hsRewrite
  rw [hRewrite]
  apply leftSafeRun_add (by simpa [A, hflat] using hsShift)
  have hShift' := hShift
  simp only [List.length_nil, Nat.add_zero, List.nil_append] at hShift'
  have hShift'' : run sourceCompactMachine (shiftPairsClock (dataPairs rest))
      ⟨holeLo, (pre ++ out ++ [b, true, false]).length,
        bubbleTape (pre ++ out ++ [b, true, false]) [] b
          (encodeD rest) (garbage ++ tail)⟩ =
      ⟨holeLo, A.length + 2 * (dataPairs rest).length,
        bubbleTape A (flattenPairs (dataPairs rest))
          ((flattenPairs (dataPairs rest)).getD
            (2 * (dataPairs rest).length - 1) b)
          [false, true] (garbage ++ tail)⟩ := by
    simpa [A, hflat] using hShift'
  rw [hShift'']
  apply leftSafeRun_add (by
    simpa [A, flattenPairs_length] using hsLo)
  have hLo' := hLo
  simp only [flattenPairs_length, List.length_append, List.length_singleton]
    at hLo'
  rw [hLo']
  apply leftSafeRun_add (by
    simpa [A, flattenPairs_length, List.append_assoc] using hsHi)
  have hHi' := hHi
  simp only [flattenPairs_length, List.length_append, List.length_singleton]
    at hHi'
  rw [show run sourceCompactMachine 3
      ⟨holeHi false, A.length + 2 * (dataPairs rest).length + 1,
        bubbleTape A (flattenPairs (dataPairs rest) ++ [false]) false [true]
          (garbage ++ tail)⟩ =
      ⟨returnStart, A.length + 2 * (dataPairs rest).length + 2,
        bubbleTape A (flattenPairs (dataPairs rest) ++ [false, true]) true []
          (garbage ++ tail)⟩ by
    simpa [List.append_assoc] using hHi']
  convert hsRet using 1 <;>
    simp [ps, A, hflat, bubbleTape, flattenPairs_append, flattenPairs,
      encodeD_length, dataPairs, List.append_assoc] <;> omega

theorem sourceCompact_rounds_leftSafe (pre garbage tail : List Bool) :
    ∀ (out rest : List Bool),
    LeftSafeRun sourceCompactMachine
      ⟨markerLo, pre.length + out.length,
        compactTape pre out rest garbage tail⟩
      (sourceCompactRoundsClock rest)
  | out, [] => by simp [sourceCompactRoundsClock, LeftSafeRun]
  | out, b :: rest => by
      rw [sourceCompactRoundsClock]
      have hsRound := sourceCompact_round_leftSafe pre out rest garbage tail b
      have hRound := sourceCompact_round pre out rest garbage tail b
      apply leftSafeRun_add hsRound
      rw [hRound]
      exact sourceCompact_rounds_leftSafe pre (true :: garbage) tail
        (out ++ [b]) rest

/-- Complete in-place compaction is left-safe for every protected prefix,
including the empty prefix. -/
theorem sourceCompact_run_leftSafe (pre bits tail : List Bool) :
    LeftSafeRun sourceCompactMachine
      ⟨backHi, pre.length + 2,
        pre ++ [true, false] ++ encodeD bits ++ tail⟩
      (sourceCompactClock bits) := by
  have hsStart := sourceCompact_start_leftSafe pre [] bits [] tail
  have hStart := sourceCompact_start pre [] bits [] tail
  have hsRounds := sourceCompact_rounds_leftSafe pre [] tail [] bits
  have hRounds := sourceCompact_rounds pre [] tail [] bits
  have hsFinish := sourceCompact_finish_leftSafe pre bits
    (List.replicate bits.length true) tail
  rw [sourceCompactClock,
    show 2 + sourceCompactRoundsClock bits + 4 =
      2 + (sourceCompactRoundsClock bits + 4) by omega]
  have hsStart' : LeftSafeRun sourceCompactMachine
      ⟨backHi, pre.length + 2,
        pre ++ [true, false] ++ encodeD bits ++ tail⟩ 2 := by
    simpa [compactTape, List.append_assoc] using hsStart
  apply leftSafeRun_add hsStart'
  have hStart' : run sourceCompactMachine 2
      ⟨backHi, pre.length + 2,
        pre ++ [true, false] ++ encodeD bits ++ tail⟩ =
      ⟨markerLo, pre.length,
        compactTape pre [] bits [] tail⟩ := by
    simpa [compactTape, List.append_assoc] using hStart
  rw [hStart']
  apply leftSafeRun_add hsRounds
  rw [hRounds]
  simpa [compactTape, List.append_assoc] using hsFinish

theorem leftSafeRun_of_halted {M : Machine} {c : Cfg M} (n : Nat)
    (hh : M.halt c.st = true) : LeftSafeRun M c n := by
  intro i _ hlive _
  have hf : run M i c = c := run_of_halted M hh i
  rw [hf] at hlive
  simp [hh] at hlive

theorem headSeqAccept_leftSafe_inl (M1 M2 : Machine) (c : Cfg M1)
    (t : Nat) (hno : ∀ i < t, M1.halt (run M1 i c).st = false)
    (hsafe : LeftSafeRun M1 c t) :
    LeftSafeRun (headSeqAcceptMachine M1 M2)
      (headAcceptInlCfg M1 M2 c) t := by
  intro i hi hhalt hmove
  have hr := headSeqAccept_run_inl M1 M2 c i
    (fun j hj => hno j (by omega))
  rw [hr] at hhalt hmove ⊢
  have hh1 : M1.halt (run M1 i c).st = false := hno i hi
  have hm1 : (M1.δ (run M1 i c).st
      ((run M1 i c).tp.getD (run M1 i c).hd false)).2.2 = 0 := by
    simpa [headSeqAcceptMachine, headAcceptInlCfg, hh1] using hmove
  exact hsafe i hi hh1 hm1

theorem headSeqAccept_leftSafe_handoff (M1 M2 : Machine) (c : Cfg M1)
    (hh : M1.halt c.st = true) :
    LeftSafeRun (headSeqAcceptMachine M1 M2)
      (headAcceptInlCfg M1 M2 c) 1 := by
  apply leftSafeRun_one_of_not_left
  simp [headSeqAcceptMachine, headAcceptInlCfg, hh]

theorem headSeqAccept_leftSafe_inr (M1 M2 : Machine) (c : Cfg M2)
    (t : Nat) (hsafe : LeftSafeRun M2 c t) :
    LeftSafeRun (headSeqAcceptMachine M1 M2)
      (headAcceptInrCfg M1 M2 c) t := by
  intro i hi hhalt hmove
  rw [headSeqAccept_run_inr M1 M2 c i] at hhalt hmove ⊢
  have hh2 : M2.halt (run M2 i c).st = false := by
    simpa [headSeqAcceptMachine, headAcceptInrCfg] using hhalt
  have hm2 : (M2.δ (run M2 i c).st
      ((run M2 i c).tp.getD (run M2 i c).hd false)).2.2 = 0 := by
    simpa [headSeqAcceptMachine, headAcceptInrCfg] using hmove
  exact hsafe i hi hh2 hm2

/-- Complete safety composition with the same least-halt slack absorption as
`headSeqAccept_run`. -/
theorem headSeqAccept_leftSafe (M1 M2 : Machine) (T0 T1 : List Bool)
    (t1 t2 p1 : Nat) (s1 : M1.State)
    (h1 : run M1 t1 (init M1 T0) = ⟨s1, p1, T1⟩)
    (hh1 : M1.halt s1 = true)
    (hsafe1 : LeftSafeRun M1 (init M1 T0) t1)
    (hsafe2 : LeftSafeRun M2 ⟨M2.start, p1, T1⟩ t2)
    (hh2 : M2.halt (run M2 t2 ⟨M2.start, p1, T1⟩).st = true) :
    LeftSafeRun (headSeqAcceptMachine M1 M2)
      (init (headSeqAcceptMachine M1 M2) T0) (t1 + 1 + t2) := by
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
  have hs1 : LeftSafeRun (headSeqAcceptMachine M1 M2)
      (init (headSeqAcceptMachine M1 M2) T0) tm := by
    change LeftSafeRun (headSeqAcceptMachine M1 M2)
      (headAcceptInlCfg M1 M2 (init M1 T0)) tm
    exact headSeqAccept_leftSafe_inl M1 M2 (init M1 T0) tm hno
      (fun i hi => hsafe1 i (by omega))
  have hrun1 : run (headSeqAcceptMachine M1 M2) tm
      (init (headSeqAcceptMachine M1 M2) T0) =
      headAcceptInlCfg M1 M2 (⟨s1, p1, T1⟩ : Cfg M1) := by
    change run (headSeqAcceptMachine M1 M2) tm
      (headAcceptInlCfg M1 M2 (init M1 T0)) = _
    rw [headSeqAccept_run_inl M1 M2 _ tm hno, hfrozen]
  have hsSwitch : LeftSafeRun (headSeqAcceptMachine M1 M2)
      (run (headSeqAcceptMachine M1 M2) tm
        (init (headSeqAcceptMachine M1 M2) T0)) 1 := by
    rw [hrun1]
    exact headSeqAccept_leftSafe_handoff M1 M2 _ hh1
  have hafter : run (headSeqAcceptMachine M1 M2) 1
      (run (headSeqAcceptMachine M1 M2) tm
        (init (headSeqAcceptMachine M1 M2) T0)) =
      headAcceptInrCfg M1 M2 ⟨M2.start, p1, T1⟩ := by
    rw [hrun1, run_succ, run_zero]
    exact headSeqAccept_step_handoff M1 M2 _ hh1
  have hs2 : LeftSafeRun (headSeqAcceptMachine M1 M2)
      (run (headSeqAcceptMachine M1 M2) (tm + 1)
        (init (headSeqAcceptMachine M1 M2) T0)) t2 := by
    rw [run_add, hafter]
    exact headSeqAccept_leftSafe_inr M1 M2 _ t2 hsafe2
  have hsMain : LeftSafeRun (headSeqAcceptMachine M1 M2)
      (init (headSeqAcceptMachine M1 M2) T0) (tm + 1 + t2) :=
    leftSafeRun_add (leftSafeRun_add hs1 hsSwitch) hs2
  have hhaltAt : (headSeqAcceptMachine M1 M2).halt
      (run (headSeqAcceptMachine M1 M2) (tm + 1 + t2)
        (init (headSeqAcceptMachine M1 M2) T0)).st =
      M2.halt (run M2 t2 ⟨M2.start, p1, T1⟩).st := by
    rw [show tm + 1 + t2 = (tm + 1) + t2 by omega, run_add]
    rw [run_add, hafter, headSeqAccept_run_inr]
    rfl
  have hsSlack : LeftSafeRun (headSeqAcceptMachine M1 M2)
      (run (headSeqAcceptMachine M1 M2) (tm + 1 + t2)
        (init (headSeqAcceptMachine M1 M2) T0)) (t1 - tm) :=
    leftSafeRun_of_halted _ (by rw [hhaltAt, hh2])
  have hsAll := leftSafeRun_add hsMain hsSlack
  convert hsAll using 1 <;> omega

/-- `headSeqMachine` and `headSeqAcceptMachine` have exactly the same
transition graph; only their observational `accept` field differs. -/
def headCfgToAccept (M1 M2 : Machine) (c : Cfg (headSeqMachine M1 M2)) :
    Cfg (headSeqAcceptMachine M1 M2) :=
  ⟨c.st, c.hd, c.tp⟩

theorem headSeq_run_map_accept (M1 M2 : Machine)
    (c : Cfg (headSeqMachine M1 M2))
    (t : Nat) :
    run (headSeqAcceptMachine M1 M2) t (headCfgToAccept M1 M2 c) =
      headCfgToAccept M1 M2 (run (headSeqMachine M1 M2) t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, run_succ, ih]
      cases cs : run (headSeqMachine M1 M2) t c with
      | mk st hd tp =>
        cases st with
        | inl s =>
            simp [step, headSeqMachine, headSeqAcceptMachine, headCfgToAccept]
        | inr s =>
            by_cases hh : M2.halt s = true <;>
              simp [step, headSeqMachine, headSeqAcceptMachine,
                headCfgToAccept, hh]

/-- The ordinary head-preserving compositor inherits the same complete
left-safety composition theorem. -/
theorem headSeq_leftSafe (M1 M2 : Machine) (T0 T1 : List Bool)
    (t1 t2 p1 : Nat) (s1 : M1.State)
    (h1 : run M1 t1 (init M1 T0) = ⟨s1, p1, T1⟩)
    (hh1 : M1.halt s1 = true)
    (hsafe1 : LeftSafeRun M1 (init M1 T0) t1)
    (hsafe2 : LeftSafeRun M2 ⟨M2.start, p1, T1⟩ t2)
    (hh2 : M2.halt (run M2 t2 ⟨M2.start, p1, T1⟩).st = true) :
    LeftSafeRun (headSeqMachine M1 M2)
      (init (headSeqMachine M1 M2) T0) (t1 + 1 + t2) := by
  have hs := headSeqAccept_leftSafe M1 M2 T0 T1 t1 t2 p1 s1
    h1 hh1 hsafe1 hsafe2 hh2
  intro i hi hhalt hmove
  have hrun := headSeq_run_map_accept M1 M2
    (init (headSeqMachine M1 M2) T0) i
  have hhalt' : (headSeqAcceptMachine M1 M2).halt
      (run (headSeqAcceptMachine M1 M2) i
        (init (headSeqAcceptMachine M1 M2) T0)).st = false := by
    rw [show init (headSeqAcceptMachine M1 M2) T0 =
      headCfgToAccept M1 M2 (init (headSeqMachine M1 M2) T0) from rfl,
      hrun]
    simpa [headSeqMachine, headSeqAcceptMachine, headCfgToAccept] using hhalt
  have hmove' : ((headSeqAcceptMachine M1 M2).δ
      (run (headSeqAcceptMachine M1 M2) i
        (init (headSeqAcceptMachine M1 M2) T0)).st
      ((run (headSeqAcceptMachine M1 M2) i
        (init (headSeqAcceptMachine M1 M2) T0)).tp.getD
        (run (headSeqAcceptMachine M1 M2) i
          (init (headSeqAcceptMachine M1 M2) T0)).hd false)).2.2 = 0 := by
    rw [show init (headSeqAcceptMachine M1 M2) T0 =
      headCfgToAccept M1 M2 (init (headSeqMachine M1 M2) T0) from rfl,
      hrun]
    simpa [headSeqMachine, headSeqAcceptMachine, headCfgToAccept] using hmove
  have hp := hs i hi hhalt' hmove'
  rw [show init (headSeqAcceptMachine M1 M2) T0 =
    headCfgToAccept M1 M2 (init (headSeqMachine M1 M2) T0) from rfl,
    hrun] at hp
  simpa [headCfgToAccept] using hp

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeLeftSafety

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeLeftSafety.headSeqAccept_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeLeftSafety.headSeq_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeLeftSafety.sourceSelect_leftSafe_any
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeLeftSafety.sourceRewind_run_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeLeftSafety.sourceCompact_run_leftSafe
