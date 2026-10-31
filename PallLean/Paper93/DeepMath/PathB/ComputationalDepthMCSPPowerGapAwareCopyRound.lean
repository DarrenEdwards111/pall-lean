import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPPowerGapAwareCopyGrow

/-!
# MCSP verifier: one complete gap-aware bridge-copy round

The post-growth reset first scans the copied table and both power counters,
crosses the unique internal `00` gap while consuming its one-shot flag, then
scans the table source and its marker to the genuine local home.  This file
composes that reset with find, mark, gap-aware seek, and grow into one exact
round of the physical controller.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyRound

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyLift
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRound
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyMachine
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopySeek
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyGrow
open LocalHomeState
open GapCopyState

theorem gapped_getD_Amark_lo (n a jA jC i : ℕ)
    (suffix : List Bool) (hA : jA ≤ a) (hi : i < jA) :
    (gappedBridgeCpyS n a jA jC suffix).getD (2 * i) false = true := by
  rw [gappedBridgeCpyS, List.getD_append (h := by
    rw [cpyT_length a jA 0 hA]
    omega)]
  exact cpyT_getD_Amark_lo a jA 0 i hi

theorem gapped_getD_Amark_hi (n a jA jC i : ℕ)
    (suffix : List Bool) (hA : jA ≤ a) (hi : i < jA) :
    (gappedBridgeCpyS n a jA jC suffix).getD (2 * i + 1) false = false := by
  rw [gappedBridgeCpyS, List.getD_append (h := by
    rw [cpyT_length a jA 0 hA]
    omega)]
  exact cpyT_getD_Amark_hi a jA 0 i hi

/-- A nonblank doubled pair is crossed in two leftward steps without changing
either the remembered copy state or the gap flag. -/
theorem run_two_gapHomePair (resume : copyMachine.State) (skip : Bool)
    {p : ℕ} {T : List Bool} (_hp : 0 < p)
    (hpair : T.getD p false = true ∨ T.getD (p + 1) false = true) :
    run gapCopyMachine 2
      ⟨.home resume skip scanHi, p + 1, T⟩ =
      ⟨.home resume skip scanHi, p - 1, T⟩ := by
  rcases hpair with hlo | hhi
  · by_cases h : T.getD (p + 1) false = true
    · rw [List.getD_eq_getElem?_getD] at h
      rw [run_succ, run_succ, run_zero]
      simp [step, gapCopyMachine, localHomeMachine, moveHead, h]
    · have hf : T.getD (p + 1) false = false := by simpa using h
      rw [List.getD_eq_getElem?_getD] at hf hlo
      rw [run_succ, run_succ, run_zero]
      simp [step, gapCopyMachine, localHomeMachine, moveHead, hf, hlo]
  · rw [List.getD_eq_getElem?_getD] at hhi
    rw [run_succ, run_succ, run_zero]
    simp [step, gapCopyMachine, localHomeMachine, moveHead, hhi]

/-- Scan `k` consecutive nonblank pairs right-to-left. -/
theorem run_gapHomePairs (resume : copyMachine.State) (skip : Bool)
    (T : List Bool) (q k : ℕ)
    (hpairs : ∀ i, i < k →
      T.getD (q + 2 + 2 * i) false = true ∨
        T.getD (q + 2 + 2 * i + 1) false = true) :
    run gapCopyMachine (2 * k)
      ⟨.home resume skip scanHi, q + 1 + 2 * k, T⟩ =
      ⟨.home resume skip scanHi, q + 1, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show q + 1 + 2 * (k + 1) = (q + 2 + 2 * k) + 1 by omega,
        show 2 * (k + 1) = 2 + 2 * k by omega, run_add,
        run_two_gapHomePair resume skip (p := q + 2 + 2 * k)
          (by omega) (hpairs k (by omega)),
        show q + 2 + 2 * k - 1 = q + 1 + 2 * k by omega]
      exact ih (fun i hi => hpairs i (by omega))

theorem gapped_left_active_pair (n a j i : ℕ) (suffix : List Bool)
    (hj : j ≤ a) (hi : i < a + 1) :
    (gappedBridgeCpyS n a j j suffix).getD (2 * i) false = true ∨
      (gappedBridgeCpyS n a j j suffix).getD (2 * i + 1) false = true := by
  by_cases hs : i < a
  · by_cases hm : i < j
    · exact Or.inl (gapped_getD_Amark_lo n a j j i suffix hj hm)
    · exact Or.inl (gapped_getD_Adata n a j j (2 * i) suffix hj
        (by omega) (by omega))
  · have hi' : i = a := by omega
    subst i
    exact Or.inr (gapped_getD_marker_hi n a j j suffix hj)

theorem gapped_right_active_pair (n a j i : ℕ) (suffix : List Bool)
    (hj : j ≤ a) (hi : i < bridgePairs n + j) :
    (gappedBridgeCpyS n a j j suffix).getD
        (2 * a + 4 + 2 * i) false = true ∨
      (gappedBridgeCpyS n a j j suffix).getD
        (2 * a + 4 + 2 * i + 1) false = true := by
  by_cases hb : i < bridgePairs n
  · right
    exact gapped_getD_bridge_high n a j j i suffix hj hb
  · right
    rw [show 2 * a + 4 + 2 * i + 1 =
      2 * a + 4 + 2 * bridgePairs n + 2 * (i - bridgePairs n) + 1 by omega]
    have h := gapped_getD_C_high n a j j (i - bridgePairs n)
      suffix hj (by omega)
    simpa using h

/-- Complete post-growth reset.  The internal gap is crossed exactly once;
the next `00` is recognized as the true table home and copying resumes in
state `0` with both one-round flags cleared. -/
theorem run_gapped_growHome_resume (pre suffix : List Bool)
    (n a j : ℕ) (hj : j < a) :
    let q := localOffset pre
    let p := 2 * a + 4 + 2 * bridgePairs n + 2 * j
    run gapCopyMachine (2 * (a + bridgePairs n + j) + 10)
      ⟨.home (0, false) true scanHi, q + p + 1,
        localTape pre
          (gappedBridgeCpyS n a (j + 1) (j + 1) suffix)⟩ =
      ⟨.copy (0, false) false, q,
        localTape pre
          (gappedBridgeCpyS n a (j + 1) (j + 1) suffix)⟩ := by
  intro q p
  let T := localTape pre
    (gappedBridgeCpyS n a (j + 1) (j + 1) suffix)
  let gap := q + 2 * a + 2
  let kr := bridgePairs n + (j + 1)
  have hright : run gapCopyMachine (2 * kr)
      ⟨.home (0, false) true scanHi, q + p + 1, T⟩ =
      ⟨.home (0, false) true scanHi, gap + 1, T⟩ := by
    have h := run_gapHomePairs (0, false) true T gap kr (fun i hi => by
      have hp := gapped_right_active_pair n a (j + 1) i suffix
        (by omega) (by simpa [kr] using hi)
      rcases hp with hlo | hhi
      · left
        rw [show gap + 2 + 2 * i =
          localOffset pre + (2 * a + 4 + 2 * i) by simp [gap]; omega,
          localTape_getD]
        exact hlo
      · right
        rw [show gap + 2 + 2 * i + 1 =
          localOffset pre + (2 * a + 4 + 2 * i + 1) by simp [gap]; omega,
          localTape_getD]
        exact hhi)
    have hhead : q + p + 1 = gap + 1 + 2 * kr := by
      simp [p, gap, kr]
      ring
    rw [hhead]
    exact h
  have hgap : run gapCopyMachine 2
      ⟨.home (0, false) true scanHi, gap + 1, T⟩ =
      ⟨.home (0, false) false scanHi, gap - 1, T⟩ := by
    apply run_gapHome_two
    · simp [gap, q, localOffset]
    · rw [show gap = localOffset pre + (2 * a + 2) by rfl,
        localTape_getD]
      exact gapped_getD_gap_lo n a (j + 1) (j + 1) suffix (by omega)
    · rw [show gap + 1 = localOffset pre + (2 * a + 3) by omega,
        localTape_getD]
      exact gapped_getD_gap_hi n a (j + 1) (j + 1) suffix (by omega)
  have hleft : run gapCopyMachine (2 * (a + 1))
      ⟨.home (0, false) false scanHi, gap - 1, T⟩ =
      ⟨.home (0, false) false scanHi, pre.length + 1, T⟩ := by
    have h := run_gapHomePairs (0, false) false T pre.length (a + 1)
      (fun i hi => by
        have hp := gapped_left_active_pair n a (j + 1) i suffix
          (by omega) hi
        rcases hp with hlo | hhi
        · left
          rw [show pre.length + 2 + 2 * i =
            localOffset pre + 2 * i by simp [localOffset], localTape_getD]
          exact hlo
        · right
          rw [show pre.length + 2 + 2 * i + 1 =
            localOffset pre + (2 * i + 1) by simp [localOffset]; omega,
            localTape_getD]
          exact hhi)
    have hhead : gap - 1 = pre.length + 1 + 2 * (a + 1) := by
      simp [gap, q, localOffset]
      omega
    rw [hhead]
    exact h
  have hhome : run gapCopyMachine 4
      ⟨.home (0, false) false scanHi, pre.length + 1, T⟩ =
      ⟨.copy (0, false) false, q, T⟩ := by
    have h := run_trueHome_four
      (resume := (0, false))
      (q := pre.length) (T := T)
      (by simp [T, localTape, homePrefix])
      (by simp [T, localTape, homePrefix])
    simpa [q, localOffset] using h
  rw [show 2 * (a + bridgePairs n + j) + 10 =
      2 * kr + (2 + (2 * (a + 1) + 4)) by simp [kr]; omega,
    run_add, hright, run_add, hgap, run_add, hleft, hhome]

def gappedRoundClock (n a j : ℕ) : ℕ :=
  2 * j + 2 + (2 * (a + bridgePairs n) + 2) +
    (4 + (2 * (a + bridgePairs n + j) + 10))

theorem gappedRoundClock_eq (n a j : ℕ) :
    gappedRoundClock n a j =
      4 * a + 4 * j + 4 * bridgePairs n + 18 := by
  unfold gappedRoundClock
  ring

theorem run_two_gapFind {crossed s : Bool} {p : ℕ} {T : List Bool}
    (hlo : T.getD p false = true)
    (hhi : T.getD (p + 1) false = false) :
    run gapCopyMachine 2 ⟨.copy (0, s) crossed, p, T⟩ =
      ⟨.copy (0, true) crossed, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo hhi
  rw [run_succ, run_succ, run_zero]
  simp [step, gapCopyMachine, copyMachine, moveHead, hlo, hhi]

theorem run_gapFind (T : List Bool) (q k : ℕ) (s crossed : Bool)
    (h : ∀ i, i < k →
      T.getD (q + 2 * i) false = true ∧
        T.getD (q + 2 * i + 1) false = false) :
    run gapCopyMachine (2 * k) ⟨.copy (0, s) crossed, q, T⟩ =
      ⟨.copy (0, if k = 0 then s else true) crossed,
        q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, run_add,
        ih (fun i hi => h i (by omega))]
      simpa [Nat.succ_ne_zero, Nat.mul_succ, Nat.add_assoc] using
        run_two_gapFind
          (s := if k = 0 then s else true) (crossed := crossed)
          (p := q + 2 * k) (h k (by omega)).1 (h k (by omega)).2

theorem run_gapped_find (pre suffix : List Bool)
    (n a j : ℕ) (hj : j ≤ a) (s : Bool) :
    let q := localOffset pre
    run gapCopyMachine (2 * j)
      ⟨.copy (0, s) false, q,
        localTape pre (gappedBridgeCpyS n a j j suffix)⟩ =
      ⟨.copy (0, if j = 0 then s else true) false, q + 2 * j,
        localTape pre (gappedBridgeCpyS n a j j suffix)⟩ := by
  intro q
  apply run_gapFind
  intro i hi
  constructor
  · rw [show q + 2 * i = localOffset pre + 2 * i by rfl,
          localTape_getD]
    exact gapped_getD_Amark_lo n a j j i suffix hj hi
  · rw [show q + 2 * i + 1 = localOffset pre + (2 * i + 1) by omega,
          localTape_getD]
    exact gapped_getD_Amark_hi n a j j i suffix hj hi

/-- One complete physical gapped bridge-copy round. -/
theorem run_gapped_round (pre suffix : List Bool)
    (n a j : ℕ) (hj : j < a) (s : Bool) :
    let q := localOffset pre
    run gapCopyMachine (gappedRoundClock n a j)
      ⟨.copy (0, s) false, q,
        localTape pre (gappedBridgeCpyS n a j j suffix)⟩ =
      ⟨.copy (0, false) false, q,
        localTape pre
          (gappedBridgeCpyS n a (j + 1) (j + 1) suffix)⟩ := by
  intro q
  rw [gappedRoundClock,
    show 2 * j + 2 + (2 * (a + bridgePairs n) + 2) +
        (4 + (2 * (a + bridgePairs n + j) + 10)) =
      2 * j + (2 + ((2 * (a + bridgePairs n) + 2) +
        (4 + (2 * (a + bridgePairs n + j) + 10)))) by omega,
    run_add, run_gapped_find pre suffix n a j (by omega) s,
    run_add,
    run_gapped_mark pre suffix n a j hj (if j = 0 then s else true),
    run_add, run_gapped_bridge_seek pre suffix n a j hj,
    show localOffset pre + 2 * a + 4 + 2 * bridgePairs n + 2 * j =
      localOffset pre + (2 * a + 4 + 2 * bridgePairs n + 2 * j) by omega,
    run_add, run_gapped_grow_enterHome pre suffix n a j hj,
    run_gapped_growHome_resume pre suffix n a j hj]

end PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyRound

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyRound.run_gapped_growHome_resume
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyRound.run_gapped_round
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyRound.gappedRoundClock_eq
