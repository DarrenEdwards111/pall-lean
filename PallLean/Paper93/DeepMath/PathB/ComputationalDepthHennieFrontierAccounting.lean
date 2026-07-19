import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHennieLocalWrite
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTraceDistinctRowsObstruction

/-!
# Frontier-growth accounting

This file separates the combinatorial accounting from the local blank-excursion theorem.  Given a
uniform bound `K` saying that every write occurs with `head + 1 ≤ tapeLength + K`, it proves:

* each tape-length increase is by at most `K`;
* the final tape length is at most the input length plus `K` times the number of strict increases;
* strict increases inject into distinct tape snapshots;
* hence final tape length is at most `inputLength + K * distinctRows(traceObj)`.

The remaining integration task is to derive the write-head hypothesis from the local write-free
phase theorem in `HennieLocalWrite` by splitting a halting run at its write attempts.
-/

namespace PallLean.Paper93.DeepMath.PathB.HennieFrontierAccounting

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema
open PallLean.Paper93.DeepMath.PathB.TraceDistinctRows
open PallLean.Paper93.DeepMath.PathB.TraceDistinctRowsObstruction
open PallLean.Paper93.DeepMath.PathB.SuperAdditiveKills (distinctRows)

attribute [local instance] Classical.propDecidable

variable {M : Machine}

/-- The tape length at time `t`. -/
def tapeLen (M : Machine) (c : Cfg M) (t : ℕ) : ℕ := (run M t c).tp.length

/-- Times before `T` at which the tape length strictly increases. -/
def growthTimes (M : Machine) (c : Cfg M) (T : ℕ) : Finset ℕ :=
  (Finset.range T).filter fun t => tapeLen M c t < tapeLen M c (t + 1)

/-- Operational hypothesis supplied by local excursion analysis: every active write is made within
`K` cells of the current tape frontier. -/
def WriteHeadBound (M : Machine) (c : Cfg M) (T K : ℕ) : Prop :=
  ∀ t, t < T → M.halt (run M t c).st = false →
    (M.δ (run M t c).st
      ((run M t c).tp.getD (run M t c).hd false)).2.1 ≠ none →
    (run M t c).hd + 1 ≤ (run M t c).tp.length + K

/-- Under the write-head bound, one step grows the tape by at most `K`. -/
theorem tapeLen_succ_le {c : Cfg M} {T K t : ℕ}
    (hK : WriteHeadBound M c T K) (ht : t < T) :
    tapeLen M c (t + 1) ≤ tapeLen M c t + K := by
  rw [tapeLen, tapeLen, run_succ]
  set d := run M t c
  by_cases hh : M.halt d.st = true
  · rw [step_of_halted M hh]
    omega
  · simp only [Bool.not_eq_true] at hh
    rcases hw : (M.δ d.st (d.tp.getD d.hd false)).2.1 with _ | w
    · unfold step
      rw [hh]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hw]
      simp
    · have hn : (M.δ (run M t c).st
          ((run M t c).tp.getD (run M t c).hd false)).2.1 ≠ none := by
          have hn' : (M.δ d.st (d.tp.getD d.hd false)).2.1 ≠ none := by
            rw [hw]
            simp
          simpa [d] using hn'
      have hhead : d.hd + 1 ≤ d.tp.length + K := by
        simpa [d] using hK t ht hh hn
      unfold step
      rw [hh]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hw, TraceMeasureSchema.writeAt_length]
      omega

/-- Final length is bounded by initial length plus `K` for each strict growth time. -/
theorem tapeLen_le_growthTimes {c : Cfg M} {T K : ℕ}
    (hK : WriteHeadBound M c T K) :
    tapeLen M c T ≤ tapeLen M c 0 + K * (growthTimes M c T).card := by
  induction T with
  | zero => simp [growthTimes]
  | succ T ih =>
      have hK' : WriteHeadBound M c T K := fun t ht => hK t (by omega)
      have ih' := ih hK'
      by_cases hg : tapeLen M c T < tapeLen M c (T + 1)
      · have hstep := tapeLen_succ_le hK (Nat.lt_succ_self T)
        have hset : growthTimes M c (T + 1) = insert T (growthTimes M c T) := by
          ext i
          simp only [growthTimes, Finset.mem_filter, Finset.mem_range,
            Finset.mem_insert]
          constructor
          · rintro ⟨hi, hgi⟩
            rcases lt_or_eq_of_le (by omega : i ≤ T) with hlt | rfl
            · exact Or.inr ⟨hlt, hgi⟩
            · exact Or.inl rfl
          · rintro (rfl | ⟨hi, hgi⟩)
            · exact ⟨by omega, hg⟩
            · exact ⟨by omega, hgi⟩
        have hcard : (growthTimes M c (T + 1)).card = (growthTimes M c T).card + 1 := by
          rw [hset, Finset.card_insert_of_notMem]
          simp [growthTimes]
        rw [hcard]
        nlinarith
      · have hmono := run_tp_length_mono M c (Nat.le_succ T)
        have heq : tapeLen M c (T + 1) = tapeLen M c T := by
          simp only [tapeLen, Nat.succ_eq_add_one] at hg hmono ⊢
          omega
        have hset : growthTimes M c (T + 1) = growthTimes M c T := by
          ext i
          simp only [growthTimes, Finset.mem_filter, Finset.mem_range]
          constructor
          · rintro ⟨hi, hgi⟩
            have hne : i ≠ T := by rintro rfl; exact hg hgi
            exact ⟨by omega, hgi⟩
          · rintro ⟨hi, hgi⟩
            exact ⟨by omega, hgi⟩
        have hcard : (growthTimes M c (T + 1)).card = (growthTimes M c T).card :=
          congrArg Finset.card hset
        rw [heq, hcard]
        exact ih'

/-- Distinct growth times yield distinct post-growth tape snapshots. -/
theorem postGrowth_injOn (c : Cfg M) (T : ℕ) :
    Set.InjOn (fun t => (run M (t + 1) c).tp) ↑(growthTimes M c T) := by
  intro i hi j hj heq
  simp only [Finset.mem_coe] at hi hj
  rw [growthTimes, Finset.mem_filter] at hi hj
  simp only [Finset.mem_range] at hi hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hmono := run_tp_length_mono M c (show i + 1 ≤ j by omega)
    have hlt : (run M (i + 1) c).tp.length < (run M (j + 1) c).tp.length := by
      exact hmono.trans_lt hj.2
    have hlenEq := congrArg List.length heq
    exact (ne_of_lt hlt) hlenEq
  · have hmono := run_tp_length_mono M c (show j + 1 ≤ i by omega)
    have hlt : (run M (j + 1) c).tp.length < (run M (i + 1) c).tp.length := by
      exact hmono.trans_lt hi.2
    have hlenEq := congrArg List.length heq
    exact (ne_of_lt hlt) hlenEq.symm

/-- The number of strict frontier increases is at most the number of distinct tape snapshots. -/
theorem growthTimes_card_le_distinctRows (M : Machine) (x : List Bool) (T : ℕ) :
    (growthTimes M (init M x) T).card ≤ distinctRows (traceObj M T x) := by
  calc
    (growthTimes M (init M x) T).card
        ≤ ((visitedConfigs (init M x) T).image (fun d => d.tp)).card := by
          apply Finset.card_le_card_of_injOn (fun t => (run M (t + 1) (init M x)).tp)
          · intro t ht
            simp only [Finset.mem_coe] at ht
            rw [growthTimes, Finset.mem_filter] at ht
            have htT : t < T := Finset.mem_range.mp ht.1
            simp only [Finset.mem_coe]
            apply Finset.mem_image.mpr
            refine ⟨run M (t + 1) (init M x), ?_, rfl⟩
            unfold visitedConfigs
            apply Finset.mem_image.mpr
            exact ⟨t + 1, Finset.mem_range.mpr (by omega), rfl⟩
          · exact postGrowth_injOn (init M x) T
    _ = distinctRows (traceObj M T x) := visitedTapes_card_eq_distinctRows M x T

/-- **Frontier accounting theorem.**  A write-head bound immediately yields the desired final-tape
bound in terms of input length and the exact trace-level distinct-row count. -/
theorem finalTape_le_of_writeHeadBound (M : Machine) (x : List Bool) {T K : ℕ}
    (hK : WriteHeadBound M (init M x) T K) :
    (run M T (init M x)).tp.length ≤
      x.length + K * distinctRows (traceObj M T x) := by
  have hsum := tapeLen_le_growthTimes hK
  have hcard := growthTimes_card_le_distinctRows M x T
  simp only [tapeLen, run_zero, init] at hsum
  exact hsum.trans (Nat.add_le_add_left (Nat.mul_le_mul_left K hcard) x.length)

end PallLean.Paper93.DeepMath.PathB.HennieFrontierAccounting
