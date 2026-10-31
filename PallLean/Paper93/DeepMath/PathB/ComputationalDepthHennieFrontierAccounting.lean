import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHennieLocalWrite
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTraceDistinctRowsObstruction

/-!
# Frontier-growth accounting

This file separates the combinatorial accounting from the local blank-excursion theorem.  Given a
uniform bound `K` saying that every write occurs with `head + 1 ≤ tapeLength + K`, it proves:

* each tape-length increase is by at most `K`;
* the final tape length is at most the input length plus `K` times the number of strict increases;
* strict increases inject into distinct tape snapshots;
* hence final tape length is at most `inputLength + K * distinctRows(traceObj)`;
* splitting at the last earlier write supplies that write-head bound for every first-halting run;
* the resulting explicit clock is polynomial whenever the distinct-row bound is polynomial.

Thus this file closes the no-computation-in-empty-space obligation and proves
`NoEmptySpaceComputation` without an additional mathematical hypothesis.
-/

namespace PallLean.Paper93.DeepMath.PathB.HennieFrontierAccounting

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema
open PallLean.Paper93.DeepMath.PathB.TraceDistinctRows
open PallLean.Paper93.DeepMath.PathB.TraceDistinctRowsObstruction
open PallLean.Paper93.DeepMath.PathB.SuperAdditiveKills (distinctRows)
open PallLean.Paper93.DeepMath.PathB.HennieLocalWrite

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

/-! ## Discharging the write-head bound by splitting at the last write -/

/-- Whether the active transition table specifies a write at time `t`.  Halting is handled
separately by the first-halt hypothesis. -/
def WritesAt (M : Machine) (c : Cfg M) (t : ℕ) : Prop :=
  (M.δ (run M t c).st
    ((run M t c).tp.getD (run M t c).hd false)).2.1 ≠ none

/-- Earlier write-attempt times. -/
noncomputable def writesBefore (M : Machine) (c : Cfg M) (t : ℕ) : Finset ℕ :=
  (Finset.range t).filter fun j => WritesAt M c j

/-- Immediately after an active write, the head is still inside or one-past the new list tape,
hence strictly below `newLength + 1`. -/
theorem head_lt_tape_succ_after_write (d : Cfg M)
    (hhalt : M.halt d.st = false) {w : Bool}
    (hwrite : (M.δ d.st (d.tp.getD d.hd false)).2.1 = some w) :
    (step M d).hd < (step M d).tp.length + 1 := by
  have hhd := TraceMeasureSchema.step_hd_le M d
  have htp : d.hd + 1 ≤ (step M d).tp.length := by
    unfold step
    rw [hhalt]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hwrite, TraceMeasureSchema.writeAt_length]
    exact le_max_right _ _
  omega

/-- **Every first-halting run satisfies the uniform write-head bound.**  At a write time `t`, split
after the last earlier write (or at the initial configuration if none exists).  The intervening
phase is write-free and begins with the head inside its tape, so `head_lt_at_next_write` applies.
The extra `+1` converts its strict inequality to the non-strict `WriteHeadBound` convention. -/
theorem writeHeadBound_of_firstHalting (M : Machine) (c : Cfg M) {T : ℕ}
    (hstart0 : c.hd < c.tp.length + 1)
    (hfirst : ∀ j, j < T → M.halt (run M j c).st = false) :
    WriteHeadBound M c T (Fintype.card (stopBeforeWrite M).State + 1) := by
  intro t htT hhalt hwriteNe
  rcases hopt : (M.δ (run M t c).st
      ((run M t c).tp.getD (run M t c).hd false)).2.1 with _ | w
  · exact False.elim (hwriteNe hopt)
  · let S := writesBefore M c t
    by_cases hSne : S.Nonempty
    · let a := S.max' hSne
      have hamem : a ∈ S := S.max'_mem hSne
      have halt : a < t := by
        have := (Finset.mem_filter.mp hamem).1
        exact Finset.mem_range.mp this
      let s := a + 1
      let d := run M s c
      let u := t - s
      have hst : s ≤ t := by simp [s]; omega
      have hsu : s + u = t := by simp [u]; omega
      have hrun (j : ℕ) : run M j d = run M (s + j) c := by
        simp only [d]
        rw [← run_add]
      have hfree : WriteFreeBefore M d u := by
        intro j hju
        have hglobal : s + j < t := by omega
        have hnonhalt : M.halt (run M j d).st = false := by
          rw [hrun]
          exact hfirst (s + j) (by omega)
        refine ⟨hnonhalt, ?_⟩
        by_contra hn
        have hwglobal : WritesAt M c (s + j) := by
          simpa [WritesAt, hrun] using hn
        have hmem : s + j ∈ S := by
          change s + j ∈ writesBefore M c t
          rw [writesBefore, Finset.mem_filter]
          exact ⟨Finset.mem_range.mpr hglobal, hwglobal⟩
        have hlemax := S.le_max' (s + j) hmem
        simp only [s, a] at hlemax
        omega
      have hstart : d.hd < d.tp.length + 1 := by
        have hawrite : WritesAt M c a := (Finset.mem_filter.mp hamem).2
        rcases haw : (M.δ (run M a c).st
            ((run M a c).tp.getD (run M a c).hd false)).2.1 with _ | wa
        · exact False.elim (hawrite haw)
        · have hstep := head_lt_tape_succ_after_write (run M a c)
            (hfirst a (by omega)) haw
          simp only [d, s]
          rwa [← run_succ] at hstep
      have huHalt : M.halt (run M u d).st = false := by
        rw [hrun, hsu]
        exact hhalt
      have huWrite : (M.δ (run M u d).st
          ((run M u d).tp.getD (run M u d).hd false)).2.1 = some w := by
        rw [hrun, hsu]
        exact hopt
      have hlocal := head_lt_at_next_write d hfree hstart huHalt huWrite
      have hlen : d.tp.length ≤ (run M u d).tp.length :=
        run_tp_length_mono M d (Nat.zero_le u)
      rw [hrun, hsu] at hlocal hlen
      omega
    · have hfree : WriteFreeBefore M c t := by
        intro j hj
        refine ⟨hfirst j (by omega), ?_⟩
        by_contra hn
        have hmem : j ∈ S := by
          change j ∈ writesBefore M c t
          rw [writesBefore, Finset.mem_filter]
          exact ⟨Finset.mem_range.mpr hj, by simpa [WritesAt] using hn⟩
        exact hSne ⟨j, hmem⟩
      have hlocal := head_lt_at_next_write c hfree hstart0 hhalt hopt
      have hlen : c.tp.length ≤ (run M t c).tp.length :=
        run_tp_length_mono M c (Nat.zero_le t)
      omega

/-- The moving-frontier result specialized to initialized runs. -/
theorem finalTape_le_distinctRows (M : Machine) (x : List Bool) {T : ℕ}
    (hfirst : ∀ j, j < T → M.halt (run M j (init M x)).st = false) :
    (run M T (init M x)).tp.length ≤ x.length +
      (Fintype.card (stopBeforeWrite M).State + 1) * distinctRows (traceObj M T x) :=
  finalTape_le_of_writeHeadBound M x
    (writeHeadBound_of_firstHalting M (init M x) (by simp [init]) hfirst)

/-! ## Full time bound and polynomial packaging -/

/-- **Full no-empty-space bound.**  First-halt time is polynomially bounded by input length and
the exact number of distinct tape snapshots. -/
theorem time_le_distinctRows (M : Machine) (x : List Bool) {T : ℕ}
    (hhalt : M.halt (run M T (init M x)).st = true)
    (hfirst : ∀ j, j < T → M.halt (run M j (init M x)).st = false) :
    T ≤ Fintype.card M.State *
      (x.length + (Fintype.card (stopBeforeWrite M).State + 1) *
        distinctRows (traceObj M T x) + 1 + Fintype.card M.State) *
      distinctRows (traceObj M T x) := by
  let D := distinctRows (traceObj M T x)
  let S := Fintype.card M.State
  let K := Fintype.card (stopBeforeWrite M).State + 1
  have ht := time_le_finalTape_mul_distinctRows M x hhalt hfirst
  have hf := finalTape_le_distinctRows M x hfirst
  have hf' : (run M T (init M x)).tp.length ≤ x.length + K * D := by
    simpa [K, D] using hf
  change T ≤ S * (x.length + K * D + 1 + S) * D
  calc
    T ≤ T + 1 := Nat.le_succ T
    _ ≤ S * ((run M T (init M x)).tp.length + 1 + S) * D := by
      simpa [S, D] using ht
    _ ≤ S * (x.length + K * D + 1 + S) * D := by
      apply Nat.mul_le_mul_right
      apply Nat.mul_le_mul_left
      exact Nat.add_le_add_right (Nat.add_le_add_right hf' 1) S

/-- The explicitly polynomially bounded clock obtained from a polynomial distinct-row bound. -/
def distinctRowsClock (M : Machine) (p : ℕ → ℕ) (n : ℕ) : ℕ :=
  Fintype.card M.State *
    (n + (Fintype.card (stopBeforeWrite M).State + 1) * p n + 1 +
      Fintype.card M.State) * p n

/-- `distinctRowsClock M p` is polynomial whenever `p` is polynomial. -/
theorem polyBounded_distinctRowsClock (M : Machine) (p : ℕ → ℕ)
    (hp : PvsNPSeparatingInvariant.PolyBounded p) :
    PvsNPSeparatingInvariant.PolyBounded (distinctRowsClock M p) := by
  let S := Fintype.card M.State
  let K := Fintype.card (stopBeforeWrite M).State + 1
  let C := S * (K + S + 2)
  apply ObserverInvariantBridge.polyBounded_of_le
    (h := fun n => C * (p n + n + 1) ^ 2)
  · intro n
    let A := p n + n + 1
    have hA : 1 ≤ A := by simp [A]
    have hpA : p n ≤ A := by simp only [A]; omega
    have hnA : n ≤ A := by simp [A]; omega
    have h1A : 1 ≤ A := hA
    have hSA : S ≤ S * A := by
      have := Nat.mul_le_mul_left S hA
      simpa using this
    have hKA : K * p n ≤ K * A := Nat.mul_le_mul_left K hpA
    have hbase : n + K * p n + 1 + S ≤ (K + S + 2) * A := by
      calc
        n + K * p n + 1 + S ≤ A + K * A + A + S * A := by omega
        _ = (K + S + 2) * A := by ring
    change S * (n + K * p n + 1 + S) * p n ≤ C * A ^ 2
    calc
      S * (n + K * p n + 1 + S) * p n
          ≤ S * ((K + S + 2) * A) * A :=
            Nat.mul_le_mul (Nat.mul_le_mul_left S hbase) hpA
      _ = C * A ^ 2 := by simp [C]; ring
  · exact ObserverInvariantBridge.polyBounded_time_comp C 2 hp

/-- **Machine-checked discharge of the head-as-data obstruction.** -/
theorem noEmptySpaceComputation : NoEmptySpaceComputation := by
  intro M p hp hrows
  refine ⟨distinctRowsClock M p, polyBounded_distinctRowsClock M p hp, ?_⟩
  intro x T hhalt hfirst
  have ht := time_le_distinctRows M x hhalt hfirst
  have hD := hrows x T hhalt hfirst
  unfold distinctRowsClock
  exact ht.trans (by
    apply Nat.mul_le_mul
    · apply Nat.mul_le_mul_left
      exact Nat.add_le_add_right
        (Nat.add_le_add_right
          (Nat.add_le_add_left (Nat.mul_le_mul_left _ hD) x.length) 1)
        (Fintype.card M.State)
    · exact hD)

end PallLean.Paper93.DeepMath.PathB.HennieFrontierAccounting
