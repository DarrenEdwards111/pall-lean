import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHennieDrift

/-!
# The peak lemma: the head stays within `|State|` of the blank frontier

Building on `no_rightward_repeat` (the drift core), this file proves the excursion-peak bound: if
positions `≥ R` read `false` throughout a halting run whose head starts below `R`, then the head
never exceeds `R + |State|`.

The argument: were the head to reach `R + |State|`, take the last time `t₀` before the peak with
head `< R`; on the window `(t₀, t*]` the head stays `≥ R`.  The head rises by at most one per step
(`hd_le_succ`), so the first window-times `ν₀ < ν₁ < ⋯ < ν_{|State|}` at which it reaches
`R, R+1, …, R+|State|` are well defined with `head(νᵢ) = R+i`.  These are `|State|+1` times in only
`|State|` states, so two share a state — a same-state pair with strictly increasing head and head
`≥ R` in between — which `no_rightward_repeat` forbids.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  This file proves no SAT lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.HenniePeak

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.HennieDrift (no_rightward_repeat)

variable {M : Machine}

/-- The head advances by at most one cell per step. -/
theorem moveHead_le_succ (h : ℕ) (m : Move) : moveHead h m ≤ h + 1 := by
  fin_cases m <;> simp [moveHead]
  all_goals omega

theorem hd_le_succ (c : Cfg M) (t : ℕ) : (run M (t + 1) c).hd ≤ (run M t c).hd + 1 := by
  rw [run_succ]
  by_cases h : M.halt (run M t c).st = true
  · rw [step_of_halted M h]; omega
  · unfold step
    rw [if_neg h]
    exact moveHead_le_succ _ _

/-- **The peak lemma.**  If positions `≥ R` read `false` throughout a run that first-halts at `T`,
and the head starts below `R`, then the head never reaches `R + |State|`. -/
theorem head_lt_of_blank (c : Cfg M) (R T : ℕ) (hR1 : 1 ≤ R)
    (hstart : (run M 0 c).hd < R)
    (hhalt : M.halt (run M T c).st = true)
    (hfirst : ∀ j, j < T → M.halt (run M j c).st = false)
    (hblank : ∀ t, R ≤ (run M t c).hd → (run M t c).tp.getD (run M t c).hd false = false)
    (ts : ℕ) (htsT : ts ≤ T) :
    (run M ts c).hd < R + Fintype.card M.State := by
  by_contra hcon
  push_neg at hcon   -- R + card ≤ hd(ts)
  set N := Fintype.card M.State with hN
  -- the peak time ts has head ≥ R, so ts > 0
  have hts0 : 0 < ts := by
    rcases Nat.eq_zero_or_pos ts with h0 | h0
    · rw [h0] at hcon; omega
    · exact h0
  -- window start t0: last time ≤ ts with head < R
  set S := (Finset.range (ts + 1)).filter (fun t => (run M t c).hd < R) with hS
  have h0mem : (0 : ℕ) ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hstart⟩
  have hSne : S.Nonempty := ⟨0, h0mem⟩
  set t0 := S.max' hSne with ht0
  have ht0mem : t0 ∈ S := S.max'_mem hSne
  have ht0lt : (run M t0 c).hd < R := by
    have := (Finset.mem_filter.mp ht0mem).2; exact this
  have ht0le : t0 ≤ ts := by
    have := (Finset.mem_range.mp (Finset.mem_filter.mp ht0mem).1); omega
  -- window property: for t0 < t ≤ ts, head ≥ R
  have hwin : ∀ t, t0 < t → t ≤ ts → R ≤ (run M t c).hd := by
    intro t htlo hthi
    by_contra hlt
    push_neg at hlt
    have hmem : t ∈ S := by
      rw [hS, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hlt⟩
    have := S.le_max' t hmem
    omega
  have ht0ts : t0 < ts := by
    rcases Nat.lt_or_ge t0 ts with h | h
    · exact h
    · have : t0 = ts := by omega
      rw [this] at ht0lt; omega
  have hstepR : (run M (t0 + 1) c).hd = R := by
    have hge : R ≤ (run M (t0 + 1) c).hd := hwin (t0 + 1) (by omega) (by omega)
    have hle : (run M (t0 + 1) c).hd ≤ (run M t0 c).hd + 1 := hd_le_succ c t0
    omega
  -- records over Fin (N+1): first window-time reaching R + i
  have hexFin : ∀ i : Fin (N + 1), ∃ t, t0 + 1 ≤ t ∧ R + i.val ≤ (run M t c).hd := by
    intro i
    refine ⟨ts, by omega, ?_⟩
    have := i.isLt
    omega
  let nu : Fin (N + 1) → ℕ := fun i => Nat.find (hexFin i)
  have hnu_spec : ∀ i : Fin (N + 1), t0 + 1 ≤ nu i ∧ R + i.val ≤ (run M (nu i) c).hd :=
    fun i => Nat.find_spec (hexFin i)
  have hnu_le : ∀ i : Fin (N + 1), nu i ≤ ts := by
    intro i
    exact Nat.find_le ⟨by omega, by have := i.isLt; omega⟩
  have hnu_min : ∀ (i : Fin (N + 1)) t, t < nu i →
      ¬ (t0 + 1 ≤ t ∧ R + i.val ≤ (run M t c).hd) :=
    fun i t ht => Nat.find_min (hexFin i) ht
  have hnu_hd : ∀ i : Fin (N + 1), (run M (nu i) c).hd = R + i.val := by
    intro i
    obtain ⟨hlo, hge⟩ := hnu_spec i
    rcases eq_or_lt_of_le hlo with heq | hgt
    · rw [← heq] at hge ⊢; rw [hstepR] at hge ⊢; omega
    · have hprev := hnu_min i (nu i - 1) (by omega)
      have hlo' : t0 + 1 ≤ nu i - 1 := by omega
      have hltprev : (run M (nu i - 1) c).hd < R + i.val := by
        by_contra hc; push_neg at hc; exact hprev ⟨hlo', hc⟩
      have hstep : (run M (nu i) c).hd ≤ (run M (nu i - 1) c).hd + 1 := by
        have := hd_le_succ c (nu i - 1); rwa [show nu i - 1 + 1 = nu i from by omega] at this
      omega
  have hnu_mono : ∀ i j : Fin (N + 1), i.val < j.val → nu i < nu j := by
    intro i j hij
    have hle : nu i ≤ nu j := by
      apply Nat.find_le
      obtain ⟨hlo, hge⟩ := hnu_spec j
      exact ⟨hlo, by omega⟩
    have hne : nu i ≠ nu j := by
      intro heq; have h1 := hnu_hd i; have h2 := hnu_hd j; rw [heq] at h1; omega
    omega
  obtain ⟨a, b, hab, hstab⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (N + 1) => (run M (nu i) c).st) (by rw [Fintype.card_fin, hN]; omega)
  have key : ∀ i j : Fin (N + 1), i.val < j.val →
      (run M (nu i) c).st = (run M (nu j) c).st → False := by
    intro i j hlt hsteq
    apply no_rightward_repeat c R T hR1 hhalt hfirst hblank (nu i) (nu j)
      (hnu_mono i j hlt) (le_trans (hnu_le j) htsT) hsteq
    · rw [hnu_hd i, hnu_hd j]; omega
    · intro t htlo hthi
      apply hwin t
      · have := (hnu_spec i).1; omega
      · exact le_trans hthi (hnu_le j)
  rcases lt_or_gt_of_ne (fun heq => hab (Fin.val_injective heq)) with hlt | hgt
  · exact key a b hlt hstab
  · exact key b a hgt hstab.symm

end PallLean.Paper93.DeepMath.PathB.HenniePeak
