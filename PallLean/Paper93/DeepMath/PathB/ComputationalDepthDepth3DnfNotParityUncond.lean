import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightBudgetUncond
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightParity

/-!
# Tight switching, step 34: unconditional single-DNF parity refutation (branch `razborov-recoverRho-wip`)

`exists_survivor_shallow` and `tight_dnf_not_parity` (step 15) with the empty-skip hypotheses dropped: the
deep-gate term of the three-event union bound now uses `tight_switching_budget_uncond` (step 32).  A single
bottom DNF `D` (width `≤ w`, `≤ m` terms) disagrees with parity somewhere on the subcube — **unconditionally**
(no `hnf`/`hleaf`/`hpos`), `F`-independent at `p ≈ 1/(4wm)`.

* `exists_survivor_shallow_uncond` — the three-event union bound with the unconditional deep cap.
* `tight_dnf_not_parity_uncond` — the unconditional single-DNF parity refutation.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The three-event union bound, unconditional.**  No alive/leaf/position hypotheses: with per-gate width
`≤ w` and clause-count `≤ m`, if the low/high star tails and the `F`-independent deep cap total `< 1`, some
restriction has `s ≤ stars ρ ≤ F` and makes every gate shallow. -/
theorem exists_survivor_shallow_uncond {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s m : ℕ} [NeZero w] [NeZero m] (G : Finset (List (Clause n)))
    (hw : ∀ g ∈ G, ∀ T ∈ g, T.lits.length ≤ w) (hm : ∀ g ∈ G, g.length ≤ m)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) < 1)
    (hsmall :
        (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ < s),
            pweight p ρ)
          + (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => F < SwitchingCounting.stars ρ),
              pweight p ρ)
          + (G.card : ℚ)
              * (((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s
                  / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)))) < 1) :
    ∃ ρ : Restriction n, s ≤ SwitchingCounting.stars ρ ∧ SwitchingCounting.stars ρ ≤ F ∧
      ∀ g ∈ G, (canonicalDT g F ρ).depth < s := by
  classical
  set cap : ℚ := ((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s
    / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) with hcap
  have hpw_nonneg : ∀ ρ : Restriction n, 0 ≤ pweight p ρ :=
    fun ρ => pweight_nonneg hp0 (by linarith) ρ
  by_contra hcon
  push_neg at hcon
  have hcase : ∀ ρ : Restriction n,
      SwitchingCounting.stars ρ < s ∨ F < SwitchingCounting.stars ρ
        ∨ ∃ g ∈ G, s ≤ (canonicalDT g F ρ).depth := by
    intro ρ
    by_cases h1 : SwitchingCounting.stars ρ < s
    · exact Or.inl h1
    · by_cases h2 : F < SwitchingCounting.stars ρ
      · exact Or.inr (Or.inl h2)
      · obtain ⟨g, hg, hgρ⟩ := hcon ρ (Nat.le_of_not_lt h1) (Nat.le_of_not_lt h2)
        exact Or.inr (Or.inr ⟨g, hg, hgρ⟩)
  have key : (1 : ℚ) ≤
      (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ < s),
          pweight p ρ)
        + (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => F < SwitchingCounting.stars ρ),
            pweight p ρ)
        + (G.card : ℚ) * cap := by
    calc (1 : ℚ) = ∑ ρ : Restriction n, pweight p ρ := (pweight_sum_eq_one p).symm
      _ ≤ ∑ ρ : Restriction n,
            ((if SwitchingCounting.stars ρ < s then pweight p ρ else 0)
              + (if F < SwitchingCounting.stars ρ then pweight p ρ else 0)
              + ∑ g ∈ G, (if s ≤ (canonicalDT g F ρ).depth then pweight p ρ else 0)) := by
          apply Finset.sum_le_sum
          intro ρ _
          have hlo_nn : (0 : ℚ) ≤ (if SwitchingCounting.stars ρ < s then pweight p ρ else 0) := by
            split <;> first | exact hpw_nonneg ρ | exact le_refl 0
          have hhi_nn : (0 : ℚ) ≤ (if F < SwitchingCounting.stars ρ then pweight p ρ else 0) := by
            split <;> first | exact hpw_nonneg ρ | exact le_refl 0
          have hsum_nn : (0 : ℚ) ≤
              ∑ g ∈ G, (if s ≤ (canonicalDT g F ρ).depth then pweight p ρ else 0) :=
            Finset.sum_nonneg
              (fun g' _ => by split <;> first | exact hpw_nonneg ρ | exact le_refl 0)
          rcases hcase ρ with hlo | hhi | ⟨g, hg, hgρ⟩
          · rw [if_pos hlo]; linarith
          · rw [if_pos hhi]; linarith
          · have hnn : ∀ g' ∈ G,
                (0 : ℚ) ≤ (if s ≤ (canonicalDT g' F ρ).depth then pweight p ρ else 0) :=
              fun g' _ => by split <;> first | exact hpw_nonneg ρ | exact le_refl 0
            have hsingle := Finset.single_le_sum hnn hg
            rw [if_pos hgρ] at hsingle
            linarith
      _ = (∑ ρ : Restriction n, (if SwitchingCounting.stars ρ < s then pweight p ρ else 0))
            + (∑ ρ : Restriction n, (if F < SwitchingCounting.stars ρ then pweight p ρ else 0))
            + ∑ ρ : Restriction n,
                ∑ g ∈ G, (if s ≤ (canonicalDT g F ρ).depth then pweight p ρ else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ < s),
              pweight p ρ)
            + (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => F < SwitchingCounting.stars ρ),
                pweight p ρ)
            + ∑ g ∈ G, ∑ ρ : Restriction n,
                (if s ≤ (canonicalDT g F ρ).depth then pweight p ρ else 0) := by
          rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_comm]
      _ ≤ (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ < s),
              pweight p ρ)
            + (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => F < SwitchingCounting.stars ρ),
                pweight p ρ)
            + (G.card : ℚ) * cap := by
          have hgate : ∑ g ∈ G, ∑ ρ : Restriction n,
              (if s ≤ (canonicalDT g F ρ).depth then pweight p ρ else 0) ≤ (G.card : ℚ) * cap := by
            calc ∑ g ∈ G, ∑ ρ : Restriction n,
                    (if s ≤ (canonicalDT g F ρ).depth then pweight p ρ else 0)
                ≤ ∑ _g ∈ G, cap := by
                  apply Finset.sum_le_sum
                  intro g hg
                  rw [← Finset.sum_filter]
                  exact tight_switching_budget_uncond hp0 hp3 (cs := g) (hw g hg) (hm g hg) hr1
              _ = (G.card : ℚ) * cap := by rw [Finset.sum_const, nsmul_eq_mul]
          linarith
  linarith

/-- **The unconditional single-DNF parity refutation.**  No alive/leaf/position hypotheses: a single bottom
DNF `D` (width `≤ w`, `≤ m` terms) disagrees with parity at some subcube point. -/
theorem tight_dnf_not_parity_uncond {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s m : ℕ} [NeZero w] [NeZero m] (D : List (Clause n))
    (hw : ∀ T ∈ D, T.lits.length ≤ w) (hm : D.length ≤ m)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) < 1)
    (hsmall :
        (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ < s),
            pweight p ρ)
          + (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => F < SwitchingCounting.stars ρ),
              pweight p ρ)
          + (((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s
              / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)))) < 1) :
    ∃ (ρ : Restriction n) (x : Fin n → Bool),
      DTree.agreeRestriction ρ x ∧ DTree.dnfValue D x ≠ DTree.parity x := by
  classical
  obtain ⟨ρ, hge, hle, hshallow⟩ :=
    exists_survivor_shallow_uncond hp0 hp3 ({D} : Finset (List (Clause n)))
      (fun g hg T hT => by rw [Finset.mem_singleton] at hg; subst hg; exact hw T hT)
      (fun g hg => by rw [Finset.mem_singleton] at hg; subst hg; exact hm)
      hr1
      (by rw [Finset.card_singleton, Nat.cast_one, one_mul]; exact hsmall)
  have hsh : (canonicalDT D F ρ).depth < SwitchingCounting.stars ρ :=
    lt_of_lt_of_le (hshallow D (Finset.mem_singleton.mpr rfl)) hge
  obtain ⟨x, hx, hne⟩ := shallow_canonicalDT_not_parity D F ρ hle hsh
  exact ⟨ρ, x, hx, hne⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.tight_dnf_not_parity_uncond
