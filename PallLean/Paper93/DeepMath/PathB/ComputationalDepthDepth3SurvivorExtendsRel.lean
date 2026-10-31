import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BudgetExtends
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SurvivorExtendsUncond

/-!
# Tight switching, step 81: the subcube-relative survivor budget (box-factor) (branch `razborov-recoverRho-wip`)

`exists_survivor_shallow_extends_uncond` (step 36) bounded the deep-gate mass by the *absolute* `cap` (summing
the per-gate budget over `univ`).  Here the gate term is bounded *relative to the box* by
`tight_switching_budget_extends_uncond` (step 80) — directly over `extBox τ`, with no lossy detour through
`univ` — so the deep term is `card · cap · box`.  Dividing the survivor inequality by the box mass turns
`hsmall` into the **box-free** condition `(low-star)/box + card·cap < 1`, i.e. the `gap ∧ h2_rel_clean` split.

* `exists_survivor_shallow_extends_REL` — the subcube-relative survivor budget with the box-factor deep term.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The subcube-relative survivor-shallow existence (box-factor).**  As `exists_survivor_shallow_extends
_uncond`, but the deep-gate term is `card · cap · box` (relative), so `hsmall` is the box-free union bound. -/
theorem exists_survivor_shallow_extends_REL {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s m : ℕ} [NeZero w] [NeZero m] (hF : n ≤ F) (τ : Fin n → Option Bool)
    (G : Finset (List (Clause n)))
    (hw : ∀ g ∈ G, ∀ T ∈ g, T.lits.length ≤ w) (hm : ∀ g ∈ G, g.length ≤ m)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) < 1)
    (hsmall :
        (∑ σ ∈ (extBox τ).filter (fun σ => SwitchingCounting.stars σ < s), pweight p σ)
          + (G.card : ℚ)
              * ((((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s
                  / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))))
                * ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ))
        < ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ)) :
    ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ s ≤ SwitchingCounting.stars ρ ∧
      SwitchingCounting.stars ρ ≤ F ∧ ∀ g ∈ G, (canonicalDT g F ρ).depth < s := by
  classical
  set cap : ℚ := ((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s
    / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) with hcap
  set box : ℚ := ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ) with hbox
  have hpw_nonneg : ∀ ρ : Restriction n, 0 ≤ pweight p ρ :=
    fun ρ => pweight_nonneg hp0 (by linarith) ρ
  have hsF : ∀ ρ : Restriction n, SwitchingCounting.stars ρ ≤ F :=
    fun ρ => le_trans (by rw [stars]; exact le_trans (Finset.card_le_univ _) (by simp)) hF
  by_contra hcon
  push_neg at hcon
  have hcase : ∀ σ ∈ extBox τ,
      SwitchingCounting.stars σ < s ∨ ∃ g ∈ G, s ≤ (canonicalDT g F σ).depth := by
    intro σ hσ
    by_cases h1 : SwitchingCounting.stars σ < s
    · exact Or.inl h1
    · obtain ⟨g, hg, hgσ⟩ := hcon σ (mem_extBox.mp hσ) (Nat.le_of_not_lt h1) (hsF σ)
      exact Or.inr ⟨g, hg, hgσ⟩
  have key : box ≤
      (∑ σ ∈ (extBox τ).filter (fun σ => SwitchingCounting.stars σ < s), pweight p σ)
        + (G.card : ℚ) * (cap * box) := by
    calc box
        = ∑ σ ∈ extBox τ, pweight p σ := (pweight_sum_extends p τ).symm
      _ ≤ ∑ σ ∈ extBox τ,
            ((if SwitchingCounting.stars σ < s then pweight p σ else 0)
              + ∑ g ∈ G, (if s ≤ (canonicalDT g F σ).depth then pweight p σ else 0)) := by
          apply Finset.sum_le_sum
          intro σ hσ
          have hsum_nn : (0 : ℚ) ≤
              ∑ g ∈ G, (if s ≤ (canonicalDT g F σ).depth then pweight p σ else 0) :=
            Finset.sum_nonneg
              (fun g' _ => by split <;> first | exact hpw_nonneg σ | exact le_refl 0)
          have hlo_nn : (0 : ℚ) ≤ (if SwitchingCounting.stars σ < s then pweight p σ else 0) := by
            split <;> first | exact hpw_nonneg σ | exact le_refl 0
          rcases hcase σ hσ with hlo | ⟨g, hg, hgσ⟩
          · rw [if_pos hlo]; linarith
          · have hnn : ∀ g' ∈ G,
                (0 : ℚ) ≤ (if s ≤ (canonicalDT g' F σ).depth then pweight p σ else 0) :=
              fun g' _ => by split <;> first | exact hpw_nonneg σ | exact le_refl 0
            have hsingle := Finset.single_le_sum hnn hg
            rw [if_pos hgσ] at hsingle
            linarith
      _ = (∑ σ ∈ extBox τ, (if SwitchingCounting.stars σ < s then pweight p σ else 0))
            + ∑ σ ∈ extBox τ,
                ∑ g ∈ G, (if s ≤ (canonicalDT g F σ).depth then pweight p σ else 0) :=
          Finset.sum_add_distrib
      _ = (∑ σ ∈ (extBox τ).filter (fun σ => SwitchingCounting.stars σ < s), pweight p σ)
            + ∑ g ∈ G, ∑ σ ∈ extBox τ,
                (if s ≤ (canonicalDT g F σ).depth then pweight p σ else 0) := by
          rw [Finset.sum_filter, Finset.sum_comm]
      _ ≤ (∑ σ ∈ (extBox τ).filter (fun σ => SwitchingCounting.stars σ < s), pweight p σ)
            + (G.card : ℚ) * (cap * box) := by
          have hgate : ∑ g ∈ G, ∑ σ ∈ extBox τ,
              (if s ≤ (canonicalDT g F σ).depth then pweight p σ else 0)
                ≤ (G.card : ℚ) * (cap * box) := by
            calc ∑ g ∈ G, ∑ σ ∈ extBox τ,
                    (if s ≤ (canonicalDT g F σ).depth then pweight p σ else 0)
                ≤ ∑ _g ∈ G, cap * box := by
                  apply Finset.sum_le_sum
                  intro g hg
                  rw [← Finset.sum_filter]
                  exact tight_switching_budget_extends_uncond hp0 hp3 τ
                    (hw g hg) (hm g hg) hr1
              _ = (G.card : ℚ) * (cap * box) := by rw [Finset.sum_const, nsmul_eq_mul]
          linarith
  linarith

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.exists_survivor_shallow_extends_REL
