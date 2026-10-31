import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightBudgetUncond
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PWeightExtends

/-!
# Tight switching, step 36: unconditional subcube-relative survivor budget (branch `razborov-recoverRho-wip`)

`exists_survivor_shallow_extends` (step 18) with the empty-skip hypotheses dropped: the deep-gate term of the
conditional union bound now uses `tight_switching_budget_uncond` (step 32).  This discharges the terminal
survivor budget `hterm` of `parity_not_depth3_tight_uncond` (step 35) **unconditionally** — no
`hnf`/`hleaf`/`hpos`, only per-gate width/clause-count bounds.

* `exists_survivor_shallow_extends_uncond` — the unconditional per-round subcube-relative survivor budget.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The unconditional subcube-relative survivor-shallow existence.**  No alive/leaf/position hypotheses:
with per-gate width `≤ w`, clause-count `≤ m`, and the conditional union bound below the box mass, some
restriction extends `τ`, keeps `s ≤ stars ρ ≤ F`, and makes every gate shallow. -/
theorem exists_survivor_shallow_extends_uncond {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s m : ℕ} [NeZero w] [NeZero m] (hF : n ≤ F) (τ : Fin n → Option Bool)
    (G : Finset (List (Clause n)))
    (hw : ∀ g ∈ G, ∀ T ∈ g, T.lits.length ≤ w) (hm : ∀ g ∈ G, g.length ≤ m)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) < 1)
    (hsmall :
        (∑ σ ∈ (extBox τ).filter (fun σ => SwitchingCounting.stars σ < s), pweight p σ)
          + (G.card : ℚ)
              * (((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s
                  / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))))
        < ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ)) :
    ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ s ≤ SwitchingCounting.stars ρ ∧
      SwitchingCounting.stars ρ ≤ F ∧ ∀ g ∈ G, (canonicalDT g F ρ).depth < s := by
  classical
  set cap : ℚ := ((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s
    / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) with hcap
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
    · obtain ⟨g, hg, hgσ⟩ :=
        hcon σ (mem_extBox.mp hσ) (Nat.le_of_not_lt h1) (hsF σ)
      exact Or.inr ⟨g, hg, hgσ⟩
  have key : ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ) ≤
      (∑ σ ∈ (extBox τ).filter (fun σ => SwitchingCounting.stars σ < s), pweight p σ)
        + (G.card : ℚ) * cap := by
    calc ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ)
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
            + (G.card : ℚ) * cap := by
          have hgate : ∑ g ∈ G, ∑ σ ∈ extBox τ,
              (if s ≤ (canonicalDT g F σ).depth then pweight p σ else 0)
                ≤ (G.card : ℚ) * cap := by
            calc ∑ g ∈ G, ∑ σ ∈ extBox τ,
                    (if s ≤ (canonicalDT g F σ).depth then pweight p σ else 0)
                ≤ ∑ _g ∈ G, cap := by
                  apply Finset.sum_le_sum
                  intro g hg
                  calc ∑ σ ∈ extBox τ,
                        (if s ≤ (canonicalDT g F σ).depth then pweight p σ else 0)
                      ≤ ∑ σ : Restriction n,
                          (if s ≤ (canonicalDT g F σ).depth then pweight p σ else 0) :=
                        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                          (fun σ _ _ => by split <;> first | exact hpw_nonneg σ | exact le_refl 0)
                    _ ≤ cap := by
                        rw [← Finset.sum_filter]
                        exact tight_switching_budget_uncond hp0 hp3 (cs := g)
                          (hw g hg) (hm g hg) hr1
              _ = (G.card : ℚ) * cap := by rw [Finset.sum_const, nsmul_eq_mul]
          linarith
  linarith

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.exists_survivor_shallow_extends_uncond
