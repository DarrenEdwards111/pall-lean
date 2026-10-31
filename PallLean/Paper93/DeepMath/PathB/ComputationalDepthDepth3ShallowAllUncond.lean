import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightBudgetUncond

/-!
# Tight switching, step 33: unconditional collapse-existence (branch `razborov-recoverRho-wip`)

`exists_shallow_all_tight` (step 11) with the empty-skip hypotheses dropped: the per-gate union bound now
uses `tight_switching_budget_uncond` (step 32), so no `hnf`/`hleaf`/`hpos` are needed — only per-gate width
(`hw`) and clause-count (`hm`) bounds.  If `#gates · r^s/(1-r) < 1` (`r = (2p/(1-p))·(2wm)`) then some
restriction makes every gate's single-literal canonical tree shallow.

* `exists_shallow_all_tight_uncond` — unconditional `F`-independent collapse-existence.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Unconditional collapse-existence.**  No alive/leaf/position hypotheses: given per-gate width `≤ w` and
clause-count `≤ m`, and the `F`-independent union bound `#gates · r^s/(1-r) < 1`, some restriction makes every
gate shallow (`depth < s`). -/
theorem exists_shallow_all_tight_uncond {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s m : ℕ} [NeZero w] [NeZero m] (G : Finset (List (Clause n)))
    (hw : ∀ g ∈ G, ∀ T ∈ g, T.lits.length ≤ w) (hm : ∀ g ∈ G, g.length ≤ m)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) < 1)
    (hsmall : (G.card : ℚ)
        * (((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s
            / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)))) < 1) :
    ∃ ρ : Restriction n, ∀ g ∈ G, (canonicalDT g F ρ).depth < s := by
  classical
  by_contra hcon
  push_neg at hcon
  set cap : ℚ := ((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s
    / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) with hcap
  have hpw_nonneg : ∀ ρ : Restriction n, 0 ≤ pweight p ρ :=
    fun ρ => pweight_nonneg hp0 (by linarith) ρ
  have key : (1 : ℚ) ≤ (G.card : ℚ) * cap := by
    calc (1 : ℚ) = ∑ ρ : Restriction n, pweight p ρ := (pweight_sum_eq_one p).symm
      _ ≤ ∑ ρ : Restriction n, ∑ g ∈ G,
            (if s ≤ (canonicalDT g F ρ).depth then pweight p ρ else 0) := by
        apply Finset.sum_le_sum
        intro ρ _
        obtain ⟨g, hg, hgρ⟩ := hcon ρ
        have hnn : ∀ g' ∈ G,
            (0 : ℚ) ≤ (if s ≤ (canonicalDT g' F ρ).depth then pweight p ρ else 0) := by
          intro g' _
          split
          · exact hpw_nonneg ρ
          · exact le_refl 0
        have hsingle := Finset.single_le_sum hnn hg
        rwa [if_pos hgρ] at hsingle
      _ = ∑ g ∈ G, ∑ ρ : Restriction n,
            (if s ≤ (canonicalDT g F ρ).depth then pweight p ρ else 0) := Finset.sum_comm
      _ ≤ ∑ _g ∈ G, cap := by
        apply Finset.sum_le_sum
        intro g hg
        rw [← Finset.sum_filter]
        exact tight_switching_budget_uncond hp0 hp3 (cs := g) (hw g hg) (hm g hg) hr1
      _ = (G.card : ℚ) * cap := by rw [Finset.sum_const, nsmul_eq_mul]
  linarith

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.exists_shallow_all_tight_uncond
