import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightCollapseRound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PWeightExtends
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3StarTailExtends

/-!
# Tight switching, step 18: the subcube-relative survivor budget (branch `razborov-recoverRho-wip`)

The genuinely-open analytic input of the multi-round loop, now discharged in the tight, `F`-independent
setting.  To iterate the collapse round (`collapse_or_layer_tight`, step 16) we must apply switching on each
round's *free* coordinates — i.e. restrict to the subcube `extBox τ` of restrictions extending the previous
round's `τ` — and still keep enough survivors (`s ≤ stars ρ`) for the parity capstone.

We run the union bound on the **conditional** measure (total mass `((1-p)/2)^(n - stars τ)`,
`pweight_sum_extends`) over `extBox τ`.  Two bad events:

* **too few survivors** `{stars ρ < s}`: conditional low star tail, bounded by `stars_tail_le_extends`
  (Markov on `t^stars`, `t < 1`) — `≤ ((1-p)/2)^(n-stars τ)·(t·p+(1-p))^{stars τ} / t^{s-1}`;
* **some gate deep** `{∃ g, depth_g ≥ s}`: the deep weight *inside the box* is `≤` the full deep weight,
  which `tight_switching_budget` (step 10) caps at `#gates·r^s/(1-r)` — `F`-independent — by subset.

Crucially the *high* star tail `{F < stars ρ}` is **vacuous**: `stars ρ ≤ n ≤ F`, so taking `F ≥ n` (which —
unlike the crude route — costs nothing in the `F`-independent budget) removes it entirely.  Hence if

```
  (low star tail)  +  #gates · r^s/(1-r)  <  ((1-p)/2)^(n - stars τ),
```

some `ρ` extends `τ`, has `s ≤ stars ρ ≤ F`, and makes every gate shallow — exactly the survivor budget the
nested iteration needs.

* `exists_survivor_shallow_extends` — the subcube-relative survivor-shallow existence.

## Honest scope

The low star tail is left as an explicit sum in the union-bound hypothesis, discharged by
`stars_tail_le_extends` for a chosen `t < 1` (the conditional concentration).  The per-gate alive/leaf/
position hypotheses (the empty-skip wall, brick 49) are carried explicitly.  This is the per-round
subcube-relative budget; chaining it through `iterated_not_parity_tight` (step 17) with nested `τ`'s — so the
survivor counts stay above `s` across all `d` rounds — is the final structural assembly.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The subcube-relative survivor-shallow existence.**  On the conditional measure over `extBox τ`, with
the low star tail and the `F`-independent deep cap together below the box mass, some restriction extends `τ`,
keeps `s ≤ stars ρ ≤ F`, and makes every gate's single-literal canonical tree shallow. -/
theorem exists_survivor_shallow_extends {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s : ℕ} [NeZero w] (hF : n ≤ F) (τ : Fin n → Option Bool)
    (G : Finset (List (Clause n)))
    (hnf : ∀ g ∈ G, ∀ ρ : Restriction n, ∀ U ∈ g,
      SwitchingCounting.termFalsified ρ U = false)
    (hleaf : ∀ g ∈ G, ∀ ρ : Restriction n,
      SwitchingCounting.anyTermSat g (deepestEnd g F ρ) = false)
    (hpos : ∀ g ∈ G, ∀ ρ : Restriction n, ∀ q ∈ deepestFullSeq g F ρ, q.1 < w)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ)) < 1)
    (hsmall :
        (∑ σ ∈ (extBox τ).filter (fun σ => SwitchingCounting.stars σ < s), pweight p σ)
          + (G.card : ℚ)
              * (((2 * p / (1 - p)) * (2 * (w : ℚ))) ^ s
                  / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ))))
        < ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ)) :
    ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ s ≤ SwitchingCounting.stars ρ ∧
      SwitchingCounting.stars ρ ≤ F ∧ ∀ g ∈ G, (canonicalDT g F ρ).depth < s := by
  classical
  set cap : ℚ := ((2 * p / (1 - p)) * (2 * (w : ℚ))) ^ s
    / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ))) with hcap
  have hpw_nonneg : ∀ ρ : Restriction n, 0 ≤ pweight p ρ :=
    fun ρ => pweight_nonneg hp0 (by linarith) ρ
  -- `stars ρ ≤ F` for free (`stars ρ ≤ n ≤ F`); the high star tail is vacuous.
  have hsF : ∀ ρ : Restriction n, SwitchingCounting.stars ρ ≤ F :=
    fun ρ => le_trans (by rw [stars]; exact le_trans (Finset.card_le_univ _) (by simp)) hF
  by_contra hcon
  push_neg at hcon
  -- every box restriction is too-shallow-on-survivors or has a deep gate.
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
                        exact tight_switching_budget hp0 hp3 (cs := g)
                          (hnf g hg) (hleaf g hg) (hpos g hg) hr1
              _ = (G.card : ℚ) * cap := by rw [Finset.sum_const, nsmul_eq_mul]
          linarith
  linarith

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.exists_survivor_shallow_extends
