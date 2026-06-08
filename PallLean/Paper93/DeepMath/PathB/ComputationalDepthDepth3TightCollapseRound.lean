import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseCoreTight
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightSwitchingBudget
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3StarTail
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PNormalize

/-!
# Tight switching, step 12: one `F`-independent collapse round (branch `razborov-recoverRho-wip`)

The payoff of the tight route: a *single* restriction that simultaneously (i) keeps the star count bounded
(`stars ρ ≤ F`, so the canonical tree's eval-correctness applies) and (ii) collapses **every** bottom gate
to a width-`< s` CNF on the `ρ`-subcube — with the union-bound threshold `F`-**independent**.

The construction folds the `{stars > F}` star tail into the `F`-independent deep-gate union bound:

```
  1 = ∑_ρ pweight p ρ
    ≤ ∑_{F < stars ρ} pweight p ρ  +  ∑_{g∈G} ∑_{ρ : depth_g ρ ≥ s} pweight p ρ
    ≤ (star tail)                  +  #gates · r^s/(1-r),                  r = 4pw/(1-p).
```

So if `(star tail) + #gates·r^s/(1-r) < 1` then some `ρ` has `stars ρ ≤ F` **and** every gate shallow;
`collapse_core_tight` (step 4) then turns each shallow gate into a width-`< s` CNF computing it on the
`ρ`-subcube.  The deep-gate cap is the `F`-independent `tight_switching_budget` (step 10); the star-tail
term is a genuine quantity bounded by `stars_tail_ge` (Markov on `t^stars`, `t > 1`).  Both threshold terms
are `F`-independent at the tight parameter `p ≈ 1/(4w)`, which is exactly what removed the depth-3 vacuity.

## The standing hypotheses (honest)

Inherited from `tight_switching_budget`: the per-gate *global* alive (`hnf`), leaf (`hleaf`) and position
(`hpos`) hypotheses — the empty-skip wall (`decodedSel_not_filter_invariant`), carried explicitly.  So this
is one `F`-independent collapse round *conditional on the empty-skip wall*.

* `tight_collapse_round` — `(star tail) + #gates·r^s/(1-r) < 1 ⟹ ∃ ρ, stars ρ ≤ F ∧ ∀ g ∈ G,`
  `dtreeToCNF (toDTree (canonicalDT g F ρ))` computes `g` on the `ρ`-subcube with every clause width `< s`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **One `F`-independent collapse round.**  Under the global alive/leaf/position hypotheses (per gate),
the tight regime `r < 1`, and the `F`-independent union bound `(star tail) + #gates·r^s/(1-r) < 1`, there is
a single restriction `ρ` with `stars ρ ≤ F` collapsing every gate to a width-`< s` CNF computing it on the
`ρ`-subcube. -/
theorem tight_collapse_round {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s : ℕ} [NeZero w] (G : Finset (List (Clause n)))
    (hnf : ∀ g ∈ G, ∀ ρ : Restriction n, ∀ U ∈ g,
      SwitchingCounting.termFalsified ρ U = false)
    (hleaf : ∀ g ∈ G, ∀ ρ : Restriction n,
      SwitchingCounting.anyTermSat g (deepestEnd g F ρ) = false)
    (hpos : ∀ g ∈ G, ∀ ρ : Restriction n, ∀ q ∈ deepestFullSeq g F ρ, q.1 < w)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ)) < 1)
    (hsmall :
        (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => F < SwitchingCounting.stars ρ),
            pweight p ρ)
          + (G.card : ℚ)
              * (((2 * p / (1 - p)) * (2 * (w : ℚ))) ^ s
                  / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ)))) < 1) :
    ∃ ρ : Restriction n, SwitchingCounting.stars ρ ≤ F ∧
      ∀ g ∈ G,
        (∀ x, DTree.agreeRestriction ρ x →
            cnfValue (dtreeToCNF (toDTree (canonicalDT g F ρ))) x = DTree.dnfValue g x)
          ∧ (∀ C ∈ dtreeToCNF (toDTree (canonicalDT g F ρ)), C.lits.length < s) := by
  classical
  set cap : ℚ := ((2 * p / (1 - p)) * (2 * (w : ℚ))) ^ s
    / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ))) with hcap
  have hpw_nonneg : ∀ ρ : Restriction n, 0 ≤ pweight p ρ :=
    fun ρ => pweight_nonneg hp0 (by linarith) ρ
  -- Step 1: existence of a low-star, all-shallow restriction (the `F`-independent union bound).
  have hexists : ∃ ρ : Restriction n, SwitchingCounting.stars ρ ≤ F ∧
      ∀ g ∈ G, (canonicalDT g F ρ).depth < s := by
    by_contra hcon
    push_neg at hcon
    -- `hcon ρ : stars ρ ≤ F → ∃ g ∈ G, s ≤ depth_g ρ`; recast as the disjunction.
    have hcase : ∀ ρ : Restriction n,
        F < SwitchingCounting.stars ρ ∨ ∃ g ∈ G, s ≤ (canonicalDT g F ρ).depth := by
      intro ρ
      by_cases hst : F < SwitchingCounting.stars ρ
      · exact Or.inl hst
      · obtain ⟨g, hg, hgρ⟩ := hcon ρ (Nat.le_of_not_lt hst)
        exact Or.inr ⟨g, hg, hgρ⟩
    have key : (1 : ℚ) ≤
        (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => F < SwitchingCounting.stars ρ),
            pweight p ρ) + (G.card : ℚ) * cap := by
      calc (1 : ℚ) = ∑ ρ : Restriction n, pweight p ρ := (pweight_sum_eq_one p).symm
        _ ≤ ∑ ρ : Restriction n,
              ((if F < SwitchingCounting.stars ρ then pweight p ρ else 0)
                + ∑ g ∈ G, (if s ≤ (canonicalDT g F ρ).depth then pweight p ρ else 0)) := by
            apply Finset.sum_le_sum
            intro ρ _
            have hsum_nn : (0 : ℚ) ≤
                ∑ g ∈ G, (if s ≤ (canonicalDT g F ρ).depth then pweight p ρ else 0) :=
              Finset.sum_nonneg
                (fun g' _ => by split <;> first | exact hpw_nonneg ρ | exact le_refl 0)
            have hstar_nn : (0 : ℚ) ≤ (if F < SwitchingCounting.stars ρ then pweight p ρ else 0) := by
              split <;> first | exact hpw_nonneg ρ | exact le_refl 0
            rcases hcase ρ with hst | ⟨g, hg, hgρ⟩
            · rw [if_pos hst]; linarith
            · have hnn : ∀ g' ∈ G,
                  (0 : ℚ) ≤ (if s ≤ (canonicalDT g' F ρ).depth then pweight p ρ else 0) :=
                fun g' _ => by split <;> first | exact hpw_nonneg ρ | exact le_refl 0
              have hsingle := Finset.single_le_sum hnn hg
              rw [if_pos hgρ] at hsingle
              linarith
        _ = (∑ ρ : Restriction n, (if F < SwitchingCounting.stars ρ then pweight p ρ else 0))
              + ∑ ρ : Restriction n,
                  ∑ g ∈ G, (if s ≤ (canonicalDT g F ρ).depth then pweight p ρ else 0) :=
            Finset.sum_add_distrib
        _ = (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => F < SwitchingCounting.stars ρ),
                pweight p ρ)
              + ∑ g ∈ G, ∑ ρ : Restriction n,
                  (if s ≤ (canonicalDT g F ρ).depth then pweight p ρ else 0) := by
            rw [Finset.sum_filter, Finset.sum_comm]
        _ ≤ (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => F < SwitchingCounting.stars ρ),
                pweight p ρ) + (G.card : ℚ) * cap := by
            have hgate : ∑ g ∈ G, ∑ ρ : Restriction n,
                (if s ≤ (canonicalDT g F ρ).depth then pweight p ρ else 0) ≤ (G.card : ℚ) * cap := by
              calc ∑ g ∈ G, ∑ ρ : Restriction n,
                      (if s ≤ (canonicalDT g F ρ).depth then pweight p ρ else 0)
                  ≤ ∑ _g ∈ G, cap := by
                    apply Finset.sum_le_sum
                    intro g hg
                    rw [← Finset.sum_filter]
                    exact tight_switching_budget hp0 hp3 (cs := g)
                      (hnf g hg) (hleaf g hg) (hpos g hg) hr1
                _ = (G.card : ℚ) * cap := by rw [Finset.sum_const, nsmul_eq_mul]
            linarith
    linarith
  -- Step 2: feed the witness into the tight collapse core, gate by gate.
  obtain ⟨ρ, hstars, hshallow⟩ := hexists
  exact ⟨ρ, hstars, fun g hg => collapse_core_tight F s g hstars (hshallow g hg)⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.tight_collapse_round
