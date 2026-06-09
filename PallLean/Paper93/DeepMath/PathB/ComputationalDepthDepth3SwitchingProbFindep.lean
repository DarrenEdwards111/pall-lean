import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PosValLabels
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingProbExtends
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3GeomTail

/-!
# Block-DT model, route-2 step [155c]: the F-INDEPENDENT depth-graded switching bound (branch `razborov-recoverRho-wip`)

The capstone of route 2.  The earlier `descent_switching_prob_extends` (brick 59) bounds the deep weight by
`(2p/(1-p))^s · (4^w+1)^F · (conditioning mass)`, whose `(4^w+1)^F` factor is **`F`-dependent** (the
`codesList` label space is indexed by the fuel `F`).  Here we replace it by an **`F`-independent** factor,
using the value-augmented label `descentPosValLabels` (brick 155b):

  `∑_{σ∈Bad, depth≥s} pweight σ ≤ (r')^s / (1 - r') · ∑_{ρ extends τ} pweight ρ`,   `r' = (2p/(1-p))(4w+1)`,

valid whenever `r' < 1` (small constant `p` at constant width `w`).

* `descent_switching_prob_findep` — the `F`-independent depth-graded weighted-sum bound.

The proof: gain the weight by the **full** `pathLen` (`pweight_le_ratio_pow` with the `pathLen + stars ≤ stars`
budget), inject `σ ↦ (descentSat σ, descentPosValLabels σ)` (`descentPosValLabels_injective`, valid with the
deep input varying per `σ`), bound the image by `extBox τ ×ˢ Labs`, factor out the conditioning mass, then
group the labels `Labs` by content length `k` (`≤ (4w+1)^k` of them, brick 147) and sum the geometric series
`∑_k (r')^k ≤ (r')^s/(1-r')` (`geom_shell_tail_le`).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The F-independent depth-graded switching bound.**  For `Bad` restrictions extending `τ` and all deep
(`depth ≥ s`), the deep weight is at most `(r')^s/(1-r')` times the conditioning mass, where
`r' = (2p/(1-p))(4w+1) < 1` — with **no `F`-dependence**. -/
theorem descent_switching_prob_findep {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    (cs : List (Clause n)) (hcons : ∀ T ∈ cs, Consistent T)
    (hnd : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup) (w : ℕ) [NeZero w] (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    (hr' : (2 * p / (1 - p)) * (4 * w + 1) < 1)
    (F s : ℕ) (τ : Fin n → Option Bool) {Bad : Finset (Fin n → Option Bool)}
    (hext : ∀ σ ∈ Bad, Extends τ σ)
    (hBad : ∀ σ ∈ Bad, s ≤ (canonicalDTree cs w F σ).depth) :
    (∑ σ ∈ Bad, pweight p σ)
      ≤ ((2 * p / (1 - p)) * (4 * w + 1)) ^ s / (1 - (2 * p / (1 - p)) * (4 * w + 1))
          * ∑ ρ ∈ extBox τ, pweight p ρ := by
  classical
  have hp1 : (0 : ℚ) < 1 - p := by linarith
  set r : ℚ := 2 * p / (1 - p) with hr
  set r' : ℚ := r * (4 * w + 1) with hr'def
  have hr_nonneg : 0 ≤ r := div_nonneg (by linarith) (by linarith)
  have hr'_nonneg : 0 ≤ r' := mul_nonneg hr_nonneg (by positivity)
  set xσ : (Fin n → Option Bool) → (Fin n → Bool) :=
    fun σ => Classical.choose (exists_deep_input cs w hnd F σ) with hxσ
  set g : (Fin n → Option Bool) → ((Fin n → Option Bool) × List (List (Fin w × Bool))) :=
    fun σ => (descentSat cs w F σ (xσ σ), descentPosValLabels cs w F σ (xσ σ)) with hg
  -- the injection
  have hginj : Set.InjOn g Bad := by
    intro σ1 _ σ2 _ heq
    rw [hg] at heq; simp only [Prod.mk.injEq] at heq
    exact descentPosValLabels_injective cs w hcons hw F σ1 σ2 (xσ σ1) (xσ σ2) heq.1 heq.2
  -- the set of labels that actually appear
  set Labs : Finset (List (List (Fin w × Bool))) := Bad.image (fun σ => descentPosValLabels cs w F σ (xσ σ))
    with hLabs
  have hLabsNe : ∀ L ∈ Labs, ∀ b ∈ L, b ≠ [] := by
    intro L hL b hb
    rw [hLabs, Finset.mem_image] at hL
    obtain ⟨σ, _, rfl⟩ := hL
    exact descentPosValLabels_block_nonempty cs w F σ (xσ σ) b hb
  -- STEP 1: weight gain by the full path length.
  have step1 : (∑ σ ∈ Bad, pweight p σ)
      ≤ ∑ σ ∈ Bad, r ^ (pathLen cs w F σ (xσ σ)) * pweight p (descentSat cs w F σ (xσ σ)) := by
    apply Finset.sum_le_sum
    intro σ _
    have hpl := pathLen_add_stars_descentSat_le cs w hnd F σ (xσ σ)
    exact pweight_le_ratio_pow hp0 hp3 (stars_descentSat_le cs w F σ (xσ σ)) (by omega)
  -- STEP 2: rewrite as a sum over the image of the injection.
  have step2 : (∑ σ ∈ Bad, r ^ (pathLen cs w F σ (xσ σ)) * pweight p (descentSat cs w F σ (xσ σ)))
      = ∑ q ∈ Bad.image g, r ^ (q.2.flatten.length) * pweight p q.1 := by
    rw [Finset.sum_image hginj]
    apply Finset.sum_congr rfl
    intro σ _
    rw [hg]
    simp only
    rw [descentPosValLabels_flatten_length]
  -- STEP 3: bound the image by `extBox τ ×ˢ Labs` and factor out the conditioning mass.
  have hsub : Bad.image g ⊆ (extBox τ) ×ˢ Labs := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨σ, hσ, rfl⟩ := hq
    rw [Finset.mem_product]
    refine ⟨?_, ?_⟩
    · rw [hg]; simp only
      rw [mem_extBox]
      exact Extends_trans (hext σ hσ) (descentSat_extends cs w F σ (xσ σ))
    · rw [hg, hLabs]; simp only
      exact Finset.mem_image_of_mem _ hσ
  have step3 : (∑ q ∈ Bad.image g, r ^ (q.2.flatten.length) * pweight p q.1)
      ≤ (∑ L ∈ Labs, r ^ (L.flatten.length)) * ∑ ρ ∈ extBox τ, pweight p ρ := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) ?_
    · intro q _ _
      exact mul_nonneg (pow_nonneg hr_nonneg _) (pweight_nonneg hp0 (by linarith) q.1)
    · rw [Finset.sum_product]
      apply le_of_eq
      calc (∑ ρ ∈ extBox τ, ∑ L ∈ Labs, r ^ (L.flatten.length) * pweight p ρ)
          = ∑ ρ ∈ extBox τ, (∑ L ∈ Labs, r ^ (L.flatten.length)) * pweight p ρ := by
            apply Finset.sum_congr rfl; intro ρ _; rw [Finset.sum_mul]
        _ = (∑ L ∈ Labs, r ^ (L.flatten.length)) * ∑ ρ ∈ extBox τ, pweight p ρ := by
            rw [← Finset.mul_sum]
  -- STEP 4: the label geometric sum.
  have step4 : (∑ L ∈ Labs, r ^ (L.flatten.length)) ≤ r' ^ s / (1 - r') := by
    have hmaps : ∀ L ∈ Labs, L.flatten.length ∈ Finset.Icc s n := by
      intro L hL
      rw [hLabs, Finset.mem_image] at hL
      obtain ⟨σ, hσ, rfl⟩ := hL
      rw [descentPosValLabels_flatten_length, Finset.mem_Icc]
      have hds : (canonicalDTree cs w F σ).depth ≤ pathLen cs w F σ (xσ σ) :=
        Classical.choose_spec (exists_deep_input cs w hnd F σ)
      have hsdepth := hBad σ hσ
      have hpln : pathLen cs w F σ (xσ σ) ≤ n := by
        have h1 := pathLen_add_stars_descentSat_le cs w hnd F σ (xσ σ)
        have hsn : stars σ ≤ n := le_trans (Finset.card_le_univ _) (by simp)
        omega
      exact ⟨by omega, hpln⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun L => r ^ (L.flatten.length))]
    calc (∑ k ∈ Finset.Icc s n, ∑ L ∈ Labs.filter (fun L => L.flatten.length = k), r ^ (L.flatten.length))
        ≤ ∑ k ∈ Finset.Icc s n, r' ^ k := by
          apply Finset.sum_le_sum
          intro k _
          have hcard : (Labs.filter (fun L => L.flatten.length = k)).card ≤ (4 * w + 1) ^ k := by
            have h := nonempty_block_streams_card_le (α := Fin w × Bool) k
              (S := Labs.filter (fun L => L.flatten.length = k))
              (fun L hL b hb => hLabsNe L (Finset.mem_filter.mp hL).1 b hb)
              (fun L hL => (Finset.mem_filter.mp hL).2)
            have hcc : Fintype.card (Fin w × Bool) = 2 * w := by
              rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; ring
            rw [hcc] at h
            calc (Labs.filter (fun L => L.flatten.length = k)).card
                ≤ (2 * (2 * w) + 1) ^ k := h
              _ = (4 * w + 1) ^ k := by rw [show 2 * (2 * w) + 1 = 4 * w + 1 by ring]
          calc (∑ L ∈ Labs.filter (fun L => L.flatten.length = k), r ^ (L.flatten.length))
              = ∑ _L ∈ Labs.filter (fun L => L.flatten.length = k), r ^ k := by
                apply Finset.sum_congr rfl
                intro L hL
                rw [(Finset.mem_filter.mp hL).2]
            _ = ((Labs.filter (fun L => L.flatten.length = k)).card : ℚ) * r ^ k := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ ((4 * w + 1) ^ k : ℚ) * r ^ k := by
                apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr_nonneg k)
                exact_mod_cast hcard
            _ = r' ^ k := by rw [hr'def, mul_pow]; ring
      _ ≤ r' ^ s / (1 - r') := geom_shell_tail_le hr'_nonneg hr' s n
  -- assemble.
  calc (∑ σ ∈ Bad, pweight p σ)
      ≤ ∑ σ ∈ Bad, r ^ (pathLen cs w F σ (xσ σ)) * pweight p (descentSat cs w F σ (xσ σ)) := step1
    _ = ∑ q ∈ Bad.image g, r ^ (q.2.flatten.length) * pweight p q.1 := step2
    _ ≤ (∑ L ∈ Labs, r ^ (L.flatten.length)) * ∑ ρ ∈ extBox τ, pweight p ρ := step3
    _ ≤ r' ^ s / (1 - r') * ∑ ρ ∈ extBox τ, pweight p ρ := by
        apply mul_le_mul_of_nonneg_right step4
        exact Finset.sum_nonneg (fun ρ _ => pweight_nonneg hp0 (by linarith) ρ)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descent_switching_prob_findep
