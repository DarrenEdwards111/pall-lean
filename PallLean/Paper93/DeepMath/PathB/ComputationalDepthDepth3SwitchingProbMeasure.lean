import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingProbFindep
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RestrictionMeasure

/-!
# The F-independent switching count over an arbitrary `RestrictionMeasure`

The payoff of the measure abstraction (`SCOPE_LAYER3_EXPANDER_RESTRICTIONS.md`): the F-independent
switching count holds for **any** measure satisfying the `RestrictionMeasure` interface — the decoder
(deep-input choice, `descentPosValLabels` injectivity, label count, geometric shell sum) is
**measure-free** and is reused verbatim; the only measure-dependent steps are the per-label weight
ratio (`μ.ratio` = M1) and nonnegativity (`μ.nonneg`).

This is a faithful transcription of `descent_switching_prob_findep` with exactly three swaps:
`pweight p · → μ.toFun ·`, `pweight_le_ratio_pow → μ.ratio`, `pweight_nonneg → μ.nonneg`.  Note the
count keeps `∑_{extBox τ} μ` symbolic — it uses **only `nonneg` + `ratio` (M1)**, not the global mass
`sumExtends` (M2).  So the bound is reproduced *exactly* by any `s`-wise-independent measure (M1
compares restrictions differing on `≤ s` coordinates).

* `descent_switching_prob_measure` — `∑_Bad μ ≤ (r')^s/(1-r') · ∑_{extBox τ} μ`, for any
  `RestrictionMeasure n p`, `r' = (2p/(1-p))(4w+1)`.

`pweight` is the canonical instance, so `descent_switching_prob_findep` is the special case
`μ := pweightMeasure …`.  AC⁰-adjacent; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The F-independent switching count over an arbitrary restriction measure.**  Identical to
`descent_switching_prob_findep` but driven by the abstract interface: the decoder is measure-free, and
the only measure facts used are `μ.ratio` (M1, the bounded-support weight ratio) and `μ.nonneg`.  The
global mass `μ.sumExtends` (M2) is **not** needed — `∑_{extBox τ} μ` stays symbolic. -/
theorem descent_switching_prob_measure {p : ℚ} (μ : RestrictionMeasure n p)
    (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    (cs : List (Clause n)) (hcons : ∀ T ∈ cs, Consistent T)
    (hnd : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup) (w : ℕ) [NeZero w]
    (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    (hr' : (2 * p / (1 - p)) * (4 * w + 1) < 1)
    (F s : ℕ) (τ : Fin n → Option Bool) {Bad : Finset (Fin n → Option Bool)}
    (hext : ∀ σ ∈ Bad, Extends τ σ)
    (hBad : ∀ σ ∈ Bad, s ≤ (canonicalDTree cs w F σ).depth) :
    (∑ σ ∈ Bad, μ.toFun σ)
      ≤ ((2 * p / (1 - p)) * (4 * w + 1)) ^ s / (1 - (2 * p / (1 - p)) * (4 * w + 1))
          * ∑ ρ ∈ extBox τ, μ.toFun ρ := by
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
  have hginj : Set.InjOn g Bad := by
    intro σ1 _ σ2 _ heq
    rw [hg] at heq; simp only [Prod.mk.injEq] at heq
    exact descentPosValLabels_injective cs w hcons hw F σ1 σ2 (xσ σ1) (xσ σ2) heq.1 heq.2
  set Labs : Finset (List (List (Fin w × Bool))) :=
    Bad.image (fun σ => descentPosValLabels cs w F σ (xσ σ)) with hLabs
  have hLabsNe : ∀ L ∈ Labs, ∀ b ∈ L, b ≠ [] := by
    intro L hL b hb
    rw [hLabs, Finset.mem_image] at hL
    obtain ⟨σ, _, rfl⟩ := hL
    exact descentPosValLabels_block_nonempty cs w F σ (xσ σ) b hb
  -- STEP 1: weight gain by the full path length — the ONLY (M1) site.
  have step1 : (∑ σ ∈ Bad, μ.toFun σ)
      ≤ ∑ σ ∈ Bad, r ^ (pathLen cs w F σ (xσ σ)) * μ.toFun (descentSat cs w F σ (xσ σ)) := by
    apply Finset.sum_le_sum
    intro σ _
    have hpl := pathLen_add_stars_descentSat_le cs w hnd F σ (xσ σ)
    exact μ.ratio (stars_descentSat_le cs w F σ (xσ σ)) (by omega)
  -- STEP 2: rewrite as a sum over the (measure-free) injection.
  have step2 : (∑ σ ∈ Bad, r ^ (pathLen cs w F σ (xσ σ)) * μ.toFun (descentSat cs w F σ (xσ σ)))
      = ∑ q ∈ Bad.image g, r ^ (q.2.flatten.length) * μ.toFun q.1 := by
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
  have step3 : (∑ q ∈ Bad.image g, r ^ (q.2.flatten.length) * μ.toFun q.1)
      ≤ (∑ L ∈ Labs, r ^ (L.flatten.length)) * ∑ ρ ∈ extBox τ, μ.toFun ρ := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) ?_
    · intro q _ _
      exact mul_nonneg (pow_nonneg hr_nonneg _) (μ.nonneg q.1)
    · rw [Finset.sum_product]
      apply le_of_eq
      calc (∑ ρ ∈ extBox τ, ∑ L ∈ Labs, r ^ (L.flatten.length) * μ.toFun ρ)
          = ∑ ρ ∈ extBox τ, (∑ L ∈ Labs, r ^ (L.flatten.length)) * μ.toFun ρ := by
            apply Finset.sum_congr rfl; intro ρ _; rw [Finset.sum_mul]
        _ = (∑ L ∈ Labs, r ^ (L.flatten.length)) * ∑ ρ ∈ extBox τ, μ.toFun ρ := by
            rw [← Finset.mul_sum]
  -- STEP 4: the label geometric sum (measure-free).
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
    calc (∑ k ∈ Finset.Icc s n,
            ∑ L ∈ Labs.filter (fun L => L.flatten.length = k), r ^ (L.flatten.length))
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
  calc (∑ σ ∈ Bad, μ.toFun σ)
      ≤ ∑ σ ∈ Bad, r ^ (pathLen cs w F σ (xσ σ)) * μ.toFun (descentSat cs w F σ (xσ σ)) := step1
    _ = ∑ q ∈ Bad.image g, r ^ (q.2.flatten.length) * μ.toFun q.1 := step2
    _ ≤ (∑ L ∈ Labs, r ^ (L.flatten.length)) * ∑ ρ ∈ extBox τ, μ.toFun ρ := step3
    _ ≤ r' ^ s / (1 - r') * ∑ ρ ∈ extBox τ, μ.toFun ρ := by
        apply mul_le_mul_of_nonneg_right step4
        exact Finset.sum_nonneg (fun ρ _ => μ.nonneg ρ)

/-- **The global (τ = ∅) F-independent count over an arbitrary measure.**  The abstract analog of
`descent_switching_findep_le`: at the empty base the extension-box mass is `1` — here is the *only*
place `μ.sumExtends` (M2) is used (where a `k`-wise/expander concentration substitute would enter). -/
theorem descent_switching_findep_le_measure {p : ℚ} (μ : RestrictionMeasure n p)
    (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    (cs : List (Clause n)) (hcons : ∀ T ∈ cs, Consistent T)
    (hnd : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup) (w : ℕ) [NeZero w]
    (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    (hr' : (2 * p / (1 - p)) * (4 * w + 1) < 1)
    (F s : ℕ) {Bad : Finset (Fin n → Option Bool)}
    (hBad : ∀ σ ∈ Bad, s ≤ (canonicalDTree cs w F σ).depth) :
    (∑ σ ∈ Bad, μ.toFun σ)
      ≤ ((2 * p / (1 - p)) * (4 * w + 1)) ^ s / (1 - (2 * p / (1 - p)) * (4 * w + 1)) := by
  have h := descent_switching_prob_measure μ hp0 hp3 cs hcons hnd w hw hr' F s
    (fun _ : Fin n => none) (fun σ _ v b hb => by simp at hb) hBad
  have hbox : (∑ ρ ∈ extBox (fun _ : Fin n => none), μ.toFun ρ) = 1 := by
    rw [μ.sumExtends (fun _ : Fin n => none)]
    have hstars0 : stars (fun _ : Fin n => (none : Option Bool)) = n := by rw [stars, freeVars]; simp
    rw [hstars0, Nat.sub_self, pow_zero]
  rwa [hbox, mul_one] at h

/-- **The abstraction is load-bearing, not merely declared:** the original `descent_switching_prob_findep`
is recovered as the `pweightMeasure` instance.  `simp` rewrites `(pweightMeasure …).toFun → pweight p`. -/
theorem descent_switching_prob_findep_via_measure {p : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp3 : 3 * p ≤ 1)
    (cs : List (Clause n)) (hcons : ∀ T ∈ cs, Consistent T)
    (hnd : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup) (w : ℕ) [NeZero w]
    (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    (hr' : (2 * p / (1 - p)) * (4 * w + 1) < 1)
    (F s : ℕ) (τ : Fin n → Option Bool) {Bad : Finset (Fin n → Option Bool)}
    (hext : ∀ σ ∈ Bad, Extends τ σ)
    (hBad : ∀ σ ∈ Bad, s ≤ (canonicalDTree cs w F σ).depth) :
    (∑ σ ∈ Bad, pweight p σ)
      ≤ ((2 * p / (1 - p)) * (4 * w + 1)) ^ s / (1 - (2 * p / (1 - p)) * (4 * w + 1))
          * ∑ ρ ∈ extBox τ, pweight p ρ := by
  have h := descent_switching_prob_measure (pweightMeasure hp0 hp1 hp3) hp0 hp3
    cs hcons hnd w hw hr' F s τ hext hBad
  simpa using h

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descent_switching_prob_measure
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descent_switching_findep_le_measure
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descent_switching_prob_findep_via_measure
