import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3WeightGain

/-!
# Block-DT model, foundation 59: branching holography, step 4q — the switching probability bound (branch only)

The capstone: the full p-biased switching bound, summing the brick-54 injection against the weight.  For
`0 ≤ p ≤ 1/3`,

  `∑_{σ : depth ≥ s} pweight σ ≤ (2p/(1-p))^s · |Labels| · ∑_ρ pweight ρ`,

where `|Labels| = Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) = (4^w+1)^F`.  Dividing by
`∑_ρ pweight ρ = 1` gives `Pr_ρ[depth ≥ s] ≤ (2p/(1-p))^s · (4^w+1)^F` — the branching switching lemma over
the p-biased random restriction.

The proof: per-restriction, `pweight σ ≤ (2p/(1-p))^s · pweight (descentSat σ)` (brick 58); then the
injection `σ ↦ (descentSat σ, codeEnc (codesList σ))` (bricks 53–54) reindexes the boundary sum, which is
bounded by `|Labels|` copies of the full sum.

* `descent_switching_prob` — the weighted-sum switching bound.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The p-biased switching bound.**  Over the p-biased random restriction (`0 ≤ p ≤ 1/3`), the total
weight of restrictions whose canonical tree has depth `≥ s` is at most `(2p/(1-p))^s · |Labels|` times the
full weight, with `|Labels| = Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) = (4^w+1)^F`. -/
theorem descent_switching_prob {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    (cs : List (Clause n)) (hcons : ∀ T ∈ cs, Consistent T)
    (hnd : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup) (w : ℕ) (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    (F s : ℕ) {Bad : Finset (Fin n → Option Bool)}
    (hBad : ∀ σ ∈ Bad, s ≤ (canonicalDTree cs w F σ).depth) :
    (∑ σ ∈ Bad, pweight p σ)
      ≤ (2 * p / (1 - p)) ^ s
        * ((Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ)
            * ∑ ρ : Fin n → Option Bool, pweight p ρ) := by
  classical
  have hp1 : (0 : ℚ) < 1 - p := by linarith
  have hr_nonneg : 0 ≤ (2 * p / (1 - p)) ^ s :=
    pow_nonneg (div_nonneg (by linarith) (by linarith)) s
  set xσ : (Fin n → Option Bool) → (Fin n → Bool) :=
    fun σ => Classical.choose (exists_deep_input cs w hnd F σ) with hxσ
  -- per-restriction gain
  have step12 : (∑ σ ∈ Bad, pweight p σ)
      ≤ (2 * p / (1 - p)) ^ s * ∑ σ ∈ Bad, pweight p (descentSat cs w F σ (xσ σ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro σ hσ
    have hx : (canonicalDTree cs w F σ).depth ≤ pathLen cs w F σ (xσ σ) :=
      Classical.choose_spec (exists_deep_input cs w hnd F σ)
    have hpl := pathLen_add_stars_descentSat_le cs w hnd F σ (xσ σ)
    have hsd := hBad σ hσ
    exact pweight_le_ratio_pow hp0 hp3 (stars_descentSat_le cs w F σ (xσ σ)) (by omega)
  -- the boundary sum, via the injection
  set g : (Fin n → Option Bool)
      → ((Fin n → Option Bool) × (Fin F → Option (Fin w → Option (Option Bool)))) :=
    fun σ => (descentSat cs w F σ (xσ σ), codeEnc F w (codesList cs w F σ (xσ σ))) with hg
  have hginj : Set.InjOn g Bad := by
    intro σ1 _ σ2 _ heq
    rw [hg] at heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hsat, hcode⟩ := heq
    have hcodes : codesList cs w F σ1 (xσ σ1) = codesList cs w F σ2 (xσ σ2) :=
      codeEnc_inj (codesList_length_le cs w F σ1 (xσ σ1)) (codesList_length_le cs w F σ2 (xσ σ2))
        (codesList_code_length_le cs w hw F σ1 (xσ σ1))
        (codesList_code_length_le cs w hw F σ2 (xσ σ2)) hcode
    exact descent_code_injective cs hcons w F hsat hcodes
  have step3 : (∑ σ ∈ Bad, pweight p (descentSat cs w F σ (xσ σ)))
      ≤ (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ)
          * ∑ ρ : Fin n → Option Bool, pweight p ρ := by
    have heq1 : (∑ σ ∈ Bad, pweight p (descentSat cs w F σ (xσ σ)))
        = ∑ q ∈ Bad.image g, pweight p q.1 := by
      rw [Finset.sum_image hginj]
    rw [heq1]
    calc (∑ q ∈ Bad.image g, pweight p q.1)
        ≤ ∑ q : (Fin n → Option Bool) × (Fin F → Option (Fin w → Option (Option Bool))),
            pweight p q.1 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun q _ _ => pweight_nonneg hp0 (by linarith) q.1)
      _ = (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ)
            * ∑ ρ : Fin n → Option Bool, pweight p ρ := by
          rw [← Finset.univ_product_univ, Finset.sum_product]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [← Finset.mul_sum]
  calc (∑ σ ∈ Bad, pweight p σ)
      ≤ (2 * p / (1 - p)) ^ s * ∑ σ ∈ Bad, pweight p (descentSat cs w F σ (xσ σ)) := step12
    _ ≤ (2 * p / (1 - p)) ^ s
          * ((Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ)
              * ∑ ρ : Fin n → Option Bool, pweight p ρ) :=
        mul_le_mul_of_nonneg_left step3 hr_nonneg

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descent_switching_prob
