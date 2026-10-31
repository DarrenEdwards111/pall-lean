import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingProb
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PWeightExtends

/-!
# AC⁰ reduction, foundation 32: the SCALED conditional switching bound (branch only)

The piece that makes the multi-round loop's budget *uniform*.  Brick 23's conditional existence used the
*unconditional* cap, whose budget `#gates·cap < ((1-p)/2)^(n-stars τ)` shrinks exponentially each round and
cannot iterate.  The fix: scale the cap by the conditioning mass.  The switching injection
(`descent_switching_prob`, brick 59) sends a deep `σ` to `(descentSat σ, code)`; since `descentSat σ`
*extends* `σ`, if `σ` extends `τ` then so does its boundary, so the boundary sum is bounded by the mass of
the extension box (brick 22) rather than the whole space.  This gives

  `∑_{σ ∈ Bad, σ extends τ} pweight σ ≤ cap · ((1-p)/2)^(n - stars τ)`,

i.e. the *conditional probability* of a deep gate is `≤ cap` — uniform in `τ`.  Dividing the union bound by
the conditioning mass then makes each round's budget the round-independent `#gates · cap < 1`.

* `descent_switching_prob_extends` — the scaled weighted-sum bound (boundary sum over `extBox τ`).
* `descent_switching_le_extends` — `∑_{Bad ⊆ extBox τ} pweight ≤ cap · ((1-p)/2)^(n - stars τ)`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The scaled conditional switching bound.**  For `Bad` restrictions all extending `τ`, the deep-weight
is at most `(2p/(1-p))^s · |Labels|` times the conditioning mass `∑_{ρ extends τ} pweight ρ`. -/
theorem descent_switching_prob_extends {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    (cs : List (Clause n)) (hcons : ∀ T ∈ cs, Consistent T)
    (hnd : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup) (w : ℕ) (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    (F s : ℕ) (τ : Fin n → Option Bool) {Bad : Finset (Fin n → Option Bool)}
    (hext : ∀ σ ∈ Bad, Extends τ σ)
    (hBad : ∀ σ ∈ Bad, s ≤ (canonicalDTree cs w F σ).depth) :
    (∑ σ ∈ Bad, pweight p σ)
      ≤ (2 * p / (1 - p)) ^ s
        * ((Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ)
            * ∑ ρ ∈ extBox τ, pweight p ρ) := by
  classical
  have hp1 : (0 : ℚ) < 1 - p := by linarith
  have hr_nonneg : 0 ≤ (2 * p / (1 - p)) ^ s :=
    pow_nonneg (div_nonneg (by linarith) (by linarith)) s
  set xσ : (Fin n → Option Bool) → (Fin n → Bool) :=
    fun σ => Classical.choose (exists_deep_input cs w hnd F σ) with hxσ
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
          * ∑ ρ ∈ extBox τ, pweight p ρ := by
    have heq1 : (∑ σ ∈ Bad, pweight p (descentSat cs w F σ (xσ σ)))
        = ∑ q ∈ Bad.image g, pweight p q.1 := by
      rw [Finset.sum_image hginj]
    rw [heq1]
    calc (∑ q ∈ Bad.image g, pweight p q.1)
        ≤ ∑ q ∈ (extBox τ) ×ˢ (Finset.univ : Finset (Fin F → Option (Fin w → Option (Option Bool)))),
            pweight p q.1 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro q hq
            rw [Finset.mem_image] at hq
            obtain ⟨σ, hσ, rfl⟩ := hq
            rw [Finset.mem_product]
            refine ⟨?_, Finset.mem_univ _⟩
            show descentSat cs w F σ (xσ σ) ∈ extBox τ
            rw [mem_extBox]
            exact Extends_trans (hext σ hσ) (descentSat_extends cs w F σ (xσ σ))
          · exact fun q _ _ => pweight_nonneg hp0 (by linarith) q.1
      _ = (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ)
            * ∑ ρ ∈ extBox τ, pweight p ρ := by
          rw [Finset.sum_product]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [← Finset.mul_sum]
  calc (∑ σ ∈ Bad, pweight p σ)
      ≤ (2 * p / (1 - p)) ^ s * ∑ σ ∈ Bad, pweight p (descentSat cs w F σ (xσ σ)) := step12
    _ ≤ (2 * p / (1 - p)) ^ s
          * ((Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ)
              * ∑ ρ ∈ extBox τ, pweight p ρ) :=
        mul_le_mul_of_nonneg_left step3 hr_nonneg

/-- **The scaled conditional switching lemma.**  For `Bad` restrictions extending `τ` and all deep, the
conditional deep-weight is at most `cap · ((1-p)/2)^(n - stars τ)` — i.e. the deep *probability* is `≤ cap`,
independent of `τ`. -/
theorem descent_switching_le_extends {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    (cs : List (Clause n)) (hcons : ∀ T ∈ cs, Consistent T)
    (hnd : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup) (w : ℕ) (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    (F s : ℕ) (τ : Fin n → Option Bool) {Bad : Finset (Fin n → Option Bool)}
    (hext : ∀ σ ∈ Bad, Extends τ σ)
    (hBad : ∀ σ ∈ Bad, s ≤ (canonicalDTree cs w F σ).depth) :
    (∑ σ ∈ Bad, pweight p σ)
      ≤ (2 * p / (1 - p)) ^ s
          * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ)
        * ((1 - p) / 2) ^ (n - stars τ) := by
  have h := descent_switching_prob_extends hp0 hp3 cs hcons hnd w hw F s τ hext hBad
  rw [pweight_sum_extends] at h
  linarith [h]

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descent_switching_le_extends
