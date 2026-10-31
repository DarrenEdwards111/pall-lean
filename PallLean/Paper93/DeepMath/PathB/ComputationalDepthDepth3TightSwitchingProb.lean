import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestWeightGain
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Reconstruction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPathLabel

/-!
# Tight switching, step 2: the tight p-biased switching bound (branch `razborov-recoverRho-wip`)

The label half + assembly: the **tight `(2w)^s` p-biased switching bound** over the `canonicalDT`
reconstruction.  The cardinality bound `fullpath_switching_count` (`|Bad| ≤ |Short|·(2w)^s`) is upgraded to
a *weighted* bound by replaying its injection `σ ↦ (deepestEnd σ, lab σ)` against the p-biased weight
(exactly `descent_switching_prob`'s boundary-sum argument, but with the tight `(2w)^s` label space
`PathLabel w s` instead of the crude `(4^w+1)^F` code space).  Combined with the `deepestEnd` weight gain
(step 1, brick: `pweight_le_ratio_pow_deepestEnd`):

* `deepest_switching_weighted_of_reconstruction` — `∑_{Bad} pweight (deepestEnd σ) ≤ (2w)^s · ∑_{Short} pweight`.
* `tight_descent_switching_prob` — `∑_{Bad} pweight σ ≤ (2p/(1-p))^s · (2w)^s · ∑_{Short} pweight`, for
  `Bad ⊆ {canonicalDT-depth ≥ s}` with the deepest-branch reconstruction holding.

This is the tight p-biased switching bound the depth-3 fix needs: it replaces the crude `(4^w+1)^F` cap by
`(2w)^s` (tied to tree *depth*, not fuel), so the budget `#gates·cap < 1` becomes `s ≳ log #gates`
(F-independent) and satisfiable.  `ReconstructionCorrect` is dischargeable by the sorry-free
`reconstructionCorrect_fullpath`.  The remaining reconciliation is `canonicalDT` (this bound) ↔
`canonicalDTree` (the collapse arc's tree).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The label half (weighted).**  Replaying the reconstruction injection
`σ ↦ (deepestEnd σ, lab σ)` against the p-biased weight: the deepest-end weight over `Bad` is at most
`(2w)^s` times the weight over `Short`. -/
theorem deepest_switching_weighted_of_reconstruction {p : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {w s F : ℕ} {cs : List (Clause n)} {Bad Short : Finset (Restriction n)}
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short)
    (hrec : ReconstructionCorrect cs w s F Bad) :
    (∑ σ ∈ Bad, pweight p (deepestEnd cs F σ))
      ≤ (((2 * w) ^ s : ℕ) : ℚ) * ∑ τ ∈ Short, pweight p τ := by
  classical
  obtain ⟨lab, D, hdec⟩ := hrec
  set g : Restriction n → (Restriction n × PathLabel w s) :=
    fun σ => (deepestEnd cs F σ, lab σ) with hg
  have hginj : Set.InjOn g Bad := by
    intro ρ hρ σ hσ heq
    simp only [hg, Prod.mk.injEq] at heq
    obtain ⟨hE, hlab⟩ := heq
    have h1 : D (deepestEnd cs F ρ) (lab ρ) = D (deepestEnd cs F σ) (lab σ) := by rw [hE, hlab]
    rw [hdec ρ hρ, hdec σ hσ] at h1
    exact deepestEnd_inj cs F hE h1
  have heq1 : (∑ σ ∈ Bad, pweight p (deepestEnd cs F σ)) = ∑ q ∈ Bad.image g, pweight p q.1 := by
    rw [Finset.sum_image hginj]
  rw [heq1]
  calc (∑ q ∈ Bad.image g, pweight p q.1)
      ≤ ∑ q ∈ Short ×ˢ (Finset.univ : Finset (PathLabel w s)), pweight p q.1 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          rw [Finset.mem_image] at hq
          obtain ⟨σ, hσ, rfl⟩ := hq
          rw [Finset.mem_product]
          exact ⟨hmem σ hσ, Finset.mem_univ _⟩
        · exact fun q _ _ => pweight_nonneg hp0 hp1 q.1
    _ = (((2 * w) ^ s : ℕ) : ℚ) * ∑ τ ∈ Short, pweight p τ := by
        rw [Finset.sum_product]
        have hcard : (Finset.univ : Finset (PathLabel w s)).card = (2 * w) ^ s := by
          rw [Finset.card_univ, card_pathLabels]
        simp only [Finset.sum_const, hcard, nsmul_eq_mul]
        rw [← Finset.mul_sum]

/-- **The tight p-biased switching bound.**  For `Bad` of canonical-tree depth `≥ s` whose deepest ends
land in `Short`, and with the deepest-branch reconstruction holding, the p-biased weight of `Bad` is at
most `(2p/(1-p))^s · (2w)^s` times the weight of `Short` — the tight cap, tied to depth not fuel. -/
theorem tight_descent_switching_prob {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w s F : ℕ} {cs : List (Clause n)} {Bad Short : Finset (Restriction n)}
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short)
    (hdepth : ∀ ρ ∈ Bad, s ≤ (canonicalDT cs F ρ).depth)
    (hrec : ReconstructionCorrect cs w s F Bad) :
    (∑ σ ∈ Bad, pweight p σ)
      ≤ (2 * p / (1 - p)) ^ s * (((2 * w) ^ s : ℕ) : ℚ) * ∑ τ ∈ Short, pweight p τ := by
  have hp1 : p ≤ 1 := by linarith
  have hr_nonneg : 0 ≤ (2 * p / (1 - p)) ^ s := by
    have : (0 : ℚ) < 1 - p := by linarith
    positivity
  calc (∑ σ ∈ Bad, pweight p σ)
      ≤ ∑ σ ∈ Bad, (2 * p / (1 - p)) ^ s * pweight p (deepestEnd cs F σ) := by
        apply Finset.sum_le_sum
        intro σ hσ
        exact pweight_le_ratio_pow_deepestEnd hp0 hp3 cs F s σ (hdepth σ hσ)
    _ = (2 * p / (1 - p)) ^ s * ∑ σ ∈ Bad, pweight p (deepestEnd cs F σ) := by rw [Finset.mul_sum]
    _ ≤ (2 * p / (1 - p)) ^ s * ((((2 * w) ^ s : ℕ) : ℚ) * ∑ τ ∈ Short, pweight p τ) := by
        apply mul_le_mul_of_nonneg_left _ hr_nonneg
        exact deepest_switching_weighted_of_reconstruction hp0 hp1 hmem hrec
    _ = (2 * p / (1 - p)) ^ s * (((2 * w) ^ s : ℕ) : ℚ) * ∑ τ ∈ Short, pweight p τ := by ring

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepest_switching_weighted_of_reconstruction
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.tight_descent_switching_prob
