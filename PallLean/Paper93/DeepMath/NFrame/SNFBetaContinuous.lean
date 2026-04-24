import PallLean.Paper93.DeepMath.NFrame.ParityTermContinuous
import PallLean.Paper93.DeepMath.NFrame.SNF

namespace PallLean.Paper93.DeepMath.NFrame

/-- `parityPenalty chi ·` is continuous at any Φ with no zero entries. -/
theorem parityPenalty_continuousAt_no_zero {n : ℕ} (chi : Fin n → ℝ)
    (phi : Fin n → ℝ) (h : ∀ i, phi i ≠ 0) :
    ContinuousAt (fun p : Fin n → ℝ => parityPenalty chi p) phi := by
  unfold parityPenalty
  -- `ContinuousAt` is `Tendsto` in the neighbourhood filter, so we reduce to
  -- the finset version of `tendsto_finset_sum`.
  refine tendsto_finset_sum (Finset.univ : Finset (Fin n)) (fun i _ => ?_)
  -- Goal after unfolding: `Tendsto (fun p => parityTerm (chi i) (p i)) (𝓝 phi) (𝓝 (parityTerm (chi i) (phi i)))`.
  change ContinuousAt (fun p : Fin n → ℝ => parityTerm (chi i) (p i)) phi
  have hTerm : ContinuousAt (fun y : ℝ => parityTerm (chi i) y) (phi i) :=
    parityTerm_continuousAt_ne_zero (chi i) (phi i) (h i)
  -- Compose with the coordinate projection `fun p => p i`, which is continuous.
  exact ContinuousAt.comp (f := fun p : Fin n → ℝ => p i)
    (g := fun y : ℝ => parityTerm (chi i) y) hTerm ((continuous_apply i).continuousAt)

/-- The β-term of S_NF is continuous at any Φ with no zero entries. -/
theorem S_NF_beta_continuousAt_no_zero {n : ℕ} (β : ℝ) (chi : Fin n → ℝ)
    (phi : Fin n → ℝ) (h : ∀ i, phi i ≠ 0) :
    ContinuousAt (fun p : Fin n → ℝ => S_NF_beta β chi p) phi := by
  unfold S_NF_beta
  exact continuousAt_const.mul (parityPenalty_continuousAt_no_zero chi phi h)

end PallLean.Paper93.DeepMath.NFrame
