import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef
import PallLean.Paper93.DeepMath.GraphSpectral.DiagonalMulVec

namespace PallLean.Paper93.DeepMath.GraphSpectral

/-- Laplacian quadratic form expansion:
    `∑ i, φᵢ · (L · φ)ᵢ = ∑ i, (rowSum A)ᵢ · φᵢ² − ∑ i,j, A_ij · φᵢ · φⱼ`. -/
theorem laplacian_quadForm_expand {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ) :
    ∑ i, phi i * ((laplacian A).mulVec phi i) =
      (∑ i, (∑ j, A i j) * phi i * phi i) -
      (∑ i, ∑ j, A i j * phi i * phi j) := by
  -- L · φ = D · φ − A · φ
  -- So vᵀ L φ = ∑ i, φᵢ (Dφ)ᵢ − ∑ i, φᵢ (Aφ)ᵢ
  --          = ∑ i, φᵢ (rowSum A)ᵢ φᵢ − ∑ i, φᵢ ∑ j, Aᵢⱼ φⱼ
  --          = ∑ i, (rowSum A)ᵢ φᵢ² − ∑ i,j, Aᵢⱼ φᵢ φⱼ
  unfold laplacian
  simp only [Matrix.sub_mulVec, Pi.sub_apply, mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intros i _
    rw [Matrix.mulVec_diagonal]
    unfold rowSum
    ring
  · apply Finset.sum_congr rfl
    intros i _
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros j _
    ring

end PallLean.Paper93.DeepMath.GraphSpectral
