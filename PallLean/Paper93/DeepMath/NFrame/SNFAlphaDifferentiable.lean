import PallLean.Paper93.DeepMath.NFrame.SNF

namespace PallLean.Paper93.DeepMath.NFrame

open PallLean.Paper93.DeepMath.GraphSpectral

/-- The α-term of S_NF is Fréchet differentiable everywhere in Φ
    (it's a quadratic form, hence polynomial, hence smooth). -/
theorem S_NF_alpha_differentiable {n : ℕ} (α : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Differentiable ℝ (fun phi : Fin n → ℝ => S_NF_alpha α A phi) := by
  unfold S_NF_alpha
  apply Differentiable.const_mul
  apply Differentiable.fun_sum
  intros i _
  -- phi ↦ phi i * ((laplacian A).mulVec phi) i is a quadratic in phi
  apply Differentiable.mul
  · exact differentiable_apply i
  · -- phi ↦ ((laplacian A).mulVec phi) i = ∑ j, (laplacian A) i j * phi j, linear in phi
    show Differentiable ℝ (fun phi => ((laplacian A).mulVec phi) i)
    simp only [Matrix.mulVec, dotProduct]
    apply Differentiable.fun_sum
    intros j _
    exact (differentiable_apply j).const_mul _

end PallLean.Paper93.DeepMath.NFrame
