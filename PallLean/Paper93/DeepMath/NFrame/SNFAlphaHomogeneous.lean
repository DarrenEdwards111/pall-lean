import PallLean.Paper93.DeepMath.NFrame.SNFAlphaNonneg

namespace PallLean.Paper93.DeepMath.NFrame

open PallLean.Paper93.DeepMath.GraphSpectral

/-- The α-term is homogeneous of degree 2 in Φ: `S_NF_alpha α A (c • Φ) = c² · S_NF_alpha α A Φ`. -/
theorem S_NF_alpha_homogeneous_two {n : ℕ} (α c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (phi : Fin n → ℝ) :
    S_NF_alpha α A (c • phi) = c^2 * S_NF_alpha α A phi := by
  unfold S_NF_alpha
  rw [Matrix.mulVec_smul]
  have hsum : (∑ i, (c • phi) i * (c • (laplacian A).mulVec phi) i)
       = c^2 * ∑ i, phi i * ((laplacian A).mulVec phi) i := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros i _
    ring
  rw [hsum]
  ring

end PallLean.Paper93.DeepMath.NFrame
