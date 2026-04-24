import PallLean.Paper93.DeepMath.NFrame.SNFAlphaNonneg

namespace PallLean.Paper93.DeepMath.NFrame

open PallLean.Paper93.DeepMath.GraphSpectral

/-- α-term is symmetric under negation of Φ: `S_NF_alpha α A (-Φ) = S_NF_alpha α A Φ`.
    (Since it's a quadratic form.) -/
theorem S_NF_alpha_neg_phi {n : ℕ} (α : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (phi : Fin n → ℝ) :
    S_NF_alpha α A (-phi) = S_NF_alpha α A phi := by
  unfold S_NF_alpha
  have hneg : (-phi) = ((-1 : ℝ)) • phi := by
    funext i; simp
  rw [hneg, Matrix.mulVec_smul]
  have hsum : (∑ i, ((-1 : ℝ) • phi) i * ((-1 : ℝ) • (laplacian A).mulVec phi) i)
       = ∑ i, phi i * ((laplacian A).mulVec phi) i := by
    simp only [Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intros i _
    ring
  rw [hsum]

end PallLean.Paper93.DeepMath.NFrame
