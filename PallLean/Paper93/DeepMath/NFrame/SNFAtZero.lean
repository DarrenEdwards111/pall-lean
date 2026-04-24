import PallLean.Paper93.DeepMath.NFrame.SNF

namespace PallLean.Paper93.DeepMath.NFrame

/-- At Φ = 0, the α-term of S_NF vanishes. -/
theorem S_NF_alpha_zero {n : ℕ} (α : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    S_NF_alpha α A (0 : Fin n → ℝ) = 0 := by
  unfold S_NF_alpha
  simp [Matrix.mulVec_zero, Finset.sum_const_zero, mul_zero]

/-- `Real.sign 0 = 0`. -/
theorem parityTerm_at_zero (chi_v : ℝ) : parityTerm chi_v 0 = 1 := by
  unfold parityTerm
  rw [Real.sign_zero, mul_zero, sub_zero, max_eq_right zero_le_one]

/-- At Φ = 0, the β-term equals `β · n` (counting all vertices). -/
theorem S_NF_beta_zero {n : ℕ} (β : ℝ) (chi : Fin n → ℝ) :
    S_NF_beta β chi (0 : Fin n → ℝ) = β * n := by
  unfold S_NF_beta parityPenalty
  simp only [Pi.zero_apply]
  have hterm : ∀ i : Fin n, parityTerm (chi i) (0 : ℝ) = 1 :=
    fun i => parityTerm_at_zero (chi i)
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

end PallLean.Paper93.DeepMath.NFrame
