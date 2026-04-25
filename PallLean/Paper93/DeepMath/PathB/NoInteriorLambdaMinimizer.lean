import PallLean.Paper93.DeepMath.NFrame.BarrierDivergence

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame

/-- For lam > 0, the λ-term `S_NF_lambda lam M = lam * barrier M = -lam * log(det M)`
    diverges to +∞ as `det M → 0⁺`. So no interior PosDef minimizer exists for the λ-term alone
    when minimizing on PosDef × {det M ≥ ε} for ε → 0. -/
theorem S_NF_lambda_diverges_to_infinity (lam : ℝ) (hlam : 0 < lam) (K : ℝ) {n : ℕ} :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Matrix (Fin n) (Fin n) ℝ, 0 < A.det → A.det < δ →
      K < lam * barrier A := by
  obtain ⟨δ, hδ, h⟩ := barrier_unbounded_as_det_to_zero (n := n) (K / lam)
  refine ⟨δ, hδ, ?_⟩
  intros A hpos hlt
  have h_barr : K / lam < barrier A := h A hpos hlt
  have hmul : K / lam * lam < barrier A * lam := mul_lt_mul_of_pos_right h_barr hlam
  have h_div : K / lam * lam = K := by
    field_simp
  rw [h_div] at hmul
  linarith [mul_comm lam (barrier A)]

end PallLean.Paper93.DeepMath.PathB
