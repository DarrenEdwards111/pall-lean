import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef
import PallLean.Paper93.DeepMath.NFrame.ParityPenalty
import PallLean.Paper93.DeepMath.NFrame.Barrier

namespace PallLean.Paper93.DeepMath.NFrame

open PallLean.Paper93.DeepMath.GraphSpectral

/-- The N-Frame Lagrangian `S_NF[Φ; P] = α·Σ(Φ_u − Φ_v)² + β·Σ(1 − χ·sgn Φ)₊ + λ·B(A)`
    (paper §28.3). -/
noncomputable def S_NF {n : ℕ} (α β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ)       -- graph adjacency
    (phi : Fin n → ℝ)                      -- vertex values Φ
    (chi : Fin n → ℝ)                      -- Tseitin charges χ
    (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=  -- gadget matrix A
  α * (∑ i, phi i * ((laplacian adj).mulVec phi i))
    + β * parityPenalty chi phi
    + lam * barrier A

/-- The α-term alone. -/
def S_NF_alpha {n : ℕ} (α : ℝ) (adj : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ) : ℝ :=
  α * (∑ i, phi i * ((laplacian adj).mulVec phi i))

/-- The β-term alone. -/
noncomputable def S_NF_beta {n : ℕ} (β : ℝ) (chi phi : Fin n → ℝ) : ℝ :=
  β * parityPenalty chi phi

/-- The λ-term alone. -/
noncomputable def S_NF_lambda {n : ℕ} (lam : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  lam * barrier A

/-- `S_NF` decomposes as the sum of its three terms. -/
theorem S_NF_decompose {n : ℕ} (α β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (phi chi : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    S_NF α β lam adj phi chi A
      = S_NF_alpha α adj phi + S_NF_beta β chi phi + S_NF_lambda lam A := rfl

/-- β-term is nonneg when `β ≥ 0`. -/
theorem S_NF_beta_nonneg {n : ℕ} (β : ℝ) (hβ : 0 ≤ β)
    (chi phi : Fin n → ℝ) :
    0 ≤ S_NF_beta β chi phi :=
  mul_nonneg hβ (parityPenalty_nonneg chi phi)

end PallLean.Paper93.DeepMath.NFrame
