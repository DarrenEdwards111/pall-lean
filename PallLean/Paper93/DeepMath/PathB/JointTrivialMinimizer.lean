import PallLean.Paper93.DeepMath.NFrame.SNFAtOrigin
import PallLean.Paper93.DeepMath.NFrame.SNF

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame

/-- At (Φ = 0, A = I), the S_NF Lagrangian equals β · n. (Sanity check value.) -/
theorem S_NF_at_zero_identity {n : ℕ} (α β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (chi : Fin n → ℝ) :
    S_NF α β lam adj (0 : Fin n → ℝ) chi (1 : Matrix (Fin n) (Fin n) ℝ) = β * n :=
  S_NF_at_origin_identity α β lam adj chi

/-- Special case: for α = β = lam = 0, S_NF at (0, I) equals 0 — the trivial minimum. -/
theorem S_NF_zero_at_zero_identity {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℝ) (chi : Fin n → ℝ) :
    S_NF 0 0 0 adj (0 : Fin n → ℝ) chi (1 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  rw [S_NF_at_zero_identity 0 0 0 adj chi]
  ring

end PallLean.Paper93.DeepMath.PathB
