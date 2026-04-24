import PallLean.Paper93.DeepMath.NFrame.Barrier
import PallLean.Paper93.DeepMath.NFrame.DetMulWrapper

namespace PallLean.Paper93.DeepMath.NFrame

/-- For invertible `U` with `det U * det U = 1` (unitary/orthogonal real),
    `barrier (Uᵀ * A * U) = barrier A`. -/
theorem barrier_conj_unit_det {n : ℕ} (U A : Matrix (Fin n) (Fin n) ℝ)
    (hU : U.det * U.det = 1) (hA : A.det ≠ 0) :
    barrier (U.transpose * A * U) = barrier A := by
  -- We use the multiplicativity of determinant and the identity
  -- `(det U)² = 1` to conclude `det(Uᵀ A U) = det A`, hence equal logs.
  -- The hypothesis `hA` is retained as part of the API (the orthogonal
  -- invariance is mathematically meaningful only when `A` is invertible);
  -- it is not needed inside the algebraic computation.
  have _hA := hA
  unfold barrier
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  -- Goal: -Real.log (U.det * A.det * U.det) = -Real.log A.det
  have h_eq : U.det * A.det * U.det = A.det := by
    have hcomm : U.det * A.det * U.det = U.det * U.det * A.det := by ring
    rw [hcomm, hU, one_mul]
  rw [h_eq]

end PallLean.Paper93.DeepMath.NFrame
