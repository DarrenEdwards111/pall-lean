import PallLean.Paper93.DeepMath.NFrame.DetUnitInvariance

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame

/-- For U with `(det U)² = 1` and any A, the determinant `det(Uᵀ · A · U) = det A`. -/
theorem det_preserved_orthogonal {n : ℕ} (U A : Matrix (Fin n) (Fin n) ℝ)
    (hU : U.det^2 = 1) :
    (U.transpose * A * U).det = A.det :=
  det_conj_invariant_of_unit_det_sq U A hU

/-- Specifically: if det A = 1, then det(Uᵀ · A · U) = 1 for U orthogonal. -/
theorem det_one_preserved_orthogonal {n : ℕ} (U A : Matrix (Fin n) (Fin n) ℝ)
    (hU : U.det^2 = 1) (hA : A.det = 1) :
    (U.transpose * A * U).det = 1 := by
  rw [det_preserved_orthogonal U A hU, hA]

end PallLean.Paper93.DeepMath.PathB
