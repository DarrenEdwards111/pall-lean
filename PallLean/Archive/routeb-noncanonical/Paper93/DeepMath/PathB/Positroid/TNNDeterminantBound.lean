import PallLean.Paper93.DeepMath.PathB.Positroid.TNNMatrixDef
import PallLean.Paper93.DeepMath.PathB.Positroid.PluckerAbstract

/-!
# Determinant bound for principal-TNN matrices

For any square matrix `A`, the determinant `A.det` equals the principal
minor at `Finset.univ`. Combined with the principal-TNN / principal-TP
hypotheses, this yields:

* `principalTNN_det_eq_principalMinor_univ` — `A.det = principalMinor A
  Finset.univ` for any matrix `A`;
* `IsPrincipalTNN.det_nonneg` — `0 ≤ A.det` for any principal-TNN matrix;
* `IsPrincipalTP.det_pos` — `0 < A.det` for any principal-TP matrix;
* `identity_det_nonneg` — `0 ≤ (1 : Matrix _ _ ℝ).det`, a kernel-only
  sanity check.

The file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- For any square matrix `A`, the determinant equals the principal minor at
    `Finset.univ`. -/
theorem principalTNN_det_eq_principalMinor_univ {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    A.det = principalMinor A Finset.univ :=
  (principalMinor_univ A).symm

/-- For a principal-TNN matrix, `det A ≥ 0`. -/
theorem IsPrincipalTNN.det_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsPrincipalTNN A) : 0 ≤ A.det := by
  rw [principalTNN_det_eq_principalMinor_univ A]
  exact hA Finset.univ

/-- For a principal-TP matrix, `det A > 0`. -/
theorem IsPrincipalTP.det_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsPrincipalTP A) : 0 < A.det := by
  rw [principalTNN_det_eq_principalMinor_univ A]
  exact hA Finset.univ

/-- For the identity matrix, `det = 1 ≥ 0` (kernel-only check). -/
theorem identity_det_nonneg (n : ℕ) :
    0 ≤ (1 : Matrix (Fin n) (Fin n) ℝ).det := by
  rw [Matrix.det_one]
  norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid
