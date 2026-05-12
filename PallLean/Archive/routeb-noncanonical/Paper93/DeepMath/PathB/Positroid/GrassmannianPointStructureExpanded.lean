import PallLean.Paper93.DeepMath.PathB.Positroid.TNNGrassmannianMembership
import PallLean.Paper93.DeepMath.PathB.Positroid.DiagonalNonnegTNN

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- For each n ≥ 1, the identity matrix is in the TNN Grassmannian. -/
theorem identity_in_TNN_Grassmannian_general (n : ℕ) :
    ∃ p : TNNGrassmannianPoint n, p.matrix = (1 : Matrix (Fin n) (Fin n) ℝ) :=
  identity_in_TNNGrassmannian n

/-- The all-zero diagonal is in the TNN Grassmannian. -/
theorem zero_diag_in_TNN_general (n : ℕ) :
    ∃ p : TNNGrassmannianPoint n, p.matrix = Matrix.diagonal (fun _ : Fin n => (0 : ℝ)) :=
  zero_diag_in_TNNGrassmannian n

/-- Existence of multiple TNN Grassmannian points (identity, zero-diag). -/
theorem multiple_TNN_points (n : ℕ) :
    (∃ p : TNNGrassmannianPoint n, p.matrix = (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
    (∃ p : TNNGrassmannianPoint n, p.matrix = Matrix.diagonal (fun _ : Fin n => (0 : ℝ))) :=
  ⟨identity_in_TNNGrassmannian n, zero_diag_in_TNNGrassmannian n⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
