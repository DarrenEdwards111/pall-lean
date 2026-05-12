import PallLean.Paper93.DeepMath.PathB.Positroid.TNNMatrixDef
import PallLean.Paper93.DeepMath.PathB.Positroid.DiagonalNonnegTNN

/-!
# Membership in the TNN Grassmannian via principal-TNN matrices

This file packages the kernel-only definition of a **point in the TNN
Grassmannian** `Gr⁺(n, n)`: a square `n × n` real matrix together with a
proof that it is principal-TNN (cf. `TNNMatrixDef.lean`).

We provide two canonical constructors:

* `TNNGrassmannianPoint.identity` — the identity matrix as a TNN point;
* `TNNGrassmannianPoint.diagonal` — diagonal matrices with non-negative
  diagonal entries as TNN points.

The membership theorems
`identity_in_TNNGrassmannian` and `zero_diag_in_TNNGrassmannian`
show that the identity and the all-zeros diagonal each yield a
well-defined point in `Gr⁺(n, n)`.

All theorems below are checked to depend only on the kernel axioms
`propext`, `Classical.choice`, and `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- A point in the **TNN Grassmannian Gr⁺(n, n)** — a principal-TNN n×n matrix. -/
structure TNNGrassmannianPoint (n : ℕ) where
  matrix : Matrix (Fin n) (Fin n) ℝ
  isTNN : IsPrincipalTNN matrix

/-- The identity defines a TNN Grassmannian point. -/
def TNNGrassmannianPoint.identity (n : ℕ) : TNNGrassmannianPoint n where
  matrix := 1
  isTNN := identity_isPrincipalTNN n

/-- Diagonal matrices with non-negative entries define TNN Grassmannian points. -/
def TNNGrassmannianPoint.diagonal {n : ℕ} (d : Fin n → ℝ) (h : ∀ i, 0 ≤ d i) :
    TNNGrassmannianPoint n where
  matrix := Matrix.diagonal d
  isTNN := diagonal_nonneg_isPrincipalTNN d h

/-- The identity TNN Grassmannian point has identity matrix. -/
theorem TNNGrassmannianPoint.identity_matrix (n : ℕ) :
    (TNNGrassmannianPoint.identity n).matrix = (1 : Matrix (Fin n) (Fin n) ℝ) := rfl

/-- The diagonal TNN Grassmannian point has diagonal matrix. -/
theorem TNNGrassmannianPoint.diagonal_matrix {n : ℕ} (d : Fin n → ℝ) (h : ∀ i, 0 ≤ d i) :
    (TNNGrassmannianPoint.diagonal d h).matrix = Matrix.diagonal d := rfl

/-- The identity is in the TNN Grassmannian (via its identity point). -/
theorem identity_in_TNNGrassmannian (n : ℕ) :
    ∃ p : TNNGrassmannianPoint n, p.matrix = 1 :=
  ⟨TNNGrassmannianPoint.identity n, rfl⟩

/-- The all-zeros diagonal is in the TNN Grassmannian. -/
theorem zero_diag_in_TNNGrassmannian (n : ℕ) :
    ∃ p : TNNGrassmannianPoint n, p.matrix = Matrix.diagonal (fun _ : Fin n => (0 : ℝ)) :=
  ⟨TNNGrassmannianPoint.diagonal (fun _ => 0) (fun _ => le_refl 0), rfl⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
