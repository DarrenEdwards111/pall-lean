import PallLean.Paper93.DeepMath.PathB.Positroid.DiagonalNonnegTNN
import PallLean.Paper93.DeepMath.PathB.Positroid.TNNStratumDef

/-!
# Diagonal positive matrices as TNN strata

A diagonal matrix `D = Matrix.diagonal d` with all entries `d i > 0` strictly
positive forms a TNN stratum with full support: every principal submatrix has
strictly positive determinant (since it is itself diagonal with positive
entries), and in particular non-negative determinant on the entire support
`Finset.univ`.

This file constructs such strata and records their basic identification
lemmas (matrix, support, identity case).

This file is **kernel-only**: no `sorry`, no custom `axiom`, only the
kernel axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- A diagonal matrix with all positive entries forms a TNN stratum with full support. -/
def diagonalPositiveTNNStratum {n : ℕ} (d : Fin n → ℝ) (h : ∀ i, 0 < d i) :
    TNNStratum n where
  matrix := Matrix.diagonal d
  is_TNN := diagonal_nonneg_isPrincipalTNN d (fun i => le_of_lt (h i))
  support := Finset.univ
  positivity := fun J _ =>
    diagonal_nonneg_isPrincipalTNN d (fun i => le_of_lt (h i)) J

/-- The diagonal positive TNN stratum has the diagonal as its matrix. -/
theorem diagonalPositiveTNNStratum_matrix {n : ℕ} (d : Fin n → ℝ) (h : ∀ i, 0 < d i) :
    (diagonalPositiveTNNStratum d h).matrix = Matrix.diagonal d := rfl

/-- The diagonal positive TNN stratum has full support. -/
theorem diagonalPositiveTNNStratum_support {n : ℕ} (d : Fin n → ℝ) (h : ∀ i, 0 < d i) :
    (diagonalPositiveTNNStratum d h).support = Finset.univ := rfl

/-- The diagonal positive TNN stratum at all-ones is well-defined: the identity. -/
theorem diagonalPositiveTNNStratum_ones (n : ℕ) :
    (diagonalPositiveTNNStratum (fun _ : Fin n => (1 : ℝ)) (fun _ => one_pos)).matrix =
      Matrix.diagonal (fun _ : Fin n => (1 : ℝ)) := rfl

end PallLean.Paper93.DeepMath.PathB.Positroid
