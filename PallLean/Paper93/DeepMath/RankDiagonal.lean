/-
  PallLean/Paper93/DeepMath/RankDiagonal.lean

  A paper-faithful statement about the rank of a diagonal matrix.

  We prove option (a):  `Matrix.diagonal (fun _ : Fin N => (1:ℝ)) = 1`,
  which immediately gives `rank (diagonal (fun _ => 1)) = N` via
  Mathlib's `Matrix.rank_one` and `Fintype.card_fin`.

  This module is self-contained and depends only on Mathlib.  It uses
  `Matrix.diagonal_one` (from `Mathlib.Data.Matrix.Diagonal`) and
  `Matrix.rank_one` (from `Mathlib.LinearAlgebra.Matrix.Rank`).
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

namespace PallLean.Paper93.DeepMath

/-- The all-ones diagonal matrix on `Fin N` over `ℝ` is the identity matrix. -/
theorem diagonal_one_eq_one (N : ℕ) :
    Matrix.diagonal (fun _ : Fin N => (1 : ℝ)) = (1 : Matrix (Fin N) (Fin N) ℝ) :=
  Matrix.diagonal_one

/-- The rank of the all-ones diagonal matrix on `Fin N` over `ℝ` is `N`.

    This combines `diagonal_one_eq_one` with `Matrix.rank_one` and
    `Fintype.card_fin`, giving a clean, paper-faithful statement: the
    identity has full rank `N`. -/
theorem rank_diagonal_one (N : ℕ) :
    (Matrix.diagonal (fun _ : Fin N => (1 : ℝ))).rank = N := by
  rw [diagonal_one_eq_one, Matrix.rank_one]
  exact Fintype.card_fin N

end PallLean.Paper93.DeepMath
