import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.RCLike.Basic

/-!
# Rank bounds by number of rows and columns (N-Frame)

For a real matrix `A : Matrix (Fin m) (Fin n) ℝ`, its Mathlib rank
`Matrix.rank` is bounded above by both the number of rows `m` and the
number of columns `n`. These are direct specialisations of the
Mathlib lemmas `Matrix.rank_le_card_height` and
`Matrix.rank_le_card_width`, applied with the fintype cardinal of
`Fin m` / `Fin n` simplified via `Fintype.card_fin`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- Matrix rank is at most the number of rows. -/
theorem rank_le_card_rows {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    A.rank ≤ m := by
  have := Matrix.rank_le_card_height A
  simpa [Fintype.card_fin] using this

/-- Matrix rank is at most the number of columns. -/
theorem rank_le_card_cols {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    A.rank ≤ n := by
  have := Matrix.rank_le_card_width A
  simpa [Fintype.card_fin] using this

end PallLean.Paper93.DeepMath.NFrame
