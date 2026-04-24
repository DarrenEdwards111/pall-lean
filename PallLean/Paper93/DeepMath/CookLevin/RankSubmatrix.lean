import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.CookLevin

/-- Submatrix by bijections preserves rank. Wraps Mathlib. -/
theorem rank_submatrix_equiv {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (e₁ : m ≃ m) (e₂ : n ≃ n) :
    (A.submatrix e₁ e₂).rank = A.rank := by
  exact Matrix.rank_submatrix A e₁ e₂

/-- Submatrix by general Equiv to possibly different index type preserves rank. -/
theorem rank_submatrix_of_equiv {m n m' n' : Type*}
    [Fintype m] [Fintype n] [Fintype m'] [Fintype n'] [DecidableEq m] [DecidableEq n]
    [DecidableEq m'] [DecidableEq n']
    (A : Matrix m n ℝ) (e₁ : m' ≃ m) (e₂ : n' ≃ n) :
    (A.submatrix e₁ e₂).rank = A.rank := by
  exact Matrix.rank_submatrix A e₁ e₂

end PallLean.Paper93.DeepMath.CookLevin
