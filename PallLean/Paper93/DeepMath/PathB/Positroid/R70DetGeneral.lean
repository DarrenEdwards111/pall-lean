import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetMatrixIdentity
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic.Ring

/-!
# R70 determinant formula for the compiled gadget

This file proves the general closed-form determinant of the Path B compiled
gadget.  The proof uses the existing structural identity
`compiledGadget α n = (α + n) • I - J`, where `J` is the all-ones rank-one
matrix, and Mathlib's characteristic polynomial of a rank-one matrix
`Matrix.charpoly_vecMulVec`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.GadgetRank
open Matrix
open Polynomial

/-- The all-ones rank-one matrix has characteristic polynomial
`X^n - n X^(n-1)` on `Fin n`. -/
theorem allOnes_vecMulVec_charpoly_fin (n : ℕ) :
    (Matrix.vecMulVec (Function.const (Fin n) (1 : ℝ))
        (Function.const (Fin n) (1 : ℝ))).charpoly
      = X ^ n - (n : ℝ) • X ^ (n - 1) := by
  rw [Matrix.charpoly_vecMulVec]
  have hdot :
      Function.const (Fin n) (1 : ℝ) ⬝ᵥ Function.const (Fin n) (1 : ℝ)
        = (n : ℝ) := by
    simp [dotProduct]
  rw [hdot, Fintype.card_fin]

/-- Determinant of `(c I - J_n)`, where `J_n` is the all-ones rank-one matrix. -/
theorem det_scalar_sub_allOnes_vecMulVec_fin (c : ℝ) (n : ℕ) :
    (Matrix.scalar (Fin n) c
        - Matrix.vecMulVec (Function.const (Fin n) (1 : ℝ))
            (Function.const (Fin n) (1 : ℝ))).det
      = c ^ n - (n : ℝ) * c ^ (n - 1) := by
  have hEval := Matrix.eval_charpoly
    (Matrix.vecMulVec (Function.const (Fin n) (1 : ℝ))
      (Function.const (Fin n) (1 : ℝ))) c
  rw [allOnes_vecMulVec_charpoly_fin n] at hEval
  simpa using hEval.symm

/-- **General determinant formula for the compiled gadget.**

For every nonempty dimension `n`, the determinant of the compiled gadget is
`α * (α + n)^(n-1)`.  This is the product of the eigenvalue `α` on the
all-ones line and the eigenvalue `α+n` on the `(n-1)`-dimensional sum-zero
subspace, proved here through the equivalent rank-one characteristic
polynomial of the all-ones matrix. -/
theorem compiledGadget_det_general (α : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (compiledGadget α n).det = α * (α + (n : ℝ)) ^ (n - 1) := by
  let c : ℝ := α + (n : ℝ)
  have hscalar :
      c • (1 : Matrix (Fin n) (Fin n) ℝ) = Matrix.scalar (Fin n) c := by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hdet :
      (c ^ n - (n : ℝ) * c ^ (n - 1))
        = α * (α + (n : ℝ)) ^ (n - 1) := by
    have hpos : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 1) hn
    have hn_pred : n = (n - 1) + 1 := (Nat.succ_pred_eq_of_pos hpos).symm
    have hpow_n : c ^ n = c ^ ((n - 1) + 1) := congrArg (fun k => c ^ k) hn_pred
    calc
      c ^ n - (n : ℝ) * c ^ (n - 1)
          = c ^ ((n - 1) + 1) - (n : ℝ) * c ^ (n - 1) := by
            rw [hpow_n]
      _ = c ^ (n - 1) * c - (n : ℝ) * c ^ (n - 1) := by rw [pow_succ]
      _ = α * (α + (n : ℝ)) ^ (n - 1) := by
        dsimp [c]
        ring
  calc
    (compiledGadget α n).det
        = (c • (1 : Matrix (Fin n) (Fin n) ℝ)
            - Matrix.vecMulVec (Function.const (Fin n) (1 : ℝ))
                (Function.const (Fin n) (1 : ℝ))).det := by
          rw [compiledGadget_matrix_identity α n]
    _ = (Matrix.scalar (Fin n) c
            - Matrix.vecMulVec (Function.const (Fin n) (1 : ℝ))
                (Function.const (Fin n) (1 : ℝ))).det := by
          rw [hscalar]
    _ = c ^ n - (n : ℝ) * c ^ (n - 1) :=
          det_scalar_sub_allOnes_vecMulVec_fin c n
    _ = α * (α + (n : ℝ)) ^ (n - 1) := hdet

end PallLean.Paper93.DeepMath.PathB.Positroid
