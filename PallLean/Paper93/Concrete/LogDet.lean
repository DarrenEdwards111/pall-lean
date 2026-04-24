/-
  PallLean/Paper93/Concrete/LogDet.lean

  Paper §18's log-determinant barrier: wraps `Matrix.det` + `Real.log`
  using Mathlib's boundary convention `Real.log 0 = 0`.
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace PallLean.Paper93.Concrete

open Matrix Real

/-- log(det M) with boundary convention: log(0) = 0 in Mathlib. -/
noncomputable def matrixLogDet {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.log M.det

theorem matrixLogDet_identity (n : ℕ) : matrixLogDet (1 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  unfold matrixLogDet
  simp [Real.log_one]

theorem matrixLogDet_of_det_one {n} (M : Matrix (Fin n) (Fin n) ℝ) (h : M.det = 1) :
    matrixLogDet M = 0 := by
  unfold matrixLogDet
  rw [h, Real.log_one]

end PallLean.Paper93.Concrete
