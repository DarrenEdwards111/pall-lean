/-
  PallLean/Paper93/Paper283/SumPaddedInverses.lean

  Paper §28.3 — Real sum of zero-padded principal-minor inverses,
  `Σ_{J ∈ J} (A[J,J])^{-1}`, realised as a full ambient `N × N`
  matrix via the `paddedMinorInverse` construction (Z3).

  This file provides:

    * `realSumPrincipalMinorInverses` : the real (non-stub) RHS of the
      δA Euler–Lagrange condition, summing the zero-padded inverses of
      all principal minors in `minorFamily N`;
    * `realSum_zero_outside_all_J`    : entries at row `i` that lies
      outside every `J ∈ minorFamily N` are zero.
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import PallLean.Paper93.Paper283.MinorFamily
import PallLean.Paper93.Paper283.PaddedMinorInverse

namespace PallLean.Paper93.Paper283

open Matrix
open scoped BigOperators

/-- Real sum of padded principal-minor inverses. -/
noncomputable def realSumPrincipalMinorInverses {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  ∑ J ∈ minorFamily N, paddedMinorInverse A J

theorem realSum_zero_outside_all_J {N} (A : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N)
    (h : ∀ J ∈ minorFamily N, i ∉ J) :
    realSumPrincipalMinorInverses A i j = 0 := by
  unfold realSumPrincipalMinorInverses
  rw [Finset.sum_apply, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro J hJ
  exact paddedMinorInverse_zero_outside A J i j (h J hJ)

end PallLean.Paper93.Paper283
