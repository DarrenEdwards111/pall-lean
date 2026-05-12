/-
  PallLean/Paper93/Paper283/AmplituhedronBarrier.lean

  Paper §28.3 — Amplituhedron-positivity barrier

      B(A) = − Σ_{J ∈ J} log det(A[J,J])

  where `J` runs over the principal-minor index family
  `minorFamily N` (X5) and `A[J,J]` is the principal minor
  `principalMinor A J` (X6).

  This file provides the Paper §28.3 barrier functional and two
  sanity results:

    * `amplituhedronBarrier_identity`  — `B(I) = 0`, since each
      principal minor of the identity has determinant `1` and
      `log 1 = 0`.

    * `amplituhedronBarrier_det_pos_bound` — nonnegativity of the
      barrier on matrices whose principal minors satisfy
      `0 < det(A[J,J]) ≤ 1` for every `J ∈ minorFamily N`.
      (As any such determinant approaches `0⁺`, the corresponding
      summand `−log det(A[J,J])` diverges to `+∞`.)

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  ## Paper citations

    * §28.3 — amplituhedron-positivity barrier term
      `B(A) = − Σ_{J ∈ J} log det(A[J,J])`.
-/

import PallLean.Paper93.Paper283.MinorFamily
import PallLean.Paper93.Paper283.PrincipalMinor
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace PallLean.Paper93.Paper283

open Real
open scoped BigOperators

/-- Paper §28.3 barrier function. Sum runs over `minorFamily`. -/
noncomputable def amplituhedronBarrier {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  -∑ J ∈ minorFamily N, Real.log (principalMinor A J).det

/-- `B(I) = 0` since each principal minor of `I` has `det = 1`
    so `log = 0`. -/
theorem amplituhedronBarrier_identity {N : ℕ} :
    amplituhedronBarrier (1 : Matrix (Fin N) (Fin N) ℝ) = 0 := by
  unfold amplituhedronBarrier
  simp [principalMinor_one_det, Real.log_one]

/-- Barrier blows up as any principal minor determinant → `0⁺`.
    Concretely, on the bounded regime `0 < det(A[J,J]) ≤ 1` for all
    `J ∈ minorFamily N`, the barrier is nonnegative. -/
theorem amplituhedronBarrier_det_pos_bound {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ)
    (h : ∀ J ∈ minorFamily N, 0 < (principalMinor A J).det)
    (hUpper : ∀ J ∈ minorFamily N, (principalMinor A J).det ≤ 1) :
    0 ≤ amplituhedronBarrier A := by
  unfold amplituhedronBarrier
  rw [neg_nonneg]
  apply Finset.sum_nonpos
  intro J hJ
  exact Real.log_nonpos (le_of_lt (h J hJ)) (hUpper J hJ)

end PallLean.Paper93.Paper283
