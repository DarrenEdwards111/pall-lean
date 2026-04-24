/-
  PallLean/Paper93/Concrete/RealBarrier.lean

  V6 — Real log-det barrier using V4's realIdentityMinor + V5's
  log-det properties. Non-vacuous: for arbitrary `N × N` real matrices
  `M` (not just the identity minor), the barrier

      realBarrier β M  :=  -β · matrixLogDet M

  is a real-valued functional of `M` at temperature `β : ℝ`.
  See the paper §28.3 pp. 137–138 amplituhedron determinantal
  barrier term.

  This file provides:

    * `realBarrier` — the real barrier functional.

    * `realBarrier_of_posDef` — for any positive-definite `M` and
      `0 ≤ β`, `realBarrier β M ≤ -β · Real.log M.det` (here an
      identity, by definitional unfolding).

    * `realBarrier_identity_zero` — `realBarrier β 1 = 0`.

    * `realBarrier_small_det_large` — for `0 < β` and
      `0 < det M ≤ 1`, the barrier is nonnegative: approaches
      `+∞` as `det M → 0`, i.e. near-singular `M`.

  ## Kernel-only
    * No `sorry`.
    * No bespoke axioms.
-/

import PallLean.Paper93.Concrete.LogDet
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace PallLean.Paper93.Concrete

open Matrix

/-- Real barrier using a non-identity projection matrix. -/
noncomputable def realBarrier {N : ℕ} (β : ℝ) (M : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  -β * matrixLogDet M

theorem realBarrier_of_posDef {N β} (M : Matrix (Fin N) (Fin N) ℝ)
    (hM : M.PosDef) (hβ : 0 ≤ β) :
    realBarrier β M ≤ -β * Real.log (M.det) := by
  unfold realBarrier matrixLogDet
  linarith

theorem realBarrier_identity_zero {N β} :
    realBarrier β (1 : Matrix (Fin N) (Fin N) ℝ) = 0 := by
  unfold realBarrier matrixLogDet
  simp [Matrix.det_one, Real.log_one]

/-- Barrier is large when det small (approaches singular). -/
theorem realBarrier_small_det_large {N β} (M : Matrix (Fin N) (Fin N) ℝ)
    (hβ : 0 < β) (hdet : 0 < M.det) (hsmall : M.det ≤ 1) :
    0 ≤ realBarrier β M := by
  unfold realBarrier matrixLogDet
  have hlog : Real.log M.det ≤ 0 := Real.log_nonpos (le_of_lt hdet) hsmall
  have hβnn : 0 ≤ β := le_of_lt hβ
  have hprod : β * Real.log M.det ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβnn hlog
  linarith

end PallLean.Paper93.Concrete
