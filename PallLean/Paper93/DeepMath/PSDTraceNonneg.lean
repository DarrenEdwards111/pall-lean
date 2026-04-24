import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Trace of a real PSD matrix is nonnegative

For any real `N × N` positive semi-definite matrix `M`, the trace
`Matrix.trace M` is nonnegative. The proof proceeds through the
eigenvalue decomposition of the underlying Hermitian (symmetric)
matrix, invoking the spectral theorem identity
`Matrix.IsHermitian.trace_eq_sum_eigenvalues` together with
`Matrix.PosSemidef.eigenvalues_nonneg` and `Finset.sum_nonneg`.

All lemmas used are real Mathlib lemmas; the result is also available
directly as `Matrix.PosSemidef.trace_nonneg` in Mathlib. We keep the
full eigenvalue-based proof structure for Paper~9.3 downstream clients
that need access to the spectral identity explicitly.
-/

namespace PallLean.Paper93.DeepMath

open scoped Matrix

/-- The trace of a real positive semi-definite matrix is nonnegative.

Proof structure (eigenvalue-based, Route C / Paper~9.3 compliant):

* By the spectral theorem
  (`Matrix.IsHermitian.trace_eq_sum_eigenvalues`), the trace of any
  real Hermitian matrix equals the sum of its eigenvalues (cast back
  to `ℝ`; the cast is the identity for the scalar field `𝕜 = ℝ`).
* By `Matrix.PosSemidef.eigenvalues_nonneg`, every eigenvalue of a
  PSD matrix is `≥ 0`.
* `Finset.sum_nonneg` then gives the trace is `≥ 0`. -/
theorem psd_trace_nonneg {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℝ) (hM : M.PosSemidef) :
    0 ≤ M.trace := by
  -- Spectral identity: trace equals the sum of the real eigenvalues,
  -- cast to the scalar field `ℝ` (which is the identity cast here).
  have hHerm : M.IsHermitian := hM.1
  have htrace : M.trace = ∑ i, ((hHerm.eigenvalues i : ℝ) : ℝ) :=
    hHerm.trace_eq_sum_eigenvalues
  -- Every eigenvalue is nonnegative.
  have heig : ∀ i : Fin N, 0 ≤ hHerm.eigenvalues i := fun i =>
    hM.eigenvalues_nonneg i
  -- Sum of nonnegatives is nonnegative.
  have hsum : (0 : ℝ) ≤ ∑ i, ((hHerm.eigenvalues i : ℝ) : ℝ) :=
    Finset.sum_nonneg (fun i _ => heig i)
  -- Rewrite the trace using the spectral identity and conclude.
  rw [htrace]
  exact hsum

end PallLean.Paper93.DeepMath
