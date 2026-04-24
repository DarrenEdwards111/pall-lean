import PallLean.Paper93.DeepMath.LPS.CompleteGraphAdj
import PallLean.Paper93.DeepMath.LPS.KnLaplacianEig
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef
import Mathlib.LinearAlgebra.Matrix.Trace

namespace PallLean.Paper93.DeepMath.LPS

open PallLean.Paper93.DeepMath.GraphSpectral
open Matrix

/-- Diagonal entries of the `K_n` Laplacian equal `n - 1`.

The Laplacian is `L = diagonal (rowSum A) - A`.  At `(i, i)` we have
`L i i = (rowSum A) i - A i i`.  For `A = completeAdj n`, the row-sum
is `n - 1` and the diagonal entry of the adjacency is `0`. -/
theorem completeAdj_laplacian_diag_entries (n : ℕ) (i : Fin n) :
    (laplacian (completeAdj n)) i i = (n : ℝ) - 1 := by
  -- Unfold `laplacian` to `diagonal (rowSum A) - A`.
  unfold laplacian
  -- Compute the `(i, i)` entry of the difference pointwise.
  have hsub :
      (Matrix.diagonal (rowSum (completeAdj n)) - completeAdj n) i i
        = (Matrix.diagonal (rowSum (completeAdj n))) i i - (completeAdj n) i i := by
    rfl
  rw [hsub]
  -- Diagonal entry of `diagonal d` at `(i,i)` is `d i`.
  rw [Matrix.diagonal_apply_eq]
  -- `rowSum (completeAdj n) i = (n : ℝ) - 1` (packaged form).
  have hrow : rowSum (completeAdj n) i = (n : ℝ) - 1 := by
    unfold rowSum
    exact completeAdj_rowSum n i
  -- Diagonal of `completeAdj n` at `(i, i)` is `0`.
  have hdiag : (completeAdj n) i i = (0 : ℝ) := by
    simp [completeAdj]
  rw [hrow, hdiag]
  ring

/-- Trace of the `K_n` Laplacian equals `n * (n - 1)`.

By definition, `trace L = ∑ i, L i i`.  Each diagonal entry is `n - 1`
(Lemma `completeAdj_laplacian_diag_entries`), and there are `n` such
entries, so the total is `n * (n - 1)`. -/
theorem completeAdj_laplacian_trace (n : ℕ) :
    (laplacian (completeAdj n)).trace = (n : ℝ) * ((n : ℝ) - 1) := by
  -- Unfold the definition of `Matrix.trace` to `∑ i, diag L i` = `∑ i, L i i`.
  show (∑ i, Matrix.diag (laplacian (completeAdj n)) i) = (n : ℝ) * ((n : ℝ) - 1)
  -- Replace each diagonal entry by `(n : ℝ) - 1`.
  have hconst : ∀ i : Fin n,
      Matrix.diag (laplacian (completeAdj n)) i = (n : ℝ) - 1 := by
    intro i
    rw [Matrix.diag_apply]
    exact completeAdj_laplacian_diag_entries n i
  rw [Finset.sum_congr rfl (fun i _ => hconst i)]
  -- `∑ _ : Fin n, ((n : ℝ) - 1) = n * ((n : ℝ) - 1)`.
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end PallLean.Paper93.DeepMath.LPS
