import PallLean.Paper93.DeepMath.LPS.KnLaplacianEig
import PallLean.Paper93.DeepMath.LPS.CompleteGraphEig
import PallLean.Paper93.DeepMath.GraphSpectral.DiagonalMulVec

namespace PallLean.Paper93.DeepMath.LPS

open PallLean.Paper93.DeepMath.GraphSpectral

/-- The constant-1 vector is in the kernel of the `K_n` Laplacian:
`L · 1 = 0`, where `L := laplacian (completeAdj n)`.

For any vertex `i`, the row-sum `(rowSum A) i = n - 1` equals the value of
`A · 1` at `i`, so `(D · 1 − A · 1) i = (n-1) · 1 − (n-1) = 0`. -/
theorem completeAdj_laplacian_ones (n : ℕ) :
    (laplacian (completeAdj n)).mulVec (fun _ : Fin n => (1 : ℝ)) = 0 := by
  funext i
  -- Unfold Laplacian: `L = diagonal (rowSum A) − A`, hence
  -- `L · 1 = diagonal (rowSum A) · 1 − A · 1`.
  unfold laplacian
  rw [Matrix.sub_mulVec, Pi.sub_apply]
  -- Rewrite the diagonal part using `mulVec_diagonal`.
  rw [Matrix.mulVec_diagonal]
  -- Adjacency part: `(A · 1) i = n - 1`.
  have h_A_one :
      (completeAdj n).mulVec (fun _ : Fin n => (1 : ℝ)) i = (n : ℝ) - 1 :=
    completeAdj_ones_eigen n i
  -- Row-sum at `i` is `n - 1`.
  have h_rowSum : rowSum (completeAdj n) i = (n : ℝ) - 1 := by
    unfold rowSum
    exact completeAdj_rowSum n i
  rw [h_A_one, h_rowSum]
  -- Remaining arithmetic goal: `((n : ℝ) - 1) * 1 - ((n : ℝ) - 1) = 0 i`.
  show ((n : ℝ) - 1) * (1 : ℝ) - ((n : ℝ) - 1) = (0 : Fin n → ℝ) i
  simp

end PallLean.Paper93.DeepMath.LPS
