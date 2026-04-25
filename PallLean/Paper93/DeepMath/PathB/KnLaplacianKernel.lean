import PallLean.Paper93.DeepMath.LPS.KnLaplacianConstKernel
import PallLean.Paper93.DeepMath.LPS.CompleteGraphAdj
import PallLean.Paper93.DeepMath.LPS.CompleteGraphEig
import PallLean.Paper93.DeepMath.LPS.KnLaplacianEig
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef
import PallLean.Paper93.DeepMath.GraphSpectral.DiagonalMulVec
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
# Kernel of the `K_n` Laplacian: the all-ones vector

We prove that the graph Laplacian `L = D − A` of the complete graph `K_n`
sends the constant all-ones vector to zero, and more generally that any
constant vector lies in the kernel of `L`.

This is the well-known fact that `L · 1 = 0`: each row of the Laplacian
sums to zero because `(D - A) i j = (rowSum A) i · δ_{ij} − A i j`, and
summing over `j` gives `(rowSum A) i − (rowSum A) i = 0`.

The first theorem follows directly from the existing
`completeAdj_laplacian_ones` lemma; the second is obtained by linearity
of `mulVec` in the vector argument.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GraphSpectral
open PallLean.Paper93.DeepMath.LPS

/-- **Kernel of the `K_n` Laplacian (all-ones case).**

The graph Laplacian `L = D − A` of the complete graph `K_n` annihilates
the constant all-ones vector:
\[
   (L \cdot \mathbf{1})_i
   = (D \cdot \mathbf{1})_i - (A \cdot \mathbf{1})_i
   = (\mathrm{rowSum}\,A)_i - (\mathrm{rowSum}\,A)_i = 0.
\]
For `K_n`, both sides equal `(n - 1)`, so the difference is zero. -/
theorem laplacian_completeAdj_mulVec_const_one_eq_zero (n : ℕ) :
    (laplacian (completeAdj n)).mulVec (fun _ : Fin n => (1 : ℝ))
      = (fun _ : Fin n => (0 : ℝ)) := by
  -- The existing `completeAdj_laplacian_ones` proves
  -- `(L · 1) = 0`, where the right-hand side is the zero function on
  -- `Fin n → ℝ`.  We rewrite that into the explicit `fun _ => 0` form.
  have h := completeAdj_laplacian_ones n
  funext i
  -- `0 : Fin n → ℝ` is the zero of the Pi-type, whose value at any index
  -- is `(0 : ℝ)`.
  have hi := congrArg (fun f : Fin n → ℝ => f i) h
  simpa using hi

/-- **Kernel of the `K_n` Laplacian (general constant case).**

For any real constant `c`, the constant vector with value `c` lies in
the kernel of the `K_n` Laplacian. This follows from
`laplacian_completeAdj_mulVec_const_one_eq_zero` together with linearity
of `mulVec` in its vector argument:
\[
   L \cdot (c \cdot \mathbf{1}) = c \cdot (L \cdot \mathbf{1}) = c \cdot 0 = 0.
\]
-/
theorem laplacian_completeAdj_mulVec_const (n : ℕ) (c : ℝ) :
    (laplacian (completeAdj n)).mulVec (fun _ : Fin n => c)
      = (fun _ : Fin n => (0 : ℝ)) := by
  -- Rewrite the constant vector as `c • (fun _ => 1)`.
  have hconst : (fun _ : Fin n => c) = c • (fun _ : Fin n => (1 : ℝ)) := by
    funext i
    simp [Pi.smul_apply, smul_eq_mul]
  -- Use linearity of `mulVec` in the vector argument.
  rw [hconst, Matrix.mulVec_smul]
  -- Now: `c • L.mulVec (fun _ => 1) = fun _ => 0`.
  rw [laplacian_completeAdj_mulVec_const_one_eq_zero]
  -- Goal: `c • (fun _ : Fin n => (0 : ℝ)) = (fun _ : Fin n => (0 : ℝ))`.
  funext i
  simp [Pi.smul_apply, smul_eq_mul]

end PallLean.Paper93.DeepMath.PathB
