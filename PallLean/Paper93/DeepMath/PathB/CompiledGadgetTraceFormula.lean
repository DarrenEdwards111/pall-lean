import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Trace formula for the compiled gadget

We derive the closed form for the trace of the §28.3 compiled gadget
matrix `compiledGadget α n = α • I + L_{K_n}` on `Fin n`:
`trace (compiledGadget α n) = n * α + n * (n - 1)`.

The proof uses `compiledGadget_diagonal`, which gives the diagonal
entries `α + (n - 1)`, and then sums `n` constant copies.

As a corollary, when `α > 0` and `n ≥ 1` the trace is strictly positive.
Combined with the standard fact that the trace of a real symmetric
matrix is the sum of its (real) eigenvalues, this implies that
`compiledGadget α n` has at least one strictly positive eigenvalue, and
hence the rank is at least `1`.  We do not formalise the rank step
here; it is given separately in the rank-bound chain.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.LPS
open PallLean.Paper93.DeepMath.GraphSpectral
open Matrix

/-- **Trace formula for the compiled gadget.**

`trace (α • I + L_{K_n}) = n * α + n * (n - 1)`.

Proof: each diagonal entry equals `α + (n - 1)` by
`compiledGadget_diagonal`, and the trace is the sum over the `n`
indices of these constant entries, which is `n * (α + (n - 1))`. -/
theorem compiledGadget_trace_formula (α : ℝ) (n : ℕ) :
    (compiledGadget α n).trace = (n : ℝ) * α + (n : ℝ) * ((n : ℝ) - 1) := by
  -- Unfold `Matrix.trace` to `∑ i, diag M i = ∑ i, M i i`.
  show (∑ i, Matrix.diag (compiledGadget α n) i)
        = (n : ℝ) * α + (n : ℝ) * ((n : ℝ) - 1)
  -- Replace each diagonal entry by `α + (n - 1)`.
  have hconst : ∀ i : Fin n,
      Matrix.diag (compiledGadget α n) i = α + ((n : ℝ) - 1) := by
    intro i
    rw [Matrix.diag_apply]
    exact compiledGadget_diagonal α n i
  rw [Finset.sum_congr rfl (fun i _ => hconst i)]
  -- `∑ _ : Fin n, c = n • c = n * c`.
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- `n * (α + (n - 1)) = n * α + n * (n - 1)`.
  ring

/-- **Positivity of the compiled gadget trace.**

For `α > 0` and `n ≥ 1`, the trace `n * α + n * (n - 1)` is strictly
positive.  Both summands are nonneg (the second since `n ≥ 1` gives
`n - 1 ≥ 0`), and the first is strictly positive since `n ≥ 1` and
`α > 0`. -/
theorem compiledGadget_trace_pos (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 1 ≤ n) :
    0 < (compiledGadget α n).trace := by
  rw [compiledGadget_trace_formula]
  -- Coerce `1 ≤ n` to `(1 : ℝ) ≤ (n : ℝ)`.
  have hn_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- Hence `(n : ℝ) ≥ 1 > 0` and `(n : ℝ) - 1 ≥ 0`.
  have hn_pos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le one_pos hn_real
  have hn_sub_nonneg : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  -- `n * α > 0` and `n * (n - 1) ≥ 0`.
  have h1 : 0 < (n : ℝ) * α := mul_pos hn_pos hα
  have h2 : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) := mul_nonneg (le_of_lt hn_pos) hn_sub_nonneg
  linarith

end PallLean.Paper93.DeepMath.PathB
