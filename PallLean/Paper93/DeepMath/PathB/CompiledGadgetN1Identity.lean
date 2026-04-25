import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.LPS.CompleteGraphAdj
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The compiled gadget at `n = 1, α = 1` is the identity

For `n = 1`, the complete graph `K_1` has no edges (no self-loops by
convention), so its adjacency matrix `completeAdj 1` is the zero matrix
on `Fin 1`.  Consequently, its graph Laplacian `L_{K_1}` is also zero,
and the compiled gadget reduces to a scalar multiple of the identity:

* `compiledGadget α 1 = α • I` for any `α : ℝ`.
* In particular, `compiledGadget 1 1 = I`.

The proofs are direct: we extend matrices via `Matrix.ext` and case on
`i j : Fin 1`, where the only inhabitant is `0`, so `i = j` always
holds.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.LPS
open PallLean.Paper93.DeepMath.GraphSpectral

/-- For `Fin 1`, the only adjacency entry is `(0, 0)`, which is a
diagonal entry, hence the adjacency matrix of the complete graph `K_1`
is the zero matrix. -/
theorem completeAdj_one_is_zero :
    (completeAdj 1) = (0 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  -- The only element of `Fin 1` is `0`, so `i = j`.
  have hi : i = 0 := Subsingleton.elim i 0
  have hj : j = 0 := Subsingleton.elim j 0
  have hij : i = j := by rw [hi, hj]
  -- Unfold `completeAdj` and use `i = j` to land on the `0` branch.
  show (if i = j then (0 : ℝ) else 1) = (0 : Matrix (Fin 1) (Fin 1) ℝ) i j
  rw [if_pos hij]
  -- The right-hand side is `0` by `Matrix.zero_apply`.
  show (0 : ℝ) = (0 : Matrix (Fin 1) (Fin 1) ℝ) i j
  rw [Matrix.zero_apply]

/-- The graph Laplacian of `K_1` (i.e.\ of `completeAdj 1`) is the
zero `1×1` real matrix.  This is immediate from
`completeAdj_one_is_zero` together with the definition
`laplacian A = diagonal (rowSum A) - A`: when `A = 0`, both
`rowSum A = 0` and `A = 0`, so `diagonal 0 - 0 = 0`. -/
theorem laplacian_completeAdj_one_is_zero :
    laplacian (completeAdj 1) = (0 : Matrix (Fin 1) (Fin 1) ℝ) := by
  -- First reduce to the case `A = 0`.
  rw [completeAdj_one_is_zero]
  -- Now show `laplacian 0 = 0`.
  unfold laplacian
  ext i j
  -- Compute `rowSum 0 i = ∑ j, 0 = 0`.
  have hrow : rowSum (0 : Matrix (Fin 1) (Fin 1) ℝ) i = 0 := by
    unfold rowSum
    simp
  -- Compute the LHS pointwise.
  show (Matrix.diagonal (rowSum (0 : Matrix (Fin 1) (Fin 1) ℝ))
        - (0 : Matrix (Fin 1) (Fin 1) ℝ)) i j = 0
  rw [Matrix.sub_apply, Matrix.zero_apply, sub_zero]
  -- `diagonal f i j = if i = j then f i else 0`.
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, hrow]
  · rw [Matrix.diagonal_apply_ne _ hij]

/-- **The compiled gadget at `α = 1, n = 1` is the identity matrix.**

Direct consequence of `compiledGadget α n = α • I + L_{K_n}` together
with `laplacian_completeAdj_one_is_zero`: for `n = 1` the Laplacian
contribution vanishes, leaving `1 • I = I`. -/
theorem compiledGadget_one_one_is_identity :
    compiledGadget 1 1 = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  unfold compiledGadget
  rw [laplacian_completeAdj_one_is_zero, add_zero, one_smul]

/-- **The compiled gadget at `n = 1` reduces to `α • I` for any `α`.**

Same argument as `compiledGadget_one_one_is_identity` but with the
`one_smul` step replaced by leaving `α • I` in scalar form. -/
theorem compiledGadget_alpha_one_is_smul_identity (α : ℝ) :
    compiledGadget α 1 = α • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  unfold compiledGadget
  rw [laplacian_completeAdj_one_is_zero, add_zero]

end PallLean.Paper93.DeepMath.PathB
