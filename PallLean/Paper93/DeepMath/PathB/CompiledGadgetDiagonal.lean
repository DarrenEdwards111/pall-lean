import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.LPS.KnLaplacianTrace
import PallLean.Paper93.DeepMath.LPS.KnLaplacianEig
import PallLean.Paper93.DeepMath.LPS.CompleteGraphAdj
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Diagonal entries of the compiled gadget matrix

We give the explicit formula for the diagonal entries of
`compiledGadget α n`, namely
`(compiledGadget α n) i i = α + (n - 1)`.

The argument is by direct unfolding:
* `(α • I) i i = α` (identity diagonal contribution),
* `(laplacian (completeAdj n)) i i = n - 1` (already proved as
  `completeAdj_laplacian_diag_entries`),
* `(M + N) i i = M i i + N i i`.

We also derive a corollary that fixes the value of `α` forced by the
constraint `(compiledGadget α n) i i = 1`, namely `α = 2 - n`.  For
`n ≥ 3` this forces `α` to be negative, structurally obstructing the
literal `compiledGadget` from serving as a gauge for singleton
principal minors.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.LPS
open PallLean.Paper93.DeepMath.GraphSpectral
open Matrix

/-- **Diagonal of the compiled gadget.**

For every Reynolds-free index `i : Fin n`,
`(compiledGadget α n) i i = α + (n - 1)`.

The proof unfolds `compiledGadget` to `α • I + L_{K_n}`, evaluates the
sum pointwise at `(i, i)`, uses `(α • I) i i = α` (since `1 i i = 1`),
and uses the previously proved diagonal entry of the K_n Laplacian
`completeAdj_laplacian_diag_entries`. -/
theorem compiledGadget_diagonal (α : ℝ) (n : ℕ) (i : Fin n) :
    compiledGadget α n i i = α + ((n : ℝ) - 1) := by
  -- Unfold the definition `α • 1 + laplacian (completeAdj n)`.
  unfold compiledGadget
  -- Evaluate the sum entrywise at `(i, i)`.
  have hadd :
      (α • (1 : Matrix (Fin n) (Fin n) ℝ) + laplacian (completeAdj n)) i i
        = (α • (1 : Matrix (Fin n) (Fin n) ℝ)) i i
          + (laplacian (completeAdj n)) i i := by
    rfl
  rw [hadd]
  -- Compute `(α • 1) i i = α * (1 i i) = α * 1 = α`.
  have hsmul :
      (α • (1 : Matrix (Fin n) (Fin n) ℝ)) i i = α := by
    -- `(α • M) i i = α • (M i i) = α * (M i i)` and `(1 : Matrix _ _ ℝ) i i = 1`.
    show α • ((1 : Matrix (Fin n) (Fin n) ℝ) i i) = α
    have hone : (1 : Matrix (Fin n) (Fin n) ℝ) i i = 1 := by
      simp [Matrix.one_apply_eq]
    rw [hone]
    simp
  rw [hsmul]
  -- The Laplacian diagonal entry is `n - 1`.
  have hlap : (laplacian (completeAdj n)) i i = (n : ℝ) - 1 :=
    completeAdj_laplacian_diag_entries n i
  rw [hlap]

/-- **Diagonal-equals-one constraint.**

The diagonal entry of the compiled gadget at `(i, i)` is equal to `1`
if and only if `α = 2 - n`.

This is structurally important: for `n ≥ 3`, `2 - n < 0`, so any
attempt to enforce `(compiledGadget α n) i i = 1` (the unit
singleton-minor condition) forces a *negative* coupling `α`, breaking
positive-definiteness of `α • I + L_{K_n}` and hence preventing the
literal `compiledGadget` from serving as a gauge for singleton
principal minors when `n ≥ 3`. -/
theorem compiledGadget_diagonal_eq_one_iff (α : ℝ) (n : ℕ) (i : Fin n) :
    compiledGadget α n i i = 1 ↔ α = 2 - (n : ℝ) := by
  constructor
  · intro h
    have hd : α + ((n : ℝ) - 1) = 1 := by
      rw [← compiledGadget_diagonal α n i]; exact h
    linarith
  · intro hα
    have hd : compiledGadget α n i i = α + ((n : ℝ) - 1) :=
      compiledGadget_diagonal α n i
    rw [hd, hα]; ring

end PallLean.Paper93.DeepMath.PathB
