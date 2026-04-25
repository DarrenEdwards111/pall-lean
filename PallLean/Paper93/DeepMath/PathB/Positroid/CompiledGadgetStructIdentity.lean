import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.LPS.CompleteGraphAdj
import PallLean.Paper93.DeepMath.LPS.KnLaplacianEig
import PallLean.Paper93.DeepMath.LPS.KnLaplacianTrace
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Structural entrywise identity for the compiled gadget

We prove the structural entrywise identity

  `compiledGadget α n i j = (α + n) * (if i = j then 1 else 0) - 1`

which collapses the definition `compiledGadget α n = α • I + L_{K_n}`
to a single closed-form expression in the index pair `(i, j)`.

This is a "Route C ⇒ Route A"–flavoured structural fact: the gadget is
nothing more than the diagonal-mode contribution `(α + n) • I` minus the
constant all-ones background, evaluated entrywise. In particular every
off-diagonal entry equals `-1` and every diagonal entry equals
`α + n - 1`.

The proof unfolds `compiledGadget`, evaluates the `(i, j)` entry of
`α • I` and of `laplacian (completeAdj n)` separately, and finishes
with `split_ifs` + `ring`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.LPS
open PallLean.Paper93.DeepMath.GraphSpectral
open Matrix

/-- **Structural entrywise identity for the compiled gadget.**

For all `α : ℝ`, `n : ℕ`, and indices `i j : Fin n`,
`compiledGadget α n i j = (α + n) * (if i = j then 1 else 0) - 1`.

The proof proceeds entrywise:

* `(α • 1 + L) i j = (α • 1) i j + L i j` (entrywise sum),
* `(α • 1) i j = α * (if i = j then 1 else 0)` (smul of identity),
* `L i j = (diagonal (rowSum A)) i j - A i j` for `L = laplacian A`,
* `(diagonal d) i j = if i = j then d i else 0`,
* `rowSum (completeAdj n) i = n - 1`,
* `(completeAdj n) i j = if i = j then 0 else 1`.

Combining these and splitting on `i = j` gives the closed form. -/
theorem compiledGadget_struct_identity (α : ℝ) (n : ℕ) (i j : Fin n) :
    compiledGadget α n i j
      = (α + (n : ℝ)) * (if i = j then (1 : ℝ) else 0) - 1 := by
  -- Unfold the definition `α • 1 + laplacian (completeAdj n)`.
  unfold compiledGadget
  -- Evaluate the sum entrywise at `(i, j)`.
  have hadd :
      (α • (1 : Matrix (Fin n) (Fin n) ℝ) + laplacian (completeAdj n)) i j
        = (α • (1 : Matrix (Fin n) (Fin n) ℝ)) i j
          + (laplacian (completeAdj n)) i j := rfl
  rw [hadd]
  -- Compute `(α • 1) i j = α * (if i = j then 1 else 0)`.
  have hsmul :
      (α • (1 : Matrix (Fin n) (Fin n) ℝ)) i j
        = α * (if i = j then (1 : ℝ) else 0) := by
    show α • ((1 : Matrix (Fin n) (Fin n) ℝ) i j)
            = α * (if i = j then (1 : ℝ) else 0)
    by_cases hij : i = j
    · subst hij
      have hone : (1 : Matrix (Fin n) (Fin n) ℝ) i i = 1 := by
        simp [Matrix.one_apply_eq]
      rw [hone]
      simp
    · have hzero : (1 : Matrix (Fin n) (Fin n) ℝ) i j = 0 :=
        Matrix.one_apply_ne hij
      rw [hzero]
      simp [hij]
  rw [hsmul]
  -- Compute `(laplacian (completeAdj n)) i j` entrywise.
  have hlap :
      (laplacian (completeAdj n)) i j
        = (if i = j then ((n : ℝ) - 1) else 0)
            - (if i = j then (0 : ℝ) else 1) := by
    unfold laplacian
    have hsub :
        (Matrix.diagonal (rowSum (completeAdj n)) - completeAdj n) i j
          = (Matrix.diagonal (rowSum (completeAdj n))) i j
              - (completeAdj n) i j := rfl
    rw [hsub]
    -- Diagonal entry: `(diagonal d) i j = if i = j then d i else 0`.
    have hdiag :
        (Matrix.diagonal (rowSum (completeAdj n))) i j
          = (if i = j then ((n : ℝ) - 1) else 0) := by
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq]
        have hrow : rowSum (completeAdj n) i = (n : ℝ) - 1 := by
          unfold rowSum
          exact completeAdj_rowSum n i
        rw [hrow]
        simp
      · rw [Matrix.diagonal_apply_ne _ hij]
        simp [hij]
    -- Adjacency entry: `(completeAdj n) i j = if i = j then 0 else 1`.
    have hadj :
        (completeAdj n) i j = (if i = j then (0 : ℝ) else 1) := by
      show (if i = j then (0 : ℝ) else 1) = (if i = j then (0 : ℝ) else 1)
      rfl
    rw [hdiag, hadj]
  rw [hlap]
  -- Finish with case analysis on `i = j` and `ring`.
  by_cases hij : i = j
  · simp [hij]; ring
  · simp [hij]

/-- **Off-diagonal entries of the compiled gadget are `-1`.**

Immediate corollary of `compiledGadget_struct_identity`: for `i ≠ j`,
`compiledGadget α n i j = -1`. -/
theorem compiledGadget_off_diag (α : ℝ) (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    compiledGadget α n i j = -1 := by
  rw [compiledGadget_struct_identity α n i j]
  simp [hij]

/-- **Diagonal entries of the compiled gadget are `α + n - 1`.**

Immediate corollary of `compiledGadget_struct_identity`: for any `i`,
`compiledGadget α n i i = α + n - 1`. This re-derives the diagonal
formula `compiledGadget_diagonal` directly from the structural
identity. -/
theorem compiledGadget_diag_from_struct (α : ℝ) (n : ℕ) (i : Fin n) :
    compiledGadget α n i i = α + (n : ℝ) - 1 := by
  rw [compiledGadget_struct_identity α n i i]
  simp

end PallLean.Paper93.DeepMath.PathB.Positroid
