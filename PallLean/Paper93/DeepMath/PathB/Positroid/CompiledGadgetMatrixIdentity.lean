import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetStructIdentity
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Matrix-level structural identity for the compiled gadget

We promote the entrywise structural identity of
`compiledGadget_struct_identity` to a clean matrix-level equation:

  `compiledGadget α n = (α + n) • I_n − J_n`,

where `I_n = (1 : Matrix (Fin n) (Fin n) ℝ)` is the identity matrix and
`J_n = vecMulVec (Function.const (Fin n) 1) (Function.const (Fin n) 1)`
is the all-ones rank-1 outer product (`1 · 1ᵀ`).

This is the matrix form of the diagonal-mode-minus-constant-background
identity used throughout the Route C ⇒ Route A bridge for the
truncated NS / gadget construction. The proof reduces to
`Matrix.ext` plus the entrywise lemma
`compiledGadget_struct_identity` and a `split_ifs` + `ring` cleanup of
the right-hand side.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank
open Matrix

/-- **Matrix-level structural identity for the compiled gadget.**

For all `α : ℝ` and `n : ℕ`,
`compiledGadget α n = (α + n) • (1 : Matrix (Fin n) (Fin n) ℝ)
   − Matrix.vecMulVec (Function.const (Fin n) 1) (Function.const (Fin n) 1)`.

In words: the compiled gadget equals `(α + n) · I_n − J_n`, where
`J_n = 1 · 1ᵀ` is the all-ones rank-1 outer product. The proof reduces
to the entrywise identity `compiledGadget_struct_identity` via
`Matrix.ext`, evaluating each side at indices `(i, j)` and finishing
with case analysis on `i = j` and `ring`. -/
theorem compiledGadget_matrix_identity (α : ℝ) (n : ℕ) :
    compiledGadget α n
      = (α + (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ)
          - Matrix.vecMulVec (Function.const (Fin n) (1 : ℝ))
              (Function.const (Fin n) (1 : ℝ)) := by
  -- Reduce to an entrywise check.
  ext i j
  -- LHS entry from the entrywise structural identity.
  rw [compiledGadget_struct_identity α n i j]
  -- Evaluate the RHS entry-by-entry: subtraction is pointwise.
  have hsub :
      ((α + (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ)
          - Matrix.vecMulVec (Function.const (Fin n) (1 : ℝ))
              (Function.const (Fin n) (1 : ℝ))) i j
        = ((α + (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ)) i j
          - (Matrix.vecMulVec (Function.const (Fin n) (1 : ℝ))
              (Function.const (Fin n) (1 : ℝ))) i j := rfl
  rw [hsub]
  -- The `vecMulVec` entry: `Function.const (Fin n) 1 i * Function.const (Fin n) 1 j = 1`.
  have hvmv :
      (Matrix.vecMulVec (Function.const (Fin n) (1 : ℝ))
          (Function.const (Fin n) (1 : ℝ))) i j = 1 := by
    rw [Matrix.vecMulVec_apply]
    show (1 : ℝ) * (1 : ℝ) = 1
    ring
  rw [hvmv]
  -- The smul entry: `((α + n) • 1) i j = (α + n) * (if i = j then 1 else 0)`.
  have hsmul :
      ((α + (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ)) i j
        = (α + (n : ℝ)) * (if i = j then (1 : ℝ) else 0) := by
    show (α + (n : ℝ)) • ((1 : Matrix (Fin n) (Fin n) ℝ) i j)
            = (α + (n : ℝ)) * (if i = j then (1 : ℝ) else 0)
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

end PallLean.Paper93.DeepMath.PathB.Positroid
