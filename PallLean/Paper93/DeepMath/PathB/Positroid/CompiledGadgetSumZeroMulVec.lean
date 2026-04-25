import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetStructIdentity
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# Matrix-level eigenvalue identity for sum-zero vectors

We prove the matrix-level eigenvalue identity for the compiled gadget on
the sum-zero subspace:

  `∀ v : Fin n → ℝ, (∑ i, v i = 0) →
       (compiledGadget α n).mulVec v = (α + n) • v`.

This is the **Route C ⇒ Route A** translation at the linear-algebra
level: the structural matrix identity

  `compiledGadget α n = (α + n) • I − J`,

where `J = 1 · 1ᵀ` is the all-ones matrix, implies that on the kernel of
`1ᵀ` (i.e. sum-zero vectors) the gadget acts as the scalar `α + n`. We
prove it directly entrywise by leveraging the structural identity

  `compiledGadget α n i j = (α + n) * (if i = j then 1 else 0) - 1`

(see `compiledGadget_struct_identity`). The dot product of row `i` with
`v` decomposes as

  `∑ j, ((α + n) * δ_{ij} - 1) * v j = (α + n) * v i - ∑ j, v j
        = (α + n) * v i`,

using `∑ j, v j = 0`.

This file complements `compiledGadget_mulVec_sumZero` in
`CompiledGadgetOrthogonalEigenvec.lean`, which obtains the same
conclusion by combining `Matrix.add_mulVec` with the K_n Laplacian
sum-zero eigen identity. The present proof relies only on the
**structural matrix identity** of the gadget (no Laplacian-level
arguments), and is therefore the canonical Route C ⇒ Route A
formulation.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.GadgetRank
open Matrix

/-- **Matrix-level eigenvalue identity for sum-zero vectors.**

Any vector `v : Fin n → ℝ` with `∑ i, v i = 0` is an eigenvector of
`compiledGadget α n` with eigenvalue `α + n`. The proof uses the
structural matrix identity
`compiledGadget α n i j = (α + n) * (if i = j then 1 else 0) - 1`
to decompose the row-`i` dot product as
`(α + n) * v i - ∑ j, v j`, and discharges the second term using
`∑ j, v j = 0`. -/
theorem compiledGadget_mulVec_sumZero_smul (α : ℝ) (n : ℕ) (v : Fin n → ℝ)
    (hv : ∑ i, v i = 0) :
    (compiledGadget α n).mulVec v = (α + (n : ℝ)) • v := by
  funext i
  -- Unfold `mulVec` to a `dotProduct` and `dotProduct` to a finite sum.
  show (compiledGadget α n).mulVec v i = ((α + (n : ℝ)) • v) i
  unfold Matrix.mulVec dotProduct
  -- Rewrite each summand using the structural identity for `compiledGadget`.
  have hsum_eq :
      (∑ j, compiledGadget α n i j * v j)
        = ∑ j, ((α + (n : ℝ)) * (if i = j then (1 : ℝ) else 0) - 1) * v j := by
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [compiledGadget_struct_identity α n i j]
  rw [hsum_eq]
  -- Distribute the multiplication: `(A * δ - 1) * v j = A * δ * v j - v j`.
  have hsplit :
      (∑ j, ((α + (n : ℝ)) * (if i = j then (1 : ℝ) else 0) - 1) * v j)
        = (∑ j, (α + (n : ℝ)) * (if i = j then (1 : ℝ) else 0) * v j)
          - (∑ j, v j) := by
    have hpt :
        ∀ j : Fin n,
          ((α + (n : ℝ)) * (if i = j then (1 : ℝ) else 0) - 1) * v j
            = (α + (n : ℝ)) * (if i = j then (1 : ℝ) else 0) * v j - v j := by
      intro j; ring
    calc  (∑ j, ((α + (n : ℝ)) * (if i = j then (1 : ℝ) else 0) - 1) * v j)
        = ∑ j, ((α + (n : ℝ)) * (if i = j then (1 : ℝ) else 0) * v j - v j) :=
              Finset.sum_congr rfl (fun j _ => hpt j)
      _ = (∑ j, (α + (n : ℝ)) * (if i = j then (1 : ℝ) else 0) * v j)
            - (∑ j, v j) := by
              rw [Finset.sum_sub_distrib]
  rw [hsplit, hv, sub_zero]
  -- Collapse the indicator sum: only the `j = i` term survives.
  have hindicator :
      (∑ j, (α + (n : ℝ)) * (if i = j then (1 : ℝ) else 0) * v j)
        = (α + (n : ℝ)) * v i := by
    have hpt :
        ∀ j : Fin n,
          (α + (n : ℝ)) * (if i = j then (1 : ℝ) else 0) * v j
            = (if i = j then (α + (n : ℝ)) * v j else 0) := by
      intro j
      by_cases hij : i = j
      · simp [hij]
      · simp [hij]
    calc  (∑ j, (α + (n : ℝ)) * (if i = j then (1 : ℝ) else 0) * v j)
        = ∑ j, (if i = j then (α + (n : ℝ)) * v j else 0) :=
              Finset.sum_congr rfl (fun j _ => hpt j)
      _ = (α + (n : ℝ)) * v i := by
              simp [Finset.sum_ite_eq, Finset.mem_univ]
  rw [hindicator]
  -- Reduce the RHS `((α + n) • v) i` to `(α + n) * v i`.
  show (α + (n : ℝ)) * v i = ((α + (n : ℝ)) • v) i
  simp [Pi.smul_apply, smul_eq_mul]

end PallLean.Paper93.DeepMath.PathB.Positroid
