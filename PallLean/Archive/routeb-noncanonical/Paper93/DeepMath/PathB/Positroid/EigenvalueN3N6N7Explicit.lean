import PallLean.Paper93.DeepMath.PathB.CompiledGadgetEigenvalueAlpha
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetOrthogonalEigenvec
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.Algebra.BigOperators.Fin

/-!
# Explicit eigenvalue identities for `compiledGadget` at n = 3, 6, 7

This file specialises the abstract eigenvalue identities
`compiledGadget_mulVec_one` and `compiledGadget_mulVec_sumZero`
(proved in `CompiledGadgetEigenvalueAlpha` and
`CompiledGadgetOrthogonalEigenvec`) to the concrete dimensions
`n = 3`, `n = 6`, and `n = 7`, in the same style as
`EigenvalueN2Explicit.lean` and `EigenvalueN4N5Explicit.lean`.

We also prove a concrete sum-zero eigenvector identity at `n = 3`
using the explicit vector `v = e_0 - e_1 = ![1, -1, 0]`, which has
sum zero and is therefore an eigenvector of `compiledGadget α 3`
with eigenvalue `α + 3`.

All proofs reduce to invocations of the already-established generic
theorems together with explicit sum/finset computations.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- **n = 3, all-ones eigenvector, eigenvalue α.**

Specialisation of `compiledGadget_mulVec_one` to `n = 3`. This is
provided in addition to `compiledGadget_n3_allOnes_eigenvalue`
(in `EigenvalueN2Explicit.lean`) under a distinct name, to keep the
explicit `n = 3, 6, 7` package self-contained. -/
theorem compiledGadget_n3_one_eigenvalue (α : ℝ) :
    (compiledGadget α 3).mulVec (fun _ : Fin 3 => 1) = (fun _ : Fin 3 => α) :=
  compiledGadget_mulVec_one α 3

/-- **n = 6, all-ones eigenvector, eigenvalue α.**

Specialisation of `compiledGadget_mulVec_one` to `n = 6`. -/
theorem compiledGadget_n6_allOnes_eigenvalue (α : ℝ) :
    (compiledGadget α 6).mulVec (fun _ : Fin 6 => 1) = (fun _ : Fin 6 => α) :=
  compiledGadget_mulVec_one α 6

/-- **n = 7, all-ones eigenvector, eigenvalue α.**

Specialisation of `compiledGadget_mulVec_one` to `n = 7`. -/
theorem compiledGadget_n7_allOnes_eigenvalue (α : ℝ) :
    (compiledGadget α 7).mulVec (fun _ : Fin 7 => 1) = (fun _ : Fin 7 => α) :=
  compiledGadget_mulVec_one α 7

/-- **n = 3, concrete sum-zero eigenvector `![1, -1, 0]`, eigenvalue α + 3.**

The vector `v = ![1, -1, 0] : Fin 3 → ℝ` has sum
`1 + (-1) + 0 = 0`, hence by `compiledGadget_mulVec_sumZero` at
`n = 3` it is an eigenvector of `compiledGadget α 3` with
eigenvalue `α + 3`. -/
theorem compiledGadget_n3_e01_sumZero_eigenvalue (α : ℝ) :
    (compiledGadget α 3).mulVec (![1, -1, 0] : Fin 3 → ℝ)
      = (α + 3) • (![1, -1, 0] : Fin 3 → ℝ) := by
  -- Establish the sum-zero hypothesis for the concrete vector by
  -- explicit Fin.sum unfolding.
  have hv : ∑ i, (![1, -1, 0] : Fin 3 → ℝ) i = 0 := by
    -- `Fin.sum_univ_three` rewrites the sum to a 3-term expression.
    rw [Fin.sum_univ_three]
    -- Now the goal is `![1, -1, 0] 0 + ![1, -1, 0] 1 + ![1, -1, 0] 2 = 0`.
    show (1 : ℝ) + (-1) + 0 = 0
    ring
  -- Apply the generic sum-zero eigenvalue identity at `n = 3`.
  have := compiledGadget_mulVec_sumZero α 3 (![1, -1, 0] : Fin 3 → ℝ) hv
  -- Convert `(α + (3 : ℕ : ℝ))` on the right-hand side to `(α + 3)`.
  -- Both sides are definitionally equal because `((3 : ℕ) : ℝ) = 3`.
  have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
  rw [h3] at this
  exact this

end PallLean.Paper93.DeepMath.PathB.Positroid
