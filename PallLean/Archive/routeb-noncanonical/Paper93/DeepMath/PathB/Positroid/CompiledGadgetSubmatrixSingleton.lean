import PallLean.Paper93.DeepMath.PathB.CompiledGadgetSingletonMinor
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Principal submatrix of the compiled gadget at a singleton

This file restates the principal-minor formula for `compiledGadget α n` at a
singleton `{i} : Finset (Fin n)`, packaged in the `Positroid` namespace as a
direct corollary of `compiledGadget_singleton_minor` (see
`PallLean.Paper93.DeepMath.PathB.CompiledGadgetSingletonMinor`).

The principal submatrix at `{i}` is the `1 × 1` matrix whose unique diagonal
entry is `α + (n - 1)`, so its determinant equals `α + (n - 1)`.  We also
record the degenerate `n = 2`, `α = 0` instance, where the singleton minor
collapses to `1`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- The principal minor at `{i}` is `α + (n - 1)` for any `i`. -/
theorem compiledGadget_principalMinor_singleton (α : ℝ) (n : ℕ) (i : Fin n) :
    ((compiledGadget α n).submatrix
      (fun j : ({i} : Finset (Fin n)) => (j.val : Fin n))
      (fun j : ({i} : Finset (Fin n)) => (j.val : Fin n))).det
    = α + ((n : ℝ) - 1) :=
  compiledGadget_singleton_minor α n i

/-- For `α = 2 - n` (the unique value making the singleton minor `1`) at
`n = 2`: `α = 0` (degenerate). -/
theorem singleton_minor_eq_one_at_n2 :
    ((compiledGadget 0 2).submatrix
      (fun j : ({⟨0, by omega⟩} : Finset (Fin 2)) => (j.val : Fin 2))
      (fun j : ({⟨0, by omega⟩} : Finset (Fin 2)) => (j.val : Fin 2))).det
    = 1 := by
  rw [compiledGadget_principalMinor_singleton]
  norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid
