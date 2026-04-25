import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetEigenvalueAlpha
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
# `Function.const`-form eigenvector statement for `compiledGadget α n`

We restate the eigenvector relation
`(compiledGadget α n).mulVec (fun _ => 1) = (fun _ => α)` (proved as
`compiledGadget_mulVec_one` in
`PallLean.Paper93.DeepMath.PathB.CompiledGadgetEigenvalueAlpha`)
in the equivalent form using `Function.const (Fin n) 1` for the
all-ones vector and `fun _ => α` for the right-hand side. This is the
Route~A-style form of the determining-modes/eigenvalue identity.

The proof is purely a `Function.const`-versus-`fun _ => _` rewrite on
top of the existing `compiledGadget_mulVec_one`. The `n ≥ 1` hypothesis
is *not* needed for the eigenvector identity itself (which holds for
all `n : ℕ`, vacuously when `n = 0` since `Fin 0` is empty), but we
include the corollary form requiring `1 ≤ n` to package together with
the existing `exists_eigenvector_alpha` API.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.PathB

/-- **All-ones eigenvector identity in `Function.const` form.**

For every `α : ℝ` and `n : ℕ`,
`(compiledGadget α n).mulVec (Function.const (Fin n) 1) = fun _ => α`.

Mathematically this is exactly `compiledGadget_mulVec_one`, since
`Function.const (Fin n) 1` is *definitionally* `fun _ : Fin n => 1`.
The proof closes by `funext` and pointwise reduction back to the
already-proved `compiledGadget_mulVec_one`. -/
theorem compiledGadget_allOnes_eigenvector (α : ℝ) (n : ℕ) :
    (compiledGadget α n).mulVec (Function.const (Fin n) (1 : ℝ))
      = fun _ : Fin n => α := by
  -- `Function.const (Fin n) (1 : ℝ)` is definitionally `fun _ : Fin n => (1 : ℝ)`.
  -- Hence `(compiledGadget α n).mulVec (Function.const (Fin n) 1)` reduces to
  -- `(compiledGadget α n).mulVec (fun _ => 1)`, which equals `fun _ => α` by
  -- `compiledGadget_mulVec_one`.
  show (compiledGadget α n).mulVec (fun _ : Fin n => (1 : ℝ))
      = fun _ : Fin n => α
  exact compiledGadget_mulVec_one α n

/-- **Packaged eigenvector existence for `n ≥ 1`.**

For any `n ≥ 1`, the explicit all-ones vector `Function.const (Fin n) 1`
is a nonzero eigenvector of `compiledGadget α n` with eigenvalue `α`.
This is a `Function.const`-flavoured restatement of the existing
`exists_eigenvector_alpha`. -/
theorem compiledGadget_allOnes_eigenvector_with_nonzero
    (α : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    Function.const (Fin n) (1 : ℝ) ≠ 0 ∧
      (compiledGadget α n).mulVec (Function.const (Fin n) (1 : ℝ))
        = fun _ : Fin n => α := by
  refine ⟨?_, compiledGadget_allOnes_eigenvector α n⟩
  -- Nonvanishing of the all-ones vector at index `⟨0, hn⟩`.
  intro h
  have hzero :
      Function.const (Fin n) (1 : ℝ) ⟨0, hn⟩
        = (0 : Fin n → ℝ) ⟨0, hn⟩ := congrFun h ⟨0, hn⟩
  -- The left-hand side reduces to `1`, the right-hand side to `0`.
  have h1 : (1 : ℝ) = 0 := hzero
  exact one_ne_zero h1

end PallLean.Paper93.DeepMath.PathB.Positroid
