/-
Copyright (c) 2026 Pall Lean contributors. All rights reserved.
-/
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

/-!
# Idempotence of the identity endomorphism

This file provides a small, fully proved instance of the Mathlib
`IsIdempotentElem` predicate in the setting relevant to the `RealPiStar`
chain: the identity endomorphism of `ℝ`, viewed as an element of the
endomorphism ring `Module.End ℝ ℝ`, is idempotent because `id ∘ id = id`.

The result is obtained by specialising `IsIdempotentElem.one`, using the
Mathlib identification of `1 : Module.End ℝ ℝ` with `LinearMap.id` via
`Module.End.one_eq_id`.
-/

namespace PallLean.Paper93.DeepMath.RealPiStar

open LinearMap

/-- The multiplicative identity of any `MulOneClass` is idempotent.  In particular,
this specialises to `(1 : Module.End ℝ ℝ)`, i.e. the identity `ℝ →ₗ[ℝ] ℝ`. -/
theorem one_isIdempotentElem_End : IsIdempotentElem (1 : Module.End ℝ ℝ) :=
  IsIdempotentElem.one

/-- The identity linear map on `ℝ`, viewed as an element of the endomorphism
ring `Module.End ℝ ℝ`, is idempotent: `id * id = id`, where multiplication in
`Module.End ℝ ℝ` is composition. -/
theorem id_isIdempotentElem_End :
    IsIdempotentElem (LinearMap.id : Module.End ℝ ℝ) := by
  -- `1 = LinearMap.id` in `Module.End ℝ ℝ`, so idempotence of `1` transfers.
  have h : (1 : Module.End ℝ ℝ) = LinearMap.id := Module.End.one_eq_id
  simpa [h] using (IsIdempotentElem.one : IsIdempotentElem (1 : Module.End ℝ ℝ))

/-- Unfolded form: composing `LinearMap.id` with itself yields `LinearMap.id`. -/
theorem id_comp_id :
    (LinearMap.id : ℝ →ₗ[ℝ] ℝ).comp (LinearMap.id : ℝ →ₗ[ℝ] ℝ) = LinearMap.id :=
  LinearMap.id_comp _

/-- The legacy matrix statement retained for downstream consumers: the `N × N`
identity matrix over `ℝ` is idempotent under matrix multiplication. -/
theorem realPiStar_identity_idempotent {N : ℕ} :
    (1 : Matrix (Fin N) (Fin N) ℝ) * 1 = 1 := by simp

end PallLean.Paper93.DeepMath.RealPiStar
