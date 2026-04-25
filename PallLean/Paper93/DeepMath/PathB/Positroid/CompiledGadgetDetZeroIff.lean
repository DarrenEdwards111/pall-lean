import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.Tactic.Polyrith

/-!
# Det-zero iff for the small-`n` compiled gadgets

For each small `n ∈ {2, 3}`, we characterise exactly when the
determinant of the compiled gadget `compiledGadget α n = α • I + L_{K_n}`
vanishes:

* `compiledGadget_2_det_zero_iff` : `det = 0 ↔ α = 0 ∨ α = -2`,
  using the closed-form `det = α · (α + 2)`.
* `compiledGadget_3_det_zero_iff` : `det = 0 ↔ α = 0 ∨ α = -3`,
  using the closed-form `det = α · (α + 3)^2`.

These are immediate consequences of the closed-form determinant
formulas `compiledGadget_2x2_det` and `compiledGadget_3x3_det` together
with the fact that a product (or a power) of reals vanishes iff one of
the factors vanishes.

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- **Det-zero iff for the 2×2 compiled gadget.**

For every coupling `α : ℝ`, the determinant of `compiledGadget α 2`
vanishes if and only if `α = 0` or `α = -2`.

The proof rewrites the determinant via the closed form
`(compiledGadget α 2).det = α * (α + 2)` from
`compiledGadget_2x2_det` and reduces the resulting product
`α * (α + 2) = 0` to a disjunction via `mul_eq_zero`. -/
theorem compiledGadget_2_det_zero_iff (α : ℝ) :
    (compiledGadget α 2).det = 0 ↔ α = 0 ∨ α = -2 := by
  rw [compiledGadget_2x2_det]
  constructor
  · intro h
    have hprod : α * (α + 2) = 0 := h
    rcases mul_eq_zero.mp hprod with h | h
    · left; exact h
    · right; linarith
  · rintro (rfl | rfl) <;> ring

/-- **Det-zero iff for the 3×3 compiled gadget.**

For every coupling `α : ℝ`, the determinant of `compiledGadget α 3`
vanishes if and only if `α = 0` or `α = -3`.

The proof rewrites the determinant via the closed form
`(compiledGadget α 3).det = α * (α + 3)^2` from
`compiledGadget_3x3_det` and reduces `α * (α + 3)^2 = 0` to a
disjunction via `mul_eq_zero` together with `pow_eq_zero_iff`. -/
theorem compiledGadget_3_det_zero_iff (α : ℝ) :
    (compiledGadget α 3).det = 0 ↔ α = 0 ∨ α = -3 := by
  rw [compiledGadget_3x3_det]
  constructor
  · intro h
    have hprod : α * (α + 3) ^ 2 = 0 := h
    rcases mul_eq_zero.mp hprod with h | h
    · left; exact h
    · right
      have hbase : α + 3 = 0 := by
        have htwo : (2 : ℕ) ≠ 0 := by decide
        exact (pow_eq_zero_iff htwo).mp h
      linarith
  · rintro (rfl | rfl) <;> ring

end PallLean.Paper93.DeepMath.PathB.Positroid
