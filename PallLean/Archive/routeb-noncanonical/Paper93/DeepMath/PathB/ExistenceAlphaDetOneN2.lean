import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.Sqrt2MinusOnePos
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Existence (and uniqueness) of a positive `α` with `det (compiledGadget α 2) = 1`

For the 2×2 compiled gadget we have the closed form

```
(compiledGadget α 2).det = α * (α + 2)
```

(`compiledGadget_2x2_det`). Setting this equal to `1` gives the
quadratic equation

```
α² + 2α − 1 = 0,
```

whose roots are `α = -1 ± √2`. The positive root is

```
α = √2 − 1 ≈ 0.414,
```

and it is the unique positive solution.

This file provides:

* `exists_alpha_compiledGadget_2x2_det_one`: a direct construction
  (NOT via the intermediate value theorem) of a positive `α` with
  `(compiledGadget α 2).det = 1`, namely `α = √2 − 1`.

* `alpha_pos_root_unique`: uniqueness of the positive root, via the
  factorisation `(α + 1)² = 2` and strict positivity of `α + 1`.

Both results are kernel-only (axioms: `propext`, `Classical.choice`,
`Quot.sound`).

Namespace: `PallLean.Paper93.DeepMath.PathB`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open Matrix

/-- **Existence of a positive coupling `α` with `det (compiledGadget α 2) = 1`.**

Direct construction: take `α := Real.sqrt 2 - 1`. Positivity follows from
`1 < Real.sqrt 2`, and the determinant computation uses
`compiledGadget_2x2_det` together with `(√2)² = 2`. -/
theorem exists_alpha_compiledGadget_2x2_det_one :
    ∃ α : ℝ, 0 < α ∧ (compiledGadget α 2).det = 1 := by
  refine ⟨Real.sqrt 2 - 1, ?_, ?_⟩
  · -- `0 < √2 - 1`: since `√2 > 1`.
    have h : (1 : ℝ) < Real.sqrt 2 := by
      have h1 : Real.sqrt 1 < Real.sqrt 2 := by
        apply Real.sqrt_lt_sqrt
        · norm_num
        · norm_num
      rwa [Real.sqrt_one] at h1
    linarith
  · -- `(compiledGadget (√2 - 1) 2).det = 1`.
    rw [compiledGadget_2x2_det]
    -- Goal: `(√2 - 1) * ((√2 - 1) + 2) = 1`.
    have h : (Real.sqrt 2 - 1) + 2 = Real.sqrt 2 + 1 := by ring
    rw [h]
    -- Goal: `(√2 - 1) * (√2 + 1) = 1`.
    have h2 : (Real.sqrt 2 - 1) * (Real.sqrt 2 + 1)
        = (Real.sqrt 2) ^ 2 - 1 := by ring
    rw [h2]
    -- Goal: `(√2)^2 - 1 = 1`.
    have h3 : (Real.sqrt 2) ^ 2 = 2 :=
      Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)
    rw [h3]
    norm_num

/-- **Uniqueness of the positive root of `α² + 2α − 1 = 0`.**

If `α > 0` and `(compiledGadget α 2).det = 1`, then `α = √2 − 1`.

The proof uses the closed form `det = α(α + 2)` to reduce to the
quadratic `α² + 2α − 1 = 0`. Rewriting as `(α + 1)² = 2` and using
`α + 1 > 0` (since `α > 0`), we extract the positive square root
`α + 1 = √2`, hence `α = √2 − 1`. -/
theorem alpha_pos_root_unique (α : ℝ) (hα : 0 < α)
    (hdet : (compiledGadget α 2).det = 1) :
    α = Real.sqrt 2 - 1 := by
  rw [compiledGadget_2x2_det] at hdet
  -- `hdet : α * (α + 2) = 1`, so `α² + 2α - 1 = 0`.
  have h_quad : α ^ 2 + 2 * α - 1 = 0 := by nlinarith [hdet]
  -- Rewrite as `(α + 1)^2 = 2`.
  have h1 : (α + 1) ^ 2 = 2 := by nlinarith [h_quad]
  -- `α + 1 > 0` since `α > 0`.
  have h2 : 0 < α + 1 := by linarith
  -- Extract positive square root: `α + 1 = √2`.
  have h3 : α + 1 = Real.sqrt 2 := by
    -- `α + 1 = √((α + 1)^2) = √2`.
    have h4 : Real.sqrt ((α + 1) ^ 2) = α + 1 :=
      Real.sqrt_sq (le_of_lt h2)
    have h5 : Real.sqrt ((α + 1) ^ 2) = Real.sqrt 2 := by
      rw [h1]
    linarith [h4, h5]
  linarith

end PallLean.Paper93.DeepMath.PathB
