import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.PathB.Sqrt2MinusOnePos
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Determinant of the 2×2 compiled gadget at the critical coupling `α = √2 − 1`

We specialise `compiledGadget_2x2_det` to the coupling `α = Real.sqrt 2 - 1`,
which is the unique positive root of `α² + 2α − 1 = 0`. Using the
closed-form determinant `det = α(α + 2)`, the conjugate identity
`(√2 − 1)(√2 + 1) = (√2)² − 1 = 2 − 1 = 1` (from
`Sqrt2MinusOnePos.lean`), and the rewrite `(√2 − 1) + 2 = √2 + 1`,
we obtain

`(compiledGadget (√2 − 1) 2).det = 1`.

We additionally derive the corollary that
`compiledGadget (√2 − 1) 2` is positive definite, by combining the
strict positivity `√2 − 1 > 0` (`sqrt_two_minus_one_pos`) with the
general `compiledGadget_posDef` lemma at `n = 2`.

Namespace: `PallLean.Paper93.DeepMath.PathB`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open Matrix

/-- **Determinant of the 2×2 compiled gadget at `α = √2 − 1` equals `1`.**

Specialising the closed-form formula
`(compiledGadget α 2).det = α * (α + 2)` (from `compiledGadget_2x2_det`)
to `α = Real.sqrt 2 - 1`, we obtain

`(Real.sqrt 2 - 1) * ((Real.sqrt 2 - 1) + 2)
   = (Real.sqrt 2 - 1) * (Real.sqrt 2 + 1)
   = (Real.sqrt 2)² − 1
   = 2 − 1 = 1`.

The proof rewrites with `compiledGadget_2x2_det`, simplifies the second
factor algebraically via `ring` to `Real.sqrt 2 + 1`, and then invokes
`sqrt_two_minus_one_times_sqrt_two_plus_one_eq_one`
(from `Sqrt2MinusOnePos.lean`). -/
theorem compiledGadget_2x2_det_at_sqrt2 :
    (compiledGadget (Real.sqrt 2 - 1) 2).det = 1 := by
  rw [compiledGadget_2x2_det]
  -- Goal: (Real.sqrt 2 - 1) * (Real.sqrt 2 - 1 + 2) = 1
  have h1 : Real.sqrt 2 - 1 + 2 = Real.sqrt 2 + 1 := by ring
  rw [h1]
  -- Goal: (Real.sqrt 2 - 1) * (Real.sqrt 2 + 1) = 1
  exact sqrt_two_minus_one_times_sqrt_two_plus_one_eq_one

/-- **Positive definiteness of the 2×2 compiled gadget at `α = √2 − 1`.**

Combining the positivity `0 < Real.sqrt 2 - 1` (from
`sqrt_two_minus_one_pos`) with the general
`compiledGadget_posDef α n hα hn` lemma at `n = 2`, we obtain that
`compiledGadget (Real.sqrt 2 - 1) 2` is `PosDef`. -/
theorem compiledGadget_2x2_at_sqrt2_posDef :
    (compiledGadget (Real.sqrt 2 - 1) 2).PosDef := by
  apply compiledGadget_posDef
  · exact sqrt_two_minus_one_pos
  · norm_num

end PallLean.Paper93.DeepMath.PathB
