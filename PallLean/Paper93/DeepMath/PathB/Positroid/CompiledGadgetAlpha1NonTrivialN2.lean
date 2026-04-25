import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2NotIdentity
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Non-triviality of the compiled gadget for `α = 1` at `n = 2`

For the simpler choice `α = 1`, the 2×2 compiled gadget
`compiledGadget 1 2 = 1 • I + L_{K_2}` evaluates to the matrix

```
    ⎡ 2   −1 ⎤
    ⎣ −1   2 ⎦
```

In this file we package the following three observations as a single
summary theorem:

* It is **not the identity**: the off-diagonal `(0,1)` entry is `−1`,
  whereas the identity matrix has off-diagonal entry `0`. This is the
  content of `compiledGadget_2x2_ne_identity` specialised at `α = 1`.

* Its **determinant equals `3`**: by the closed form
  `det(compiledGadget α 2) = α (α + 2)` from
  `compiledGadget_2x2_det`, evaluating at `α = 1` yields `1 * (1 + 2) = 3`.

* It is **positive definite**: by `compiledGadget_posDef` with
  `0 < 1` (`one_pos`) and `1 ≤ 2`, the gadget is `PosDef`.

In particular, since the determinant is `3 ≠ 1`, this matrix is **not**
a gauge for `satFamily 2` (whose univ-minor requires determinant `1`),
even though it is a perfectly valid PosDef witness.

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- For `n = 2` and `α = 1`, `compiledGadget 1 2` is **not** the identity.

This is the specialisation at `α = 1` of `compiledGadget_2x2_ne_identity`
(which holds for every real `α`). -/
theorem compiledGadget_1_2_ne_identity :
    compiledGadget 1 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  compiledGadget_2x2_ne_identity 1

/-- For `n = 2` and `α = 1`, the determinant of `compiledGadget 1 2`
equals `3`.

This follows from the closed form
`(compiledGadget α 2).det = α * (α + 2)` (via `compiledGadget_2x2_det`)
specialised at `α = 1`: `1 * (1 + 2) = 3`. -/
theorem compiledGadget_1_2_det :
    (compiledGadget 1 2).det = 3 := by
  rw [compiledGadget_2x2_det]
  norm_num

/-- For `n = 2` and `α = 1`, `compiledGadget 1 2` is positive definite.

This is `compiledGadget_posDef` applied at `α = 1`, `n = 2`, with
the hypotheses `0 < 1` (`one_pos`) and `1 ≤ 2`. -/
theorem compiledGadget_1_2_posDef :
    (compiledGadget 1 2).PosDef :=
  compiledGadget_posDef 1 2 one_pos (by norm_num)

/-- **Summary theorem for `α = 1`, `n = 2`.**

The 2×2 compiled gadget at `α = 1` is simultaneously:

* not equal to the identity matrix,
* of determinant `3`, and
* positive definite.

In particular, since its determinant is `3 ≠ 1`, this matrix is **not**
a gauge for `satFamily 2` (which would require the univ-minor to be
`1`). The non-trivial PosDef witness with the correct determinant
`α (α + 2) = 1` requires the larger value `α = √2 − 1`; here we
record that even the simpler choice `α = 1` already produces a
genuinely non-identity PosDef matrix. -/
theorem compiledGadget_1_2_summary :
    compiledGadget 1 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    (compiledGadget 1 2).det = 3 ∧
    (compiledGadget 1 2).PosDef :=
  ⟨compiledGadget_1_2_ne_identity,
   compiledGadget_1_2_det,
   compiledGadget_1_2_posDef⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
