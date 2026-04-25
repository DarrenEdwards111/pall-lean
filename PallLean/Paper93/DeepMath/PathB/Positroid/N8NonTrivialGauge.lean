import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Non-trivial PosDef witness at `n = 8` (Path B Positroid layer)

This file packages the existence of a positive-definite, non-identity
real `8 × 8` matrix from the Path B compiled-gadget API. Concretely,
for `α = 1` and `n = 8`, the compiled gadget

    compiledGadget 1 8 = 1 • I + L_{K_8}

is:

* **positive definite**, by `compiledGadget_posDef` applied at
  `α = 1 > 0` and `1 ≤ 8`; and

* **not equal to the identity matrix**, by `compiledGadget_ne_identity`
  applied at `α = 1` and `2 ≤ 8` (its `(0,1)` off-diagonal entry is
  `−1`, while the identity matrix has `0` there).

Combining these yields the existence statement
`exists_nonidentity_posDef_n8`: there is an `8 × 8` real matrix that
is `PosDef` and not the identity. This is the `n = 8` instance of the
"non-trivial PosDef gauge" pattern used in the Positroid layer.

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- **Conjunction form, `n = 8`, `α = 1`.**

The `8 × 8` compiled gadget at `α = 1` is simultaneously positive
definite and not equal to the identity matrix on `Fin 8`. -/
theorem compiledGadget_8x8_alpha_one_posDef_nonidentity :
    (compiledGadget 1 8).PosDef ∧
    compiledGadget 1 8 ≠ (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  refine ⟨?_, ?_⟩
  · exact compiledGadget_posDef 1 8 one_pos (by norm_num)
  · exact compiledGadget_ne_identity 1 8 (by norm_num)

/-- **Existence of a non-identity PosDef `8 × 8` matrix.**

There exists a real `8 × 8` matrix that is positive definite and not
equal to the identity. The witness is `compiledGadget 1 8`, with
`PosDef` from `compiledGadget_posDef 1 8 one_pos (by norm_num)` and
non-identity from `compiledGadget_ne_identity 1 8 (by norm_num)`. -/
theorem exists_nonidentity_posDef_n8 :
    ∃ A : Matrix (Fin 8) (Fin 8) ℝ,
      A.PosDef ∧ A ≠ (1 : Matrix (Fin 8) (Fin 8) ℝ) :=
  ⟨compiledGadget 1 8, compiledGadget_posDef 1 8 one_pos (by norm_num),
   compiledGadget_ne_identity 1 8 (by norm_num)⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
