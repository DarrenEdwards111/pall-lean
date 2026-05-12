import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Non-trivial PosDef witness at `n = 9` (Path B Positroid layer)

This file packages the existence of a positive-definite, non-identity
real `9 × 9` matrix from the Path B compiled-gadget API. Concretely,
for `α = 1` and `n = 9`, the compiled gadget

    compiledGadget 1 9 = 1 • I + L_{K_9}

is:

* **positive definite**, by `compiledGadget_posDef` applied at
  `α = 1 > 0` and `1 ≤ 9`; and

* **not equal to the identity matrix**, by `compiledGadget_ne_identity`
  applied at `α = 1` and `2 ≤ 9` (its `(0,1)` off-diagonal entry is
  `−1`, while the identity matrix has `0` there).

Combining these yields the existence statement
`exists_nonidentity_posDef_n9`: there is a `9 × 9` real matrix that
is `PosDef` and not the identity. This is the `n = 9` instance of the
"non-trivial PosDef gauge" pattern used in the Positroid layer.

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- **Conjunction form, `n = 9`, `α = 1`.**

The `9 × 9` compiled gadget at `α = 1` is simultaneously positive
definite and not equal to the identity matrix on `Fin 9`. -/
theorem compiledGadget_9x9_alpha_one_posDef_nonidentity :
    (compiledGadget 1 9).PosDef ∧
    compiledGadget 1 9 ≠ (1 : Matrix (Fin 9) (Fin 9) ℝ) := by
  refine ⟨?_, ?_⟩
  · exact compiledGadget_posDef 1 9 one_pos (by norm_num)
  · exact compiledGadget_ne_identity 1 9 (by norm_num)

/-- **Existence of a non-identity PosDef `9 × 9` matrix.**

There exists a real `9 × 9` matrix that is positive definite and not
equal to the identity. The witness is `compiledGadget 1 9`, with
`PosDef` from `compiledGadget_posDef 1 9 one_pos (by norm_num)` and
non-identity from `compiledGadget_ne_identity 1 9 (by norm_num)`. -/
theorem exists_nonidentity_posDef_n9 :
    ∃ A : Matrix (Fin 9) (Fin 9) ℝ,
      A.PosDef ∧ A ≠ (1 : Matrix (Fin 9) (Fin 9) ℝ) :=
  ⟨compiledGadget 1 9, compiledGadget_posDef 1 9 one_pos (by norm_num),
   compiledGadget_ne_identity 1 9 (by norm_num)⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
