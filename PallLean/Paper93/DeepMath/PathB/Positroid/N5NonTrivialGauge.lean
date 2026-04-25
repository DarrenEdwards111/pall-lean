import PallLean.Paper93.DeepMath.PathB.Positroid.N5IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Non-identity `PosDef` witness from the compiled gadget at `n = 5`

This kernel-only file constructs a *non-identity* positive-definite
witness from the Path B compiled gadget `compiledGadget α 5 = α • I + L_{K_5}`
at `n = 5`.

As with the `n = 4` analogue (`N4NonTrivialGauge.lean`), we do **not**
claim `det = 1` here. The closed-form determinant
`(compiledGadget α 5).det = α (α + 5)^4` is not yet proved kernel-only
at this level, so we cannot package an IVT-witnessed root into a
`det = 1` certification. Instead, we record the two structural facts
that are available:

* For `α > 0` and `n = 5`, `compiledGadget α 5` is `PosDef` (by
  `compiledGadget_posDef`, since `α > 0` and `1 ≤ 5`).
* For any `α : ℝ` and `n = 5`, `compiledGadget α 5 ≠ I` (by
  `compiledGadget_ne_identity`, since `2 ≤ 5`; the off-diagonal
  `(0, 1)` entry is `-1`, not `0`).

In particular, for `α = 1` we obtain a concrete non-identity `PosDef`
matrix on `Fin 5`, witnessing the existence of a non-trivial gauge
(prior to the determinant constraint) at the truncated `n = 5` level.

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- For `n = 5` and `α = 1`, the compiled gadget `compiledGadget 1 5` is
positive definite and is not the identity matrix.

* PosDef: by `compiledGadget_posDef` with `0 < 1` and `1 ≤ 5`.
* Non-identity: by `compiledGadget_ne_identity` with `2 ≤ 5`. -/
theorem compiledGadget_5x5_alpha_one_posDef_nonidentity :
    (compiledGadget 1 5).PosDef ∧
    compiledGadget 1 5 ≠ (1 : Matrix (Fin 5) (Fin 5) ℝ) := by
  refine ⟨?_, ?_⟩
  · exact compiledGadget_posDef 1 5 one_pos (by norm_num : 1 ≤ 5)
  · exact compiledGadget_ne_identity 1 5 (by norm_num : 2 ≤ 5)

/-- For any `α > 0` at `n = 5`, the compiled gadget `compiledGadget α 5` is
positive definite and is not the identity matrix.

* PosDef: by `compiledGadget_posDef` with `hα` and `1 ≤ 5`.
* Non-identity: by `compiledGadget_ne_identity` with `2 ≤ 5`. -/
theorem compiledGadget_5x5_posDef_nonidentity (α : ℝ) (hα : 0 < α) :
    (compiledGadget α 5).PosDef ∧
    compiledGadget α 5 ≠ (1 : Matrix (Fin 5) (Fin 5) ℝ) := by
  refine ⟨?_, ?_⟩
  · exact compiledGadget_posDef α 5 hα (by norm_num : 1 ≤ 5)
  · exact compiledGadget_ne_identity α 5 (by norm_num : 2 ≤ 5)

/-- **Existence of a non-identity `PosDef` 5×5 matrix from the §28.3
construction.**

Specialising the previous theorem to `α = 1`, the matrix
`compiledGadget 1 5` is `PosDef` and is not the identity. This
witnesses the existence of a non-trivial (off-identity) positive
definite matrix on `Fin 5` arising from the Path B compiled-gadget
construction at the truncated `n = 5` level. -/
theorem exists_nonidentity_posDef_n5_compiledGadget :
    ∃ A : Matrix (Fin 5) (Fin 5) ℝ,
      A.PosDef ∧ A ≠ (1 : Matrix (Fin 5) (Fin 5) ℝ) := by
  refine ⟨compiledGadget 1 5, ?_, ?_⟩
  · exact compiledGadget_posDef 1 5 one_pos (by norm_num : 1 ≤ 5)
  · exact compiledGadget_ne_identity 1 5 (by norm_num : 2 ≤ 5)

end PallLean.Paper93.DeepMath.PathB.Positroid
