import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Non-identity `PosDef` witness from the compiled gadget at `n = 7`

This kernel-only file constructs a *non-identity* positive-definite
witness from the Path B compiled gadget `compiledGadget α 7 = α • I + L_{K_7}`
at `n = 7`, mirroring the `n = 6` analogue.

As with the smaller-`n` analogues (`N4NonTrivialGauge.lean`,
`N5NonTrivialGauge.lean`), we do **not** claim `det = 1` here. The
closed-form determinant `(compiledGadget α 7).det = α (α + 7)^6` is not
yet proved kernel-only at this level, so we cannot package an
IVT-witnessed root into a `det = 1` certification. Instead, we record
the two structural facts that are available:

* For `α > 0` and `n = 7`, `compiledGadget α 7` is `PosDef` (by
  `compiledGadget_posDef`, since `α > 0` and `1 ≤ 7`).
* For any `α : ℝ` and `n = 7`, `compiledGadget α 7 ≠ I` (by
  `compiledGadget_ne_identity`, since `2 ≤ 7`; the off-diagonal
  `(0, 1)` entry is `-1`, not `0`).

In particular, for `α = 1` we obtain a concrete non-identity `PosDef`
matrix on `Fin 7`, witnessing the existence of a non-trivial gauge
(prior to the determinant constraint) at the truncated `n = 7` level
of paper §28.3.

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- For `n = 7` and `α = 1`, the compiled gadget `compiledGadget 1 7` is
positive definite and is not the identity matrix.

* PosDef: by `compiledGadget_posDef` with `0 < 1` and `1 ≤ 7`.
* Non-identity: by `compiledGadget_ne_identity` with `2 ≤ 7`. -/
theorem compiledGadget_7x7_alpha_one_posDef_nonidentity :
    (compiledGadget 1 7).PosDef ∧
    compiledGadget 1 7 ≠ (1 : Matrix (Fin 7) (Fin 7) ℝ) := by
  refine ⟨?_, ?_⟩
  · exact compiledGadget_posDef 1 7 one_pos (by norm_num)
  · exact compiledGadget_ne_identity 1 7 (by norm_num)

/-- **Existence of a non-identity `PosDef` 7×7 matrix from the §28.3
construction.**

Specialising the previous theorem to `α = 1`, the matrix
`compiledGadget 1 7` is `PosDef` and is not the identity. This
witnesses the existence of a non-trivial (off-identity) positive
definite matrix on `Fin 7` arising from the Path B compiled-gadget
construction at the truncated `n = 7` level. -/
theorem exists_nonidentity_posDef_n7_compiledGadget :
    ∃ A : Matrix (Fin 7) (Fin 7) ℝ,
      A.PosDef ∧ A ≠ (1 : Matrix (Fin 7) (Fin 7) ℝ) :=
  ⟨compiledGadget 1 7, compiledGadget_posDef 1 7 one_pos (by norm_num),
   compiledGadget_ne_identity 1 7 (by norm_num)⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
