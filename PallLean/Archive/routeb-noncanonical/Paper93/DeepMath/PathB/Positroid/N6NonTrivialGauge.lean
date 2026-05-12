import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Non-identity `PosDef` witness from the compiled gadget at `n = 6`

This kernel-only file constructs a *non-identity* positive-definite
witness from the Path B compiled gadget `compiledGadget α 6 = α • I + L_{K_6}`
at `n = 6`.

As with the `n = 4` and `n = 5` analogues (`N4NonTrivialGauge.lean`,
`N5NonTrivialGauge.lean`), we do **not** claim `det = 1` here. The
closed-form determinant `(compiledGadget α 6).det = α (α + 6)^5` is not
yet proved kernel-only at this level, so we cannot package an
IVT-witnessed root into a `det = 1` certification. Instead, we record
the two structural facts that are available:

* For `α > 0` and `n = 6`, `compiledGadget α 6` is `PosDef` (by
  `compiledGadget_posDef`, since `α > 0` and `1 ≤ 6`).
* For any `α : ℝ` and `n = 6`, `compiledGadget α 6 ≠ I` (by
  `compiledGadget_ne_identity`, since `2 ≤ 6`; the off-diagonal
  `(0, 1)` entry is `-1`, not `0`).

In particular, for `α = 1` we obtain a concrete non-identity `PosDef`
matrix on `Fin 6`, witnessing the existence of a non-trivial gauge
(prior to the determinant constraint) at the truncated `n = 6` level.

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- For `n = 6` and `α = 1`, the compiled gadget `compiledGadget 1 6` is
positive definite and is not the identity matrix.

* PosDef: by `compiledGadget_posDef` with `0 < 1` and `1 ≤ 6`.
* Non-identity: by `compiledGadget_ne_identity` with `2 ≤ 6`. -/
theorem compiledGadget_6x6_alpha_one_posDef_nonidentity :
    (compiledGadget 1 6).PosDef ∧
    compiledGadget 1 6 ≠ (1 : Matrix (Fin 6) (Fin 6) ℝ) := by
  refine ⟨?_, ?_⟩
  · exact compiledGadget_posDef 1 6 one_pos (by norm_num)
  · exact compiledGadget_ne_identity 1 6 (by norm_num)

/-- **Existence of a non-identity `PosDef` 6×6 matrix from the §28.3
construction.**

The matrix `compiledGadget 1 6` is `PosDef` and is not the identity.
This witnesses the existence of a non-trivial (off-identity) positive
definite matrix on `Fin 6` arising from the Path B compiled-gadget
construction at the truncated `n = 6` level. -/
theorem exists_nonidentity_posDef_n6_compiledGadget :
    ∃ A : Matrix (Fin 6) (Fin 6) ℝ,
      A.PosDef ∧ A ≠ (1 : Matrix (Fin 6) (Fin 6) ℝ) :=
  ⟨compiledGadget 1 6, compiledGadget_posDef 1 6 one_pos (by norm_num),
   compiledGadget_ne_identity 1 6 (by norm_num)⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
