import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN1Identity
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN1SatGauge
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2NotIdentity
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# The `n = 1` case: compiled-gadget collapse to identity (documentation)

This file documents, in a kernel-only Lean 4 module, the structural
phenomenon that the §28.3 compiled gadget `compiledGadget α n`
*collapses* to the identity matrix at `n = 1` (with `α = 1`).

## Why does it collapse?

The compiled gadget is defined as
`compiledGadget α n = α • I + L_{K_n}`,
where `L_{K_n}` is the graph Laplacian of the complete graph on
`Fin n`. For `n = 1`, the complete graph `K_1` has **no edges** (no
self-loops by convention), so `completeAdj 1 = 0` and consequently
`L_{K_1} = 0`. The whole Laplacian contribution drops out, leaving
`compiledGadget α 1 = α • I`. At the canonical point `α = 1` this
becomes the identity matrix.

This collapse means that the "non-trivial witness" provided by the
§28.3 compiled gadget at `n = 1` is *degenerate*: the gauge witness is
literally the identity matrix, which is a trivial gauge for any
family. The witness still satisfies `IsAmplituhedronGauge` for
`satFamily 1`, but the matrix it exhibits is the same as the
identity-based witness `identity_isAmplituhedronGauge_any`.

In contrast, at `n = 2` the complete graph `K_2` has a single edge,
so `L_{K_2} ≠ 0`, and the compiled gadget is genuinely *non-identity*
at every choice of `α`. In particular at the conjugate-root coupling
`α = √2 − 1` the gauge witness `compiledGadget (√2 − 1) 2` is a
genuinely non-trivial matrix that is not equal to the identity.

## Contents

This file packages the relevant facts as a single side-by-side
comparison:

* `n1_compiledGadget_collapse`: at `n = 1, α = 1`, the compiled gadget
  is exactly the identity matrix on `Fin 1`.
* `n1_compiledGadget_isGauge_satFamily`: at `n = 1, α = 1`, the
  compiled gadget *is* (degenerately) a gauge for `satFamily 1`.
* `n2_compiledGadget_nontrivial`: at `n = 2, α = √2 − 1`, the compiled
  gadget is **not** the identity matrix.
* `n1_vs_n2_gauge_witness_comparison`: side-by-side conjunction
  recording the collapse at `n = 1` and the non-triviality at `n = 2`.

All proofs are direct reductions to the upstream §28.3 lemmas and use
only the kernel axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- The `n = 1` compiledGadget at `α = 1` IS the identity matrix
(collapse).

This is the structural collapse: at `n = 1` the complete graph `K_1`
has no edges, so `L_{K_1} = 0` and `compiledGadget 1 1 = 1 • I = I`.
Direct restatement of `compiledGadget_one_one_is_identity`. -/
theorem n1_compiledGadget_collapse :
    compiledGadget 1 1 = (1 : Matrix (Fin 1) (Fin 1) ℝ) :=
  compiledGadget_one_one_is_identity

/-- The `n = 1` case: `compiledGadget 1 1` IS a gauge for
`satFamily 1` (degenerate but valid).

Even though the gauge witness collapses to the identity matrix, the
amplituhedron gauge property still holds for `satFamily 1`. Direct
restatement of `compiledGadget_one_one_isGauge_satFamily`. -/
theorem n1_compiledGadget_isGauge_satFamily :
    IsAmplituhedronGauge (compiledGadget 1 1) (satFamily 1) :=
  compiledGadget_one_one_isGauge_satFamily

/-- The `n = 2` case: `compiledGadget (√2 − 1) 2` is **NOT** the
identity matrix (genuine non-trivial witness).

In contrast to the `n = 1` collapse, the §28.3 compiled gadget at
`n = 2` is genuinely distinct from the identity for every `α`,
because its `(0,1)` off-diagonal entry is `-1` (independent of `α`),
whereas the identity has off-diagonal entry `0`. Direct restatement
of `compiledGadget_2x2_ne_identity` at the canonical conjugate-root
coupling `α = √2 − 1`. -/
theorem n2_compiledGadget_nontrivial :
    compiledGadget (Real.sqrt 2 - 1) 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)

/-- **Comparison theorem.** Side-by-side conjunction recording the
distinct behaviour of the §28.3 compiled gadget at `n = 1` and `n = 2`:

* at `n = 1` the gauge witness collapses to the identity matrix (the
  Laplacian of `K_1` vanishes); while
* at `n = 2` the gauge witness `compiledGadget (√2 − 1) 2` is
  genuinely non-trivial (it differs from the identity at the `(0,1)`
  off-diagonal entry).

This packages `compiledGadget_one_one_is_identity` and
`compiledGadget_2x2_ne_identity` together as a single conjunction
documenting the contrast between the degenerate and non-trivial
regimes of the compiled-gadget witness. -/
theorem n1_vs_n2_gauge_witness_comparison :
    -- n = 1: collapse to identity
    compiledGadget 1 1 = (1 : Matrix (Fin 1) (Fin 1) ℝ) ∧
    -- n = 2: non-trivial
    compiledGadget (Real.sqrt 2 - 1) 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  ⟨compiledGadget_one_one_is_identity,
   compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
