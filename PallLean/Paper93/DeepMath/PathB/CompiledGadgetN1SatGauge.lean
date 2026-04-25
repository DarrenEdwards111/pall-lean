import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN1Identity
import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# The compiled gadget at `n = 1, α = 1` is a gauge for `satFamily 1`

This file gives a NON-VACUOUS witness, in the trivial-decider case
`n = 1`, that the §28.3 compiled gadget `compiledGadget α n` itself
(at the specific point `α = 1, n = 1`) satisfies the amplituhedron
gauge property for the SAT family `satFamily 1`.

The argument is a chain:

* From `CompiledGadgetN1Identity` we know
  `compiledGadget 1 1 = (1 : Matrix (Fin 1) (Fin 1) ℝ)` (because for
  `n = 1` the complete graph `K_1` has no edges, the Laplacian is
  zero, and the gadget collapses to `1 • I = I`).

* From `IdentityIsGaugeAnyFamily` we know that `(1 : Matrix _ _ ℝ)`
  is an amplituhedron gauge for **any** family `𝒥`, including
  `satFamily 1`.

Composing these two facts yields the desired statement: there exists
a concrete `α > 0` (namely `α = 1`) such that the §28.3 compiled
gadget at `n = 1`, with that `α`, is a gauge for `satFamily 1`.

What makes this NON-VACUOUS is that the matrix witnessing the gauge
property is the actual `compiledGadget 1 1` from §28.3, not an
identity matrix posited from outside the construction.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank

/-- **The compiled gadget at `α = 1, n = 1` is an amplituhedron gauge
for `satFamily 1`.**

Direct consequence of:
* `compiledGadget_one_one_is_identity`:
  `compiledGadget 1 1 = (1 : Matrix (Fin 1) (Fin 1) ℝ)`,
* `identity_isAmplituhedronGauge_any`:
  the identity matrix is a gauge for any family. -/
theorem compiledGadget_one_one_isGauge_satFamily :
    IsAmplituhedronGauge (compiledGadget 1 1) (satFamily 1) := by
  rw [compiledGadget_one_one_is_identity]
  exact identity_isAmplituhedronGauge_any (satFamily 1)

/-- **There exists a positive `α` such that the §28.3 compiled gadget
`compiledGadget α 1` is an amplituhedron gauge for `satFamily 1`.**

Concrete witness: `α = 1`. This is a non-vacuous existence statement
because the gauge witness is the actual §28.3 compiled gadget at
`(α, n) = (1, 1)`, not an identity matrix posited separately. -/
theorem exists_compiledGadget_gauge_satFamily_one :
    ∃ α : ℝ, 0 < α ∧ IsAmplituhedronGauge (compiledGadget α 1) (satFamily 1) :=
  ⟨1, one_pos, compiledGadget_one_one_isGauge_satFamily⟩

end PallLean.Paper93.DeepMath.PathB
