import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN2SatGauge
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2NotIdentity
import PallLean.Paper93.DeepMath.PathB.Sqrt2MinusOnePos
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Concrete `n = 2` SAT-decider tableau examples and their gauge witnesses

This file packages two **concrete** `n = 2` SAT-decider tableaux — the
all-zeros tableau `exampleZero2x2` and the all-ones tableau
`exampleAllOnes2x2` — together with non-trivial amplituhedron-gauge
witnesses for the `satFamily 2 = {∅, Finset.univ}` index family.

The witness is the §28.3 compiled gadget
`compiledGadget (Real.sqrt 2 − 1) 2`, which:

* is positive definite (via `compiledGadget_2x2_at_sqrt2_posDef`);
* satisfies the principal-minor identity over `satFamily 2` (via
  `compiledGadget_n2_isGauge_satFamily`);
* is genuinely **non-identity** (its `(0,1)` entry is `−1`, by
  `compiledGadget_2x2_ne_identity`).

These existential statements depend only on the dimension `n = 2` and on
the choice of `satFamily`, not on the particular row data of the
tableau. They are the structural "decider-tied" examples promised in
the Round-58 extraction story, restricted here to two concrete
two-by-two tableau instances.

The whole file is kernel-only: it uses only `propext`,
`Classical.choice`, and `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- A concrete 2×2 zero tableau example. -/
def exampleZero2x2 : SATDeciderTableau 2 2 :=
  SATDeciderTableau.zero 2 2

/-- A concrete 2×2 all-ones tableau example. -/
def exampleAllOnes2x2 : SATDeciderTableau 2 2 :=
  SATDeciderTableau.allOnes 2 2

/-- The zero tableau example admits a non-trivial gauge witness. -/
theorem exampleZero2x2_nontrivialGauge :
    ∃ A : Matrix (Fin 2) (Fin 2) ℝ,
      IsAmplituhedronGauge A (satFamily 2) ∧
      A ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  ⟨compiledGadget (Real.sqrt 2 - 1) 2,
   compiledGadget_n2_isGauge_satFamily,
   compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)⟩

/-- The all-ones tableau example admits a non-trivial gauge witness. -/
theorem exampleAllOnes2x2_nontrivialGauge :
    ∃ A : Matrix (Fin 2) (Fin 2) ℝ,
      IsAmplituhedronGauge A (satFamily 2) ∧
      A ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  ⟨compiledGadget (Real.sqrt 2 - 1) 2,
   compiledGadget_n2_isGauge_satFamily,
   compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)⟩

/-- For the example tableaus, the non-trivial witness is well-defined. -/
theorem n2_example_tableau_witnesses :
    (∃ A : Matrix (Fin 2) (Fin 2) ℝ,
      IsAmplituhedronGauge A (satFamily 2) ∧
      A ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (∃ A : Matrix (Fin 2) (Fin 2) ℝ,
      IsAmplituhedronGauge A (satFamily 2) ∧
      A ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) :=
  ⟨exampleZero2x2_nontrivialGauge, exampleAllOnes2x2_nontrivialGauge⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
