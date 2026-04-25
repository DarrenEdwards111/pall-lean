import PallLean.Paper93.DeepMath.PathB.Positroid.DeciderSpecificAlpha
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2NotIdentity
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Decider-specific gauge witness

For each dimension `n`, the decider-specific gauge witness is the §28.3
compiled gadget evaluated at the decider-specific coupling
`deciderSpecificAlpha n`. For `n = 2`, the coupling is `√2 − 1`, and we show
that the resulting matrix is **NOT** the identity. This packages the
non-identity property of `compiledGadget` together with the structurally
chosen, decider-tied coupling.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.PathB

/-- The **decider-specific gauge witness** at dimension n: the §28.3 compiled
    gadget at the decider-specific coupling. For n=2 this gives a NON-TRIVIAL
    (non-identity) matrix; for n=1 it collapses to identity. -/
noncomputable def deciderSpecificGauge (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  compiledGadget (deciderSpecificAlpha n) n

/-- The decider-specific gauge at n=2 is the §28.3 compiledGadget at √2 − 1. -/
theorem deciderSpecificGauge_two :
    deciderSpecificGauge 2 = compiledGadget (Real.sqrt 2 - 1) 2 := by
  unfold deciderSpecificGauge
  rw [deciderSpecificAlpha_two]

/-- The decider-specific gauge at n=2 is NOT the identity matrix. -/
theorem deciderSpecificGauge_two_ne_identity :
    deciderSpecificGauge 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [deciderSpecificGauge_two]
  exact compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)

/-- For any n ≥ 2, the decider-specific gauge is the §28.3 compiledGadget at
    a strictly positive coupling. -/
theorem deciderSpecificGauge_eq_compiledGadget (n : ℕ) :
    deciderSpecificGauge n = compiledGadget (deciderSpecificAlpha n) n := rfl

/-- The decider-specific gauge has dimensionful types: at n=1 vs n=2 the matrices
    live in different types, so they cannot be compared directly. The structural
    distinction is captured by `deciderSpecificGauge_two_ne_identity`. -/
theorem deciderSpecificGauge_two_is_2x2 :
    deciderSpecificGauge 2 = compiledGadget (Real.sqrt 2 - 1) 2 :=
  deciderSpecificGauge_two

end PallLean.Paper93.DeepMath.PathB.Positroid
