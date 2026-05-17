import PallLean.Paper93.DeepMath.PathC.PiPlusProjectedPayloadCloseout
import PallLean.Paper93.Wiring.ConcreteW

/-!
# Concrete `W` fields for the projected Pi+ payload

This file discharges the two purely structural `W` payload fields
unconditionally for the canonical paper-scale concrete per-type spaces:

* `W_finite`
* `W_dim ≤ 3`

It deliberately does not claim the active-data field.  That remains a real
payload theorem: the existing endpoint-augmented active progress proves useful
factor-derivative transport, but the same-profile shift/`mlProj` closure is
obstructed and must be replaced by the charged/target-profile machinery.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Paper283
open PaperFaithfulSeparation
open TuringMachine
open SymmetricPowerBound
open WithinProfileBound

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- Canonical paper-scale concrete `W` using the standard cast embedding
`Fin 4 ↪ Fin (2^804)`. -/
noncomputable def paperScaleConcreteW :
    ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ) :=
  fun τ => PallLean.Paper93.Wiring.concreteW
    (2 ^ 804) paperScale_two_pow_804_ge_four
    (Fin.castLEEmb paperScale_two_pow_804_ge_four) τ

/-- First discharged structural payload field: the canonical concrete `W` is
finite in every constraint type. -/
theorem paperScaleConcreteW_finite :
    ∀ τ, Module.Finite ℚ ↥(paperScaleConcreteW τ) := by
  intro τ
  unfold paperScaleConcreteW
  exact PallLean.Paper93.Wiring.concreteW_finite
    (2 ^ 804) paperScale_two_pow_804_ge_four
    (Fin.castLEEmb paperScale_two_pow_804_ge_four) τ

/-- Second discharged structural payload field: the canonical concrete `W` has
per-type dimension at most three. -/
theorem paperScaleConcreteW_dim_le_three :
    ∀ τ, Module.finrank ℚ ↥(paperScaleConcreteW τ) ≤ 3 := by
  intro τ
  unfold paperScaleConcreteW
  exact PallLean.Paper93.Wiring.concreteW_finrank_le_three
    (2 ^ 804) paperScale_two_pow_804_ge_four
    (Fin.castLEEmb paperScale_two_pow_804_ge_four) τ

/-- A compact package of the two now-discharged `W` fields, ready to plug into
future projected-payload constructors once the active-data theorem is repaired. -/
structure PaperScaleConcreteWStructuralFields : Type where
  W : ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ)
  W_eq : W = paperScaleConcreteW
  W_finite : ∀ τ, Module.Finite ℚ ↥(W τ)
  W_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3

/-- The concrete structural `W` payload fields are unconditionally inhabited. -/
noncomputable def paperScaleConcreteWStructuralFields :
    PaperScaleConcreteWStructuralFields where
  W := paperScaleConcreteW
  W_eq := rfl
  W_finite := paperScaleConcreteW_finite
  W_dim := paperScaleConcreteW_dim_le_three

/-! ## Axiom audit anchors -/

#print axioms paperScaleConcreteW_finite
#print axioms paperScaleConcreteW_dim_le_three
#print axioms paperScaleConcreteWStructuralFields

end PallLean.Paper93.DeepMath.PathC
