import PallLean.Paper93.DeepMath.AlgebraicSPDP.NWProjectedDerivativeIdentity
import Mathlib.Data.ZMod.Basic

/-!
# Concrete NW(4,5,2) SPDP Lower Bound

This file instantiates the general NW projected-derivative identity at the
first nontrivial finite-field example used by the diagnostics:

* points: `Fin 4`;
* values: `ZMod 5`;
* labels: affine maps `x ↦ c₀ + c₁ x` over `ZMod 5`, hence `25` labels;
* derivative window: `{0,1}`;
* ambient variables: the `20` pairs `(point,value)`.

The result is a standalone numeric lower bound on the actual project
`SPDP.spdpRank` of the concrete encoded NW polynomial.
-/

namespace PallLean.Paper93.DeepMath.AlgebraicSPDP

open scoped BigOperators

namespace NW452

abbrev Point := Fin 4
abbrev Value := ZMod 5
abbrev Label := ZMod 5 × ZMod 5

/-- Encode the `4 × 5` point/value grid into `20` ambient variables. -/
def enc (z : Point × Value) : Fin 20 :=
  ⟨z.1.val * 5 + z.2.val, by
    have hx : z.1.val < 4 := z.1.isLt
    have hv : z.2.val < 5 := ZMod.val_lt z.2
    omega⟩

/-- The affine degree-`< 2` code over `ZMod 5`, restricted to four points. -/
def code (a : Label) (x : Point) : Value :=
  a.1 + a.2 * (x.val : ZMod 5)

/-- The derivative window `{0,1}`. -/
def D : Finset Point :=
  {0, 1}

/-- The loose unshifted/window-row support count for this instance. -/
def support : NWLeadingSupportData where
  basePartialRows := 25
  legalShiftRows := 1
  collisionDefect := 0

theorem enc_injective : Function.Injective enc := by
  decide

theorem code_injective : Function.Injective code := by
  decide

theorem D_card : D.card = 2 := by
  decide

theorem support_lower_le_labels :
    support.lower <= Fintype.card Label := by
  decide

theorem D_large : 1 < D.card := by
  decide

theorem outside_large :
    1 < (Finset.univ.filter fun x : Point => x ∉ D).card := by
  decide

theorem low_agreement :
    ∀ a b : Label, a ≠ b ->
      (nwAgreementSet code a b).card <= 1 := by
  decide

/-- Concrete independence certificate for `NW_{4,5,2}` at `(κ,ℓ)=(2,0)`. -/
noncomputable def certificate :
    NWSPDPIndependenceCertificate 20 4 2 0 :=
  NWSPDPIndependenceCertificate.ofLowAgreementNWPolynomial_injective
    (support := support)
    (enc := enc)
    (code := code)
    (D := D)
    (overlapBound := 1)
    (support_lower_le_labels := support_lower_le_labels)
    (hD := D_large)
    (hOutside := outside_large)
    (hlow := low_agreement)
    (hDcard := D_card)
    (henc := enc_injective)
    (hcode := code_injective)

/-- The standalone numeric lower bound certified by the concrete instance. -/
theorem spdpRank_nw452_ge_25 :
    25 <= SPDP.spdpRank 2 0 (nwMvPolynomial enc code) := by
  simpa [certificate, support, NWLeadingSupportData.lower] using
    certificate.support_lower_le_rank

/-! ## Axiom audit -/

#print axioms enc_injective
#print axioms code_injective
#print axioms low_agreement
#print axioms certificate
#print axioms spdpRank_nw452_ge_25

end NW452

end PallLean.Paper93.DeepMath.AlgebraicSPDP
