import PallLean.Paper93.DeepMath.PathB.ConcreteWShiftMlprojClosure
import PallLean.Paper93.DeepMath.PathB.AugmentedConcreteWH4
import PallLean.Paper93.DeepMath.PathB.AugmentedConcreteWI5
import PallLean.Paper93.DeepMath.PathB.ZeroProfileNonScalarClosure
import PallLean.Paper93.Paper283.RouteBRicherGaugePWindowCover
import PallLean.Paper93.Wiring.DischargeChain

/-!
# ConcreteW charged shift/mlProj closure route

This file records the corrected concreteW-facing reduction for the
shift/mlProj closure surface.  The key difference from
`ConcreteWShiftMlprojClosure` is that multiplication by `shift` is allowed to
move from a source derivative-count profile to a charged target profile before
`mlProj` is applied.  This avoids the raw same-profile I2 zero-profile
obstruction isolated in `ConcreteWShiftMlprojClosure.lean`.

The P-window bridge at the end uses the non-scalar zero-profile common-span
surface, so it does not ask for a singleton/template zero-profile collapse.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial SymmetricPowerBound
open WithinProfileBound MultilinearSPDP
open PallLean.Paper93
open PallLean.Paper93.Closure
open PallLean.Paper93.Spanning
open scoped BigOperators

attribute [local instance] Classical.dec

/-! ## ConcreteW charged I5 surface -/

/-- Charged shift closure specialised to the canonical concreteW family. -/
def ConcreteWChargedShiftClosure
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n) : Prop :=
  PerTypeChargedShiftClosure (n := n) charge (concreteWCanonical n hn4)

/-- Corrected charged shift/mlProj closure specialised to the canonical
concreteW family. -/
def ConcreteWShiftMlprojClosureCharged
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n) : Prop :=
  PerTypeShiftMlprojClosureCharged (n := n) charge
    (concreteWCanonical n hn4)

/-- Concrete I1, charged I2, and I3 compose to the corrected charged concreteW
I5 package. -/
theorem concreteW_shiftMlprojClosure_charged_of_components
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n)
    (hI1 : ConcreteWProductGrouping n hn4)
    (hI2c : ConcreteWChargedShiftClosure n hn4 charge)
    (hI3 : ConcreteWMlprojClosure n hn4) :
    ConcreteWShiftMlprojClosureCharged n hn4 charge :=
  perTypeShiftMlprojClosure_charged_discharged
    (n := n) charge (concreteWCanonical n hn4) hI1 hI2c hI3

/-- Same theorem with the target unfolded to the bridge's literal canonical
row-embedding family. -/
theorem concreteW_perTypeShiftMlprojClosure_charged_of_components
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n)
    (hI1 : ConcreteWProductGrouping n hn4)
    (hI2c : ConcreteWChargedShiftClosure n hn4 charge)
    (hI3 : ConcreteWMlprojClosure n hn4) :
    PerTypeShiftMlprojClosureCharged (n := n) charge
      (fun tau =>
        PallLean.Paper93.Wiring.concreteW n hn4 (Fin.castLEEmb hn4) tau) :=
  concreteW_shiftMlprojClosure_charged_of_components
    n hn4 charge hI1 hI2c hI3

/-! ## Endpoint-augmented charged I5 surface -/

/-- Charged shift closure specialised to the endpoint-augmented concreteW
family, the corrected H4 target for the canonical row. -/
def EndpointAugmentedConcreteWChargedShiftClosure
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n) : Prop :=
  PerTypeChargedShiftClosure (n := n) charge
    (endpointAugmentedConcreteW n hn4)

/-- Corrected charged shift/mlProj closure specialised to the
endpoint-augmented concreteW family. -/
def EndpointAugmentedConcreteWShiftMlprojClosureCharged
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n) : Prop :=
  PerTypeShiftMlprojClosureCharged (n := n) charge
    (endpointAugmentedConcreteW n hn4)

/-- Endpoint H4, charged I1/I2/I3, and mlProj closure compose to the corrected
charged I5 package at the endpoint-augmented concreteW family. -/
theorem endpointAugmentedConcreteW_shiftMlprojClosure_charged_of_components
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n)
    (hI1 :
      PerTypeProductGrouping (n := n) (endpointAugmentedConcreteW n hn4))
    (hI2c :
      EndpointAugmentedConcreteWChargedShiftClosure n hn4 charge)
    (hI3 :
      PerTypeMlprojClosure (n := n) (endpointAugmentedConcreteW n hn4)) :
    EndpointAugmentedConcreteWShiftMlprojClosureCharged n hn4 charge :=
  perTypeShiftMlprojClosure_charged_discharged
    (n := n) charge (endpointAugmentedConcreteW n hn4) hI1 hI2c hI3

/-- The corrected local closure route for the canonical row: endpoint-augmented
H4 together with charged I5.  This is the local replacement surface for the
impossible pair "canonical H4 + raw same-profile I2". -/
def EndpointAugmentedConcreteWCorrectedLocalClosure
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n) : Prop :=
  DerivClosurePerType (n := n) (endpointAugmentedConcreteW n hn4) ∧
    EndpointAugmentedConcreteWShiftMlprojClosureCharged n hn4 charge

/-- Constructor for the corrected local closure route. -/
theorem endpointAugmentedConcreteW_correctedLocalClosure_of_charged_components
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n)
    (hI1 :
      PerTypeProductGrouping (n := n) (endpointAugmentedConcreteW n hn4))
    (hI2c :
      EndpointAugmentedConcreteWChargedShiftClosure n hn4 charge)
    (hI3 :
      PerTypeMlprojClosure (n := n) (endpointAugmentedConcreteW n hn4)) :
    EndpointAugmentedConcreteWCorrectedLocalClosure n hn4 charge :=
  ⟨endpointAugmentedConcreteW_derivClosurePerType n hn4,
    endpointAugmentedConcreteW_shiftMlprojClosure_charged_of_components
      n hn4 charge hI1 hI2c hI3⟩

/-- Universal I1/I3 packages reduce the corrected endpoint local closure to
the single charged-shift obligation for the chosen charge relation. -/
theorem endpointAugmentedConcreteW_correctedLocalClosure_of_universal_I1_I3_chargedShift
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n)
    (hI1_univ : PallLean.Paper93.Wiring.PerTypeProductGrouping_universal)
    (hI2c :
      EndpointAugmentedConcreteWChargedShiftClosure n hn4 charge)
    (hI3_univ : PallLean.Paper93.Wiring.PerTypeMlprojClosure_universal) :
    EndpointAugmentedConcreteWCorrectedLocalClosure n hn4 charge :=
  endpointAugmentedConcreteW_correctedLocalClosure_of_charged_components
    n hn4 charge
    (hI1_univ n (endpointAugmentedConcreteW n hn4))
    hI2c
    (hI3_univ n (endpointAugmentedConcreteW n hn4))

/-! ## Zero-profile check: charged target, not same-profile target -/

/-- The corrected charged I5 statement sends the one-variable zero-profile
test row into whichever target profile is certified by `charge`.

This is the non-dangerous replacement for
`concreteW_shiftMlprojClosure_forces_zeroProfile_X_mem`: the conclusion is not
membership in the all-zero profile subspace unless the charge relation itself
chooses that target. -/
theorem concreteW_chargedShiftMlprojClosure_zeroProfile_X_mem_at_chargedTarget
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n)
    (hI5c : ConcreteWShiftMlprojClosureCharged n hn4 charge)
    (v : Fin n) (bpTgt : BoundedProfile (Nat.log 2 n))
    (hcharge :
      charge (zeroBoundedProfile (Nat.log 2 n)) [v]
        (MvPolynomial.X v : MvPolynomial (Fin n) ℚ) bpTgt) :
    MvPolynomial.X v ∈
      cookLevinProfileSubspace (n := n) bpTgt
        (concreteWCanonical n hn4) := by
  classical
  have hSlen : [v].length ≤ Nat.log 2 n :=
    singleton_length_le_log_two_of_ge_four n hn4 v
  have hshift :
      (MvPolynomial.X v : MvPolynomial (Fin n) ℚ).vars ⊆ [v].toFinset := by
    intro x hx
    simpa [MvPolynomial.vars_X] using hx
  have hmem :
      mlProj ((MvPolynomial.X v : MvPolynomial (Fin n) ℚ) *
          (1 : MvPolynomial (Fin n) ℚ)) ∈
        cookLevinProfileSubspace (n := n) bpTgt
          (concreteWCanonical n hn4) := by
    refine hI5c (zeroBoundedProfile (Nat.log 2 n)) bpTgt [v] hSlen
      (MvPolynomial.X v) hshift 1 ?_ hcharge
    refine ⟨0, (fun i => False.elim (Fin.elim0 i)),
      (fun i => False.elim (Fin.elim0 i)),
      (fun i => False.elim (Fin.elim0 i)), ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact False.elim (Fin.elim0 i)
    · intro i
      exact False.elim (Fin.elim0 i)
    · simp
    · funext tau
      simp [derivCountProfile, zeroProfileHistogram]
    · simp
  simpa [mul_one, SymmetricPower.mlProj_X] using hmem

/-! ## Axiom audit anchors -/

#print axioms concreteW_shiftMlprojClosure_charged_of_components
#print axioms concreteW_perTypeShiftMlprojClosure_charged_of_components
#print axioms endpointAugmentedConcreteW_shiftMlprojClosure_charged_of_components
#print axioms endpointAugmentedConcreteW_correctedLocalClosure_of_charged_components
#print axioms endpointAugmentedConcreteW_correctedLocalClosure_of_universal_I1_I3_chargedShift
#print axioms concreteW_chargedShiftMlprojClosure_zeroProfile_X_mem_at_chargedTarget

end PallLean.Paper93.DeepMath.PathB

namespace PallLean.Paper93.Paper283

open TuringMachine
open SymmetricPowerBound
open WithinProfileBound
open PallLean.Paper93.Closure
open PallLean.Paper93.DeepMath.PathB

/-! ## P-window cover bridge using non-scalar zero-profile closure -/

/-- Combined corrected route surface for the P-window cover.

The local closure side uses endpoint-augmented H4 and charged I5; the P-window
side uses active live-profile blockers plus a non-scalar zero-profile closure.
It deliberately contains neither canonical H4 nor raw same-profile I2. -/
structure RouteBRicherGaugeEndpointChargedPWindowBridge
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4) (charge : ProfileCharge n) where
  localClosure : EndpointAugmentedConcreteWCorrectedLocalClosure n hn4 charge
  cover : RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns

/-- Active live-profile blockers plus a budgeted non-scalar zero-profile
closure feed the richer-gauge unprojected P-window finite-span cover.

This is the P-window reduction compatible with the corrected charged route:
the live profiles are supplied by active blockers, while the all-zero profile
uses the non-scalar common-span budget rather than raw same-profile I2 or a
singleton/template zero-profile collapse. -/
noncomputable def routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_activeTypeCaseBlockers_zeroNonScalarClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    {budget : Nat}
    (hzero :
      CookLevinZeroProfileNonScalarClosureWithBudget
        M n hn2 htb hns budget)
    (hbudget : budget <= withinProfileBound (Nat.log 2 n))
    (hactive :
      CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns) :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns :=
  routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_activeTypeCaseBlockers_and_zeroProfileCommonSpan
    M n hn2 htb hns hn4
    (cookLevinZeroHistogramShiftCommonSpan_of_nonScalarClosureWithBudget
      M n hn2 htb hns hzero hbudget)
    hactive

/-- Concrete cardinality-bound variant of the same non-template P-window
route. -/
noncomputable def routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_activeTypeCaseBlockers_zeroNonScalarCardBound
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hbound :
      cookLevinZeroProfileNonScalarCardBound M n hn2 htb hns <=
        withinProfileBound (Nat.log 2 n))
    (hactive :
      CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns) :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns :=
  routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_activeTypeCaseBlockers_zeroNonScalarClosure
    M n hn2 htb hns hn4
    (cookLevinZeroProfileNonScalarClosureWithCardBound M n hn2 htb hns)
    hbound hactive

/-- Focused bridge: endpoint-augmented H4 plus charged I5 components, together
with the non-scalar zero-profile closure route, package the corrected P-window
cover endpoint.

This theorem retargets the cover away from canonical-H4/raw-same-profile-I2:
the H4 field is `endpointAugmentedConcreteW_derivClosurePerType`, the I5 field
is charged, and the zero profile is supplied by the non-scalar closure budget. -/
noncomputable def routeBRicherGauge_endpointChargedPWindowBridge_of_activeTypeCaseBlockers_zeroNonScalarClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4) (charge : ProfileCharge n)
    (hI1 :
      PerTypeProductGrouping (n := n) (endpointAugmentedConcreteW n hn4))
    (hI2c :
      EndpointAugmentedConcreteWChargedShiftClosure n hn4 charge)
    (hI3 :
      PerTypeMlprojClosure (n := n) (endpointAugmentedConcreteW n hn4))
    {budget : Nat}
    (hzero :
      CookLevinZeroProfileNonScalarClosureWithBudget
        M n hn2 htb hns budget)
    (hbudget : budget <= withinProfileBound (Nat.log 2 n))
    (hactive :
      CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns) :
    RouteBRicherGaugeEndpointChargedPWindowBridge M n hn2 htb hns hn4 charge :=
  ⟨endpointAugmentedConcreteW_correctedLocalClosure_of_charged_components
      n hn4 charge hI1 hI2c hI3,
    routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_activeTypeCaseBlockers_zeroNonScalarClosure
      M n hn2 htb hns hn4 hzero hbudget hactive⟩

/-- Cardinality-bound variant of the endpoint/charged/non-scalar P-window
bridge. -/
noncomputable def routeBRicherGauge_endpointChargedPWindowBridge_of_activeTypeCaseBlockers_zeroNonScalarCardBound
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4) (charge : ProfileCharge n)
    (hI1 :
      PerTypeProductGrouping (n := n) (endpointAugmentedConcreteW n hn4))
    (hI2c :
      EndpointAugmentedConcreteWChargedShiftClosure n hn4 charge)
    (hI3 :
      PerTypeMlprojClosure (n := n) (endpointAugmentedConcreteW n hn4))
    (hbound :
      cookLevinZeroProfileNonScalarCardBound M n hn2 htb hns <=
        withinProfileBound (Nat.log 2 n))
    (hactive :
      CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns) :
    RouteBRicherGaugeEndpointChargedPWindowBridge M n hn2 htb hns hn4 charge :=
  routeBRicherGauge_endpointChargedPWindowBridge_of_activeTypeCaseBlockers_zeroNonScalarClosure
    M n hn2 htb hns hn4 charge hI1 hI2c hI3
    (cookLevinZeroProfileNonScalarClosureWithCardBound M n hn2 htb hns)
    hbound hactive

/-! ## Axiom audit anchors -/

#print axioms routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_activeTypeCaseBlockers_zeroNonScalarClosure
#print axioms routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_activeTypeCaseBlockers_zeroNonScalarCardBound
#print axioms routeBRicherGauge_endpointChargedPWindowBridge_of_activeTypeCaseBlockers_zeroNonScalarClosure
#print axioms routeBRicherGauge_endpointChargedPWindowBridge_of_activeTypeCaseBlockers_zeroNonScalarCardBound

end PallLean.Paper93.Paper283
