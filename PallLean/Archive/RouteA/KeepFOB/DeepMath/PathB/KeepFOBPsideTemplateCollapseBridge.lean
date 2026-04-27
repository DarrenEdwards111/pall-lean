import PallLean.Paper93.DeepMath.PathB.ConcreteWRowEmbeddingBridge
import PallLean.Paper93.DeepMath.PathB.ConcreteWFactorMembership
import PallLean.Paper93.DeepMath.PathB.ConcreteWShiftMlprojClosure
import PallLean.Archive.RouteA.KeepFOB.DeepMath.PathB.KeepFOBTemplateCollapseAssembly
import PallLean.Paper93.DeepMath.PathB.PerTypeSpanningTemplateCollapseBridge
import PallLean.Paper93.DeepMath.PathB.ZeroProfileSupportBasisCardinality
import PallLean.Paper93.DeepMath.PathB.ZeroProfileTemplateCollapseReduction

set_option exponentiation.threshold 1000

/-!
# keepFOB P-side template-collapse bridge

This module records the current honest P-side closure path for the concrete
`keepFOB` gauge.

The NP identity-minor field is already supplied by
`satDeciderGaugeKeepFOBProjection_npIdentityMinorPreservation`.  The remaining
load-bearing input is therefore the Cook-Levin bounded-profile template
collapse.  The theorems below push that input down to the smallest active
frontiers currently isolated in PathB:

* concreteW row embeddings;
* the concreteW H3/H4/I5 closure package;
* active admissible profile cases plus the zero-profile scalar
  singleton-template obligation.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open PaperFaithfulSeparation
open SymmetricPowerBound
open TuringMachine (DTM)
open WithinProfileBound
open PallLean.Paper93
open PallLean.Paper93.Spanning
open PallLean.Paper93.Wiring (concreteW)

attribute [local instance] Classical.dec

private theorem ge_four_of_ge_two_pow_804 {n : Nat} (hn : n ≥ 2 ^ 804) :
    n ≥ 4 := by
  have hfour : (4 : Nat) ≤ 2 ^ 804 := by
    calc
      (4 : Nat) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
  exact le_trans hfour hn

/-- ConcreteW H3/H4/I5 closure supplies the bounded-profile template-collapse
lemma through the concrete row-embedding bridge. -/
theorem cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_concreteW_closureFrontier
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hFrontier :
      CookLevinConcreteWRowEmbeddingClosureFrontier M n hn htb hns hn4) :
    CookLevinProfileTemplateCollapseLemmaBoundedProfile M n hn htb hns :=
  cookLevinProfileTemplateCollapseLemmaBoundedProfile_from_concreteW_rowEmbeddings
    M n hn htb hns hn4
    (CookLevinPerTypeRowEmbeddings_concreteW_of_closureFrontier
      M n hn htb hns hn4 hFrontier)

/-- Componentwise concreteW H3/H4/I5 version of the bounded-profile
template-collapse bridge. -/
theorem cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_concreteW_H3_H4_I5
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hFactor :
      CookLevinFactorMemPerType M n hn htb hns
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hDeriv :
      DerivClosurePerType (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hShiftMlproj :
      PerTypeShiftMlprojClosure (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau)) :
    CookLevinProfileTemplateCollapseLemmaBoundedProfile M n hn htb hns :=
  cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_concreteW_closureFrontier
    M n hn htb hns hn4 ⟨hFactor, hDeriv, hShiftMlproj⟩

/-- Concrete row embeddings are now enough to complete the concrete `keepFOB`
rich-projection target.  The NP field is filled by the projected lower-bound
module; the row embeddings fill the P-side template-collapse field. -/
theorem cookLevinRichProjectionTarget_of_keepFOB_concreteW_rowEmbeddings
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns (ge_four_of_ge_two_pow_804 hn)) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_keepFOB_boundedProfileTemplateCollapse
    M n hn hn2 htb hns
    (cookLevinProfileTemplateCollapseLemmaBoundedProfile_from_concreteW_rowEmbeddings
      M n hn2 htb hns (ge_four_of_ge_two_pow_804 hn) hRowEmbeddings)

/-- ConcreteW H3/H4/I5 closure is enough to complete the per-instance
`keepFOB` rich-projection target. -/
theorem cookLevinRichProjectionTarget_of_keepFOB_concreteW_closureFrontier
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hFrontier :
      CookLevinConcreteWRowEmbeddingClosureFrontier
        M n hn2 htb hns (ge_four_of_ge_two_pow_804 hn)) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_keepFOB_boundedProfileTemplateCollapse
    M n hn hn2 htb hns
    (cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_concreteW_closureFrontier
      M n hn2 htb hns (ge_four_of_ge_two_pow_804 hn) hFrontier)

/-- Componentwise H3/H4/I5 closure is enough to complete the per-instance
`keepFOB` rich-projection target. -/
theorem cookLevinRichProjectionTarget_of_keepFOB_concreteW_H3_H4_I5
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hFactor :
      CookLevinFactorMemPerType M n hn2 htb hns
        (fun tau =>
          concreteW n (ge_four_of_ge_two_pow_804 hn)
            (Fin.castLEEmb (ge_four_of_ge_two_pow_804 hn)) tau))
    (hDeriv :
      DerivClosurePerType (n := n)
        (fun tau =>
          concreteW n (ge_four_of_ge_two_pow_804 hn)
            (Fin.castLEEmb (ge_four_of_ge_two_pow_804 hn)) tau))
    (hShiftMlproj :
      PerTypeShiftMlprojClosure (n := n)
        (fun tau =>
          concreteW n (ge_four_of_ge_two_pow_804 hn)
            (Fin.castLEEmb (ge_four_of_ge_two_pow_804 hn)) tau)) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_keepFOB_concreteW_closureFrontier
    M n hn hn2 htb hns ⟨hFactor, hDeriv, hShiftMlproj⟩

/-- Direct branch-shape witnesses, canonical-row transport, H4, and concrete
I1/I2/I3 closure components are enough to complete the per-instance
`keepFOB` rich-projection target.  This is the current most explicit
factor/closure formulation of the P-side bridge. -/
theorem cookLevinRichProjectionTarget_of_keepFOB_directShapes_transport_H4_I123
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hShape :
      CookLevinDirectBranchShapeWitnesses
        M n hn2 htb hns (ge_four_of_ge_two_pow_804 hn))
    (hTransport :
      CookLevinConcreteWCanonicalRowTransport
        M n hn2 htb hns (ge_four_of_ge_two_pow_804 hn))
    (hDeriv :
      DerivClosurePerType (n := n)
        (fun tau =>
          concreteW n (ge_four_of_ge_two_pow_804 hn)
            (Fin.castLEEmb (ge_four_of_ge_two_pow_804 hn)) tau))
    (hI1 :
      ConcreteWProductGrouping n (ge_four_of_ge_two_pow_804 hn))
    (hI2 :
      ConcreteWShiftClosure n (ge_four_of_ge_two_pow_804 hn))
    (hI3 :
      ConcreteWMlprojClosure n (ge_four_of_ge_two_pow_804 hn)) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns := by
  refine cookLevinRichProjectionTarget_of_keepFOB_concreteW_closureFrontier
    M n hn hn2 htb hns ?_
  exact concreteW_closureFrontier_of_H3_H4_components
    M n hn2 htb hns (ge_four_of_ge_two_pow_804 hn)
    (CookLevinFactorMemPerType_concreteW_of_directBranchShapes_transport
      M n hn2 htb hns (ge_four_of_ge_two_pow_804 hn) hShape hTransport)
    hDeriv hI1 hI2 hI3

/-- Uniform direct-shape, canonical-row transport, H4, and I1/I2/I3 closure
components discharge the `keepFOB` rich-projection surface. -/
theorem cookLevinRichProjectionDischarge_of_keepFOB_directShapes_transport_H4_I123
    (hShape :
      ∀ (M : DTM) (n : Nat) (hn2 : n ≥ 2)
        (hn4 : n ≥ 4) (htb : M.timeBound ≤ 4)
        (hns : M.numStates ≤ n),
        CookLevinDirectBranchShapeWitnesses M n hn2 htb hns hn4)
    (hTransport :
      ∀ (M : DTM) (n : Nat) (hn2 : n ≥ 2)
        (hn4 : n ≥ 4) (htb : M.timeBound ≤ 4)
        (hns : M.numStates ≤ n),
        CookLevinConcreteWCanonicalRowTransport M n hn2 htb hns hn4)
    (hDeriv :
      ∀ (n : Nat) (hn4 : n ≥ 4),
        DerivClosurePerType (n := n)
          (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hI1 :
      ∀ (n : Nat) (hn4 : n ≥ 4), ConcreteWProductGrouping n hn4)
    (hI2 :
      ∀ (n : Nat) (hn4 : n ≥ 4), ConcreteWShiftClosure n hn4)
    (hI3 :
      ∀ (n : Nat) (hn4 : n ≥ 4), ConcreteWMlprojClosure n hn4) :
    CookLevinRichProjectionDischarge := by
  intro M n hn hn2 htb hns _hdec
  exact
    cookLevinRichProjectionTarget_of_keepFOB_directShapes_transport_H4_I123
      M n hn hn2 htb hns
      (hShape M n hn2 (ge_four_of_ge_two_pow_804 hn) htb hns)
      (hTransport M n hn2 (ge_four_of_ge_two_pow_804 hn) htb hns)
      (hDeriv n (ge_four_of_ge_two_pow_804 hn))
      (hI1 n (ge_four_of_ge_two_pow_804 hn))
      (hI2 n (ge_four_of_ge_two_pow_804 hn))
      (hI3 n (ge_four_of_ge_two_pow_804 hn))

/-- Uniform concreteW closure discharges the whole `keepFOB` rich-projection
surface.  This is the current sharp H3/H4/I5 formulation of the P-side
template-collapse blocker. -/
theorem cookLevinRichProjectionDischarge_of_keepFOB_concreteW_closureFrontier
    (hFrontier :
      ∀ (M : DTM) (n : Nat) (hn2 : n ≥ 2)
        (hn4 : n ≥ 4) (htb : M.timeBound ≤ 4)
        (hns : M.numStates ≤ n),
        CookLevinConcreteWRowEmbeddingClosureFrontier M n hn2 htb hns hn4) :
    CookLevinRichProjectionDischarge := by
  intro M n hn hn2 htb hns _hdec
  exact
    cookLevinRichProjectionTarget_of_keepFOB_concreteW_closureFrontier
      M n hn hn2 htb hns
      (hFrontier M n hn2 (ge_four_of_ge_two_pow_804 hn) htb hns)

/-- The active-profile/zero-profile split is another exact P-side bridge into
the concrete `keepFOB` target. -/
theorem cookLevinRichProjectionTarget_of_keepFOB_activeCases_zeroSupport
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hzero :
      CookLevinZeroProfileTemplateSupportBasisCardinalityObligation
        M n hn2 htb hns)
    (hcases :
      CookLevinProfileTemplateCollapseActiveAdmissibleProfileCases
        M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_keepFOB_boundedProfileTemplateCollapse
    M n hn hn2 htb hns
    (cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_activeAdmissibleProfileCases_and_zeroProfileSupportBasis_cardinality
      M n hn2 htb hns (ge_four_of_ge_two_pow_804 hn) hzero hcases)

/-- Uniform active-profile cases plus the zero-profile support-basis
cardinality obligation discharge the `keepFOB` rich-projection surface. -/
theorem cookLevinRichProjectionDischarge_of_keepFOB_activeCases_zeroSupport
    (hzero :
      ∀ (M : DTM) (n : Nat) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroProfileTemplateSupportBasisCardinalityObligation
          M n hn2 htb hns)
    (hcases :
      ∀ (M : DTM) (n : Nat) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinProfileTemplateCollapseActiveAdmissibleProfileCases
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge := by
  intro M n hn hn2 htb hns _hdec
  exact
    cookLevinRichProjectionTarget_of_keepFOB_activeCases_zeroSupport
      M n hn hn2 htb hns
      (hzero M n hn2 htb hns)
      (hcases M n hn2 htb hns)

/-- Scalar zero-profile singleton collapse is the honest replacement for the
false explicit support-basis-cardinality route.  Together with active
admissible profile cases it completes the per-instance concrete `keepFOB`
target. -/
theorem cookLevinRichProjectionTarget_of_keepFOB_activeCases_zeroScalar
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hzero :
      CookLevinZeroProfileTemplateScalarObligation M n hn2 htb hns)
    (hcases :
      CookLevinProfileTemplateCollapseActiveAdmissibleProfileCases
        M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_keepFOB_boundedProfileTemplateCollapse
    M n hn hn2 htb hns
    (cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_activeAdmissibleProfileCases
      M n hn2 htb hns (ge_four_of_ge_two_pow_804 hn)
      (cookLevinZeroHistogramTemplateShiftCollapse_of_scalar
        M n hn2 htb hns hzero)
      hcases)

/-- Uniform active-profile cases plus the scalar zero-profile singleton
obligation discharge the `keepFOB` rich-projection surface. -/
theorem cookLevinRichProjectionDischarge_of_keepFOB_activeCases_zeroScalar
    (hzero :
      ∀ (M : DTM) (n : Nat) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroProfileTemplateScalarObligation
          M n hn2 htb hns)
    (hcases :
      ∀ (M : DTM) (n : Nat) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinProfileTemplateCollapseActiveAdmissibleProfileCases
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge := by
  intro M n hn hn2 htb hns _hdec
  exact
    cookLevinRichProjectionTarget_of_keepFOB_activeCases_zeroScalar
      M n hn hn2 htb hns
      (hzero M n hn2 htb hns)
      (hcases M n hn2 htb hns)

/-! ## Axiom audit anchors -/

#print axioms cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_concreteW_closureFrontier
#print axioms cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_concreteW_H3_H4_I5
#print axioms cookLevinRichProjectionTarget_of_keepFOB_concreteW_rowEmbeddings
#print axioms cookLevinRichProjectionTarget_of_keepFOB_concreteW_closureFrontier
#print axioms cookLevinRichProjectionTarget_of_keepFOB_concreteW_H3_H4_I5
#print axioms cookLevinRichProjectionTarget_of_keepFOB_directShapes_transport_H4_I123
#print axioms cookLevinRichProjectionDischarge_of_keepFOB_directShapes_transport_H4_I123
#print axioms cookLevinRichProjectionDischarge_of_keepFOB_concreteW_closureFrontier
#print axioms cookLevinRichProjectionTarget_of_keepFOB_activeCases_zeroSupport
#print axioms cookLevinRichProjectionDischarge_of_keepFOB_activeCases_zeroSupport
#print axioms cookLevinRichProjectionTarget_of_keepFOB_activeCases_zeroScalar
#print axioms cookLevinRichProjectionDischarge_of_keepFOB_activeCases_zeroScalar

end PallLean.Paper93.DeepMath.PathB
