import PallLean.Paper93.DeepMath.PathB.ConcreteWRowEmbeddingBridge
import PallLean.Paper93.DeepMath.PathB.KeepFOBTemplateCollapseAssembly
import PallLean.Paper93.DeepMath.PathB.PerTypeSpanningTemplateCollapseBridge
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
* active admissible profile cases plus the zero-profile support-basis
  cardinality obligation.
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

/-! ## Axiom audit anchors -/

#print axioms cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_concreteW_closureFrontier
#print axioms cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_concreteW_H3_H4_I5
#print axioms cookLevinRichProjectionTarget_of_keepFOB_concreteW_rowEmbeddings
#print axioms cookLevinRichProjectionTarget_of_keepFOB_concreteW_closureFrontier
#print axioms cookLevinRichProjectionTarget_of_keepFOB_concreteW_H3_H4_I5
#print axioms cookLevinRichProjectionDischarge_of_keepFOB_concreteW_closureFrontier
#print axioms cookLevinRichProjectionTarget_of_keepFOB_activeCases_zeroSupport
#print axioms cookLevinRichProjectionDischarge_of_keepFOB_activeCases_zeroSupport

end PallLean.Paper93.DeepMath.PathB
