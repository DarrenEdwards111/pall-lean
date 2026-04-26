import PallLean.Paper93.Paper283.RouteBRicherGaugePWindowConcreteCover
import PallLean.Paper93.DeepMath.PathB.ConcreteWRowEmbeddingBridge
import PallLean.Paper93.DeepMath.PathB.ConcreteWFactorMembership
import PallLean.Paper93.DeepMath.PathB.ConcreteWShiftMlprojClosure

/-!
# Concrete discharge surface for the Route B richer-gauge P-window cover

This file pushes the P-window finite-span cover below the row-embedding
assumption used by `RouteBRicherGaugePWindowConcreteCover`.

The strongest checked close-out here is:

* concreteW H3/H4/I5 closure frontier
* `Direct.CookLevinPerTypeRowEmbeddings_concreteW`
* all-bounded fixed-profile common span
* `RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover`

No `spdp_profile_generators` route is used.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open TuringMachine (DTM)
open WithinProfileBound
open PallLean.Paper93
open PallLean.Paper93.Spanning
open PallLean.Paper93.Wiring (concreteW)
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- ConcreteW H3/H4/I5 closure closes one fixed-profile all-bounded
common-span obligation. -/
theorem cookLevinAllBoundedProfileCommonSpanAtProfile_of_concreteW_closureFrontier
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hFrontier :
      CookLevinConcreteWRowEmbeddingClosureFrontier M n hn htb hns hn4)
    (h : SymmetricPowerBound.ProfileHistogram) :
    CookLevinAllBoundedProfileCommonSpanAtProfile M n hn htb hns h :=
  cookLevinAllBoundedProfileCommonSpanLemma_of_concreteW_rowEmbeddings
    M n hn htb hns hn4
    (CookLevinPerTypeRowEmbeddings_concreteW_of_closureFrontier
      M n hn htb hns hn4 hFrontier)
    h

/-- ConcreteW H3/H4/I5 closure closes the all-profile all-bounded common-span
frontier. -/
theorem cookLevinAllBoundedProfileCommonSpanLemma_of_concreteW_closureFrontier
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hFrontier :
      CookLevinConcreteWRowEmbeddingClosureFrontier M n hn htb hns hn4) :
    CookLevinAllBoundedProfileCommonSpanLemma M n hn htb hns := by
  intro h
  exact
    cookLevinAllBoundedProfileCommonSpanAtProfile_of_concreteW_closureFrontier
      M n hn htb hns hn4 hFrontier h

/-- ConcreteW H3/H4/I5 closure supplies the richer-gauge unprojected P-window
finite-span cover. This is the row-embedding assumption discharged down to the
named concrete H3/H4/I5 frontier. -/
noncomputable def routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_concreteW_closureFrontier
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hFrontier :
      CookLevinConcreteWRowEmbeddingClosureFrontier M n hn htb hns hn4) :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn htb hns :=
  routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_allBoundedProfileCommonSpan
    M n hn htb hns
    (cookLevinAllBoundedProfileCommonSpanLemma_of_concreteW_closureFrontier
      M n hn htb hns hn4 hFrontier)

/-- Componentwise concreteW H3/H4/I5 version of the P-window finite-span
cover. -/
noncomputable def routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_concreteW_H3_H4_I5
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hFactor :
      CookLevinFactorMemPerType M n hn htb hns
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hDeriv :
      DerivClosurePerType (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hShiftMlproj :
      PerTypeShiftMlprojClosure (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau)) :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn htb hns :=
  routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_concreteW_closureFrontier
    M n hn htb hns hn4 ⟨hFactor, hDeriv, hShiftMlproj⟩

/-- ConcreteW H3 plus H4 plus the I1/I2/I3 component closure package supplies
the P-window finite-span cover. -/
noncomputable def routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_concreteW_H3_H4_I123
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hFactor :
      CookLevinFactorMemPerType M n hn htb hns
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hDeriv :
      DerivClosurePerType (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hI1 : ConcreteWProductGrouping n hn4)
    (hI2 : ConcreteWShiftClosure n hn4)
    (hI3 : ConcreteWMlprojClosure n hn4) :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn htb hns :=
  routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_concreteW_closureFrontier
    M n hn htb hns hn4
    (concreteW_closureFrontier_of_H3_H4_components
      M n hn htb hns hn4 hFactor hDeriv hI1 hI2 hI3)

/-- Most explicit currently checked concreteW reduction for this P-window
cover: direct branch shapes plus canonical-row transport close H3; H4 and
I1/I2/I3 remain as the concrete closure assumptions. -/
noncomputable def routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_directBranchShapes_transport_H4_I123
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hShape : CookLevinDirectBranchShapeWitnesses M n hn htb hns hn4)
    (hTransport : CookLevinConcreteWCanonicalRowTransport M n hn htb hns hn4)
    (hDeriv :
      DerivClosurePerType (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hI1 : ConcreteWProductGrouping n hn4)
    (hI2 : ConcreteWShiftClosure n hn4)
    (hI3 : ConcreteWMlprojClosure n hn4) :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn htb hns :=
  routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_concreteW_H3_H4_I123
    M n hn htb hns hn4
    (CookLevinFactorMemPerType_concreteW_of_directBranchShapes_transport
      M n hn htb hns hn4 hShape hTransport)
    hDeriv hI1 hI2 hI3

/-! ## Axiom audit anchors -/

#print axioms cookLevinAllBoundedProfileCommonSpanAtProfile_of_concreteW_closureFrontier
#print axioms cookLevinAllBoundedProfileCommonSpanLemma_of_concreteW_closureFrontier
#print axioms routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_concreteW_closureFrontier
#print axioms routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_concreteW_H3_H4_I5
#print axioms routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_concreteW_H3_H4_I123
#print axioms routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_directBranchShapes_transport_H4_I123

end PallLean.Paper93.Paper283
