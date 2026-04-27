import PallLean.Paper93.DeepMath.PathB.ConcreteWRowEmbeddingBridge
import PallLean.Paper93.DeepMath.PathB.ConcreteWRowEmbeddingsClosure
import PallLean.Paper93.DeepMath.PathB.ConcreteWFactorMembership
import PallLean.Paper93.DeepMath.PathB.CanonicalConcreteWH4Obstruction

/-!
# Active-profile blocker progress from concreteW frontiers

This module records the current checked active/profile route:

* the active type-case blockers follow from the concreteW row-embedding bundle;
* the row-embedding bundle follows from the concrete H3/H4/I5 frontier;
* equivalently, a universal per-type spanning package also supplies the
  active blockers after specializing to concreteW.

The canonical concreteW H3/H4/I5 frontier itself is now known to be blocked by
the H4 endpoint-derivative obstruction.  The purpose of this file is therefore
twofold: keep the old implication reusable when a row-embedding package is
available, and expose the sharper concrete instantiation frontier beneath it.
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

/-- The concreteW-specific remaining obligation for active profile blockers.

This is the same H3/H4/I5 frontier used to build
`Direct.CookLevinPerTypeRowEmbeddings_concreteW`, but named at the
active-profile layer. -/
def CookLevinActiveProfileConcreteWObligation
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) (hn4 : n >= 4) :
    Prop :=
  CookLevinFactorMemPerType M n hn htb hns
      (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau) ∧
    DerivClosurePerType (n := n)
      (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau) ∧
    PerTypeShiftMlprojClosure (n := n)
      (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau)

/-- The active-profile name is definitionally the existing concrete row-
embedding closure frontier. -/
theorem cookLevinActiveProfileConcreteWObligation_iff_closureFrontier
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) (hn4 : n >= 4) :
    CookLevinActiveProfileConcreteWObligation M n hn htb hns hn4 ↔
      CookLevinConcreteWRowEmbeddingClosureFrontier M n hn htb hns hn4 := by
  rfl

/-- Concrete H3/H4/I5 closure produces the active type-case blockers. -/
theorem cookLevinActiveProfileTypeCaseBlockers_of_concreteWClosureFrontier
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) (hn4 : n >= 4)
    (hFrontier :
      CookLevinConcreteWRowEmbeddingClosureFrontier M n hn htb hns hn4) :
    CookLevinActiveProfileTypeCaseBlockers M n hn htb hns :=
  cookLevinActiveProfileTypeCaseBlockers_closed_by_concreteW
    M n hn htb hns hn4
    (CookLevinPerTypeRowEmbeddings_concreteW_of_closureFrontier
      M n hn htb hns hn4 hFrontier)

/-- The active-profile concreteW obligation produces the active type-case
blockers. -/
theorem cookLevinActiveProfileTypeCaseBlockers_of_activeConcreteWObligation
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) (hn4 : n >= 4)
    (hFrontier :
      CookLevinActiveProfileConcreteWObligation M n hn htb hns hn4) :
    CookLevinActiveProfileTypeCaseBlockers M n hn htb hns :=
  cookLevinActiveProfileTypeCaseBlockers_of_concreteWClosureFrontier
    M n hn htb hns hn4 hFrontier

/-- The same concrete H3/H4/I5 closure closes all remaining live profile
cases through the active blocker split. -/
theorem cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_concreteWClosureFrontier
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) (hn4 : n >= 4)
    (hFrontier :
      CookLevinConcreteWRowEmbeddingClosureFrontier M n hn htb hns hn4) :
    CookLevinAllBoundedProfileCommonSpanLiveProfileCases M n hn htb hns :=
  cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_activeTypeCaseBlockers
    M n hn htb hns
    (cookLevinActiveProfileTypeCaseBlockers_of_concreteWClosureFrontier
      M n hn htb hns hn4 hFrontier)

/-- The concrete H3/H4/I5 components, exposed separately, produce the active
type-case blockers. -/
theorem cookLevinActiveProfileTypeCaseBlockers_of_concreteW_H3_H4_I5
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) (hn4 : n >= 4)
    (hFactor :
      CookLevinFactorMemPerType M n hn htb hns
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hDeriv :
      DerivClosurePerType (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hShiftMlproj :
      PerTypeShiftMlprojClosure (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau)) :
    CookLevinActiveProfileTypeCaseBlockers M n hn htb hns :=
  cookLevinActiveProfileTypeCaseBlockers_of_concreteWClosureFrontier
    M n hn htb hns hn4 ⟨hFactor, hDeriv, hShiftMlproj⟩

/-- The concrete H3/H4/I5 components also close the named live profile
package. -/
theorem cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_concreteW_H3_H4_I5
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) (hn4 : n >= 4)
    (hFactor :
      CookLevinFactorMemPerType M n hn htb hns
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hDeriv :
      DerivClosurePerType (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hShiftMlproj :
      PerTypeShiftMlprojClosure (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau)) :
    CookLevinAllBoundedProfileCommonSpanLiveProfileCases M n hn htb hns :=
  cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_concreteWClosureFrontier
    M n hn htb hns hn4 ⟨hFactor, hDeriv, hShiftMlproj⟩

/-! ## Instantiated concreteW component frontier -/

/-- Concrete component frontier below the abstract H3/H4/I5 active-profile
obligation.

This is the strongest canonical-concrete decomposition currently available:
direct branch-shape witnesses give existential row membership; canonical-row
transport turns those witnesses into the fixed `Fin.castLEEmb` row; H4 remains
as the canonical derivative-closure component; and I5 is composed from the
concrete I1/I2/I3 interfaces.

The H4 component is intentionally explicit: `CanonicalConcreteWH4Obstruction`
proves that it cannot be supplied for the unaugmented canonical `concreteW`
family. -/
def CookLevinActiveProfileConcreteWInstantiationFrontier
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) (hn4 : n >= 4) :
    Prop :=
  CookLevinDirectBranchShapeWitnesses M n hn htb hns hn4 ∧
    CookLevinConcreteWCanonicalRowTransport M n hn htb hns hn4 ∧
    DerivClosurePerType (n := n)
      (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau) ∧
    ConcreteWProductGrouping n hn4 ∧
    ConcreteWShiftClosure n hn4 ∧
    ConcreteWMlprojClosure n hn4

/-- The instantiated branch-shape/transport/H4/I1/I2/I3 frontier implies the
older active-profile concreteW obligation. -/
theorem cookLevinActiveProfileConcreteWObligation_of_instantiationFrontier
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) (hn4 : n >= 4)
    (hFrontier :
      CookLevinActiveProfileConcreteWInstantiationFrontier
        M n hn htb hns hn4) :
    CookLevinActiveProfileConcreteWObligation M n hn htb hns hn4 := by
  rcases hFrontier with
    ⟨hShape, hTransport, hDeriv, hI1, hI2, hI3⟩
  exact
    concreteW_closureFrontier_of_H3_H4_components
      M n hn htb hns hn4
      (CookLevinFactorMemPerType_concreteW_of_directBranchShapes_transport
        M n hn htb hns hn4 hShape hTransport)
      hDeriv hI1 hI2 hI3

/-- Concrete H3 and H4 plus I1/I2/I3, with I5 composed internally, produce
the active type-case blockers. -/
theorem cookLevinActiveProfileTypeCaseBlockers_of_concreteW_H3_H4_I123
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) (hn4 : n >= 4)
    (hFactor :
      CookLevinFactorMemPerType M n hn htb hns
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hDeriv :
      DerivClosurePerType (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hI1 : ConcreteWProductGrouping n hn4)
    (hI2 : ConcreteWShiftClosure n hn4)
    (hI3 : ConcreteWMlprojClosure n hn4) :
    CookLevinActiveProfileTypeCaseBlockers M n hn htb hns :=
  cookLevinActiveProfileTypeCaseBlockers_of_concreteWClosureFrontier
    M n hn htb hns hn4
    (concreteW_closureFrontier_of_H3_H4_components
      M n hn htb hns hn4 hFactor hDeriv hI1 hI2 hI3)

/-- Direct branch shapes plus canonical-row transport close H3; together with
canonical H4 and concrete I1/I2/I3 they produce active type-case blockers. -/
theorem cookLevinActiveProfileTypeCaseBlockers_of_directBranchShapes_transport_H4_I123
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) (hn4 : n >= 4)
    (hShape : CookLevinDirectBranchShapeWitnesses M n hn htb hns hn4)
    (hTransport :
      CookLevinConcreteWCanonicalRowTransport M n hn htb hns hn4)
    (hDeriv :
      DerivClosurePerType (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hI1 : ConcreteWProductGrouping n hn4)
    (hI2 : ConcreteWShiftClosure n hn4)
    (hI3 : ConcreteWMlprojClosure n hn4) :
    CookLevinActiveProfileTypeCaseBlockers M n hn htb hns :=
  cookLevinActiveProfileTypeCaseBlockers_of_concreteW_H3_H4_I123
    M n hn htb hns hn4
    (CookLevinFactorMemPerType_concreteW_of_directBranchShapes_transport
      M n hn htb hns hn4 hShape hTransport)
    hDeriv hI1 hI2 hI3

/-- The same instantiated component frontier closes the active type-case
blockers. -/
theorem cookLevinActiveProfileTypeCaseBlockers_of_instantiationFrontier
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) (hn4 : n >= 4)
    (hFrontier :
      CookLevinActiveProfileConcreteWInstantiationFrontier
        M n hn htb hns hn4) :
    CookLevinActiveProfileTypeCaseBlockers M n hn htb hns :=
  cookLevinActiveProfileTypeCaseBlockers_of_activeConcreteWObligation
    M n hn htb hns hn4
    (cookLevinActiveProfileConcreteWObligation_of_instantiationFrontier
      M n hn htb hns hn4 hFrontier)

/-- The instantiated component frontier also closes all named live-profile
cases. -/
theorem cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_instantiationFrontier
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) (hn4 : n >= 4)
    (hFrontier :
      CookLevinActiveProfileConcreteWInstantiationFrontier
        M n hn htb hns hn4) :
    CookLevinAllBoundedProfileCommonSpanLiveProfileCases M n hn htb hns :=
  cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_activeTypeCaseBlockers
    M n hn htb hns
    (cookLevinActiveProfileTypeCaseBlockers_of_instantiationFrontier
      M n hn htb hns hn4 hFrontier)

/-! ## Canonical-concrete no-go diagnostics -/

/-- The active-profile name for the canonical concreteW H3/H4/I5 obligation
inherits the canonical H4 obstruction. -/
theorem not_CookLevinActiveProfileConcreteWObligation
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) (hn4 : n >= 4) :
    ¬ CookLevinActiveProfileConcreteWObligation M n hn htb hns hn4 := by
  intro hFrontier
  exact not_canonicalConcreteW_derivClosurePerType n hn4 hFrontier.2.1

/-- Consequently, the fully instantiated canonical concreteW component
frontier cannot be discharged either: it still contains canonical H4. -/
theorem not_CookLevinActiveProfileConcreteWInstantiationFrontier
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) (hn4 : n >= 4) :
    ¬ CookLevinActiveProfileConcreteWInstantiationFrontier
        M n hn htb hns hn4 := by
  intro hFrontier
  rcases hFrontier with
    ⟨_hShape, _hTransport, hDeriv, _hI1, _hI2, _hI3⟩
  exact not_canonicalConcreteW_derivClosurePerType n hn4 hDeriv

/-- Compact active/profile diagnostic: the canonical concreteW active
frontier is blocked, while the endpoint-augmented H4 replacement is available.

This is the paper-faithful split for this side of Route B: active blockers may
still be consumed from a concreteW row-embedding package, but the old route for
proving that package through unaugmented canonical H4 is closed off. -/
theorem activeProfileConcreteW_no_go_and_endpointH4
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) (hn4 : n >= 4) :
    (¬ CookLevinActiveProfileConcreteWObligation M n hn htb hns hn4) ∧
      DerivClosurePerType (n := n) (endpointAugmentedConcreteW n hn4) :=
  ⟨not_CookLevinActiveProfileConcreteWObligation M n hn htb hns hn4,
    corrected_endpointAugmentedConcreteW_derivClosurePerType n hn4⟩

/-- A universal concreteW row-embedding package supplies active type-case
blockers for every Cook-Levin instance satisfying the side conditions. -/
theorem cookLevinActiveProfileTypeCaseBlockers_of_concreteWRowEmbeddings_universal
    (hRowEmbeddings_universal :
      forall (M : DTM) (n : Nat) (hn : n >= 2)
        (hn4 : n >= 4) (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
          M n hn htb hns hn4) :
    forall (M : DTM) (n : Nat) (hn : n >= 2)
      (_hn4 : n >= 4) (htb : M.timeBound <= 4) (hns : M.numStates <= n),
      CookLevinActiveProfileTypeCaseBlockers M n hn htb hns := by
  intro M n hn hn4 htb hns
  exact
    cookLevinActiveProfileTypeCaseBlockers_closed_by_concreteW
      M n hn htb hns hn4
      (hRowEmbeddings_universal M n hn hn4 htb hns)

/-- A universal per-type spanning theorem supplies active type-case blockers
after specialization to the canonical concreteW family. -/
theorem cookLevinActiveProfileTypeCaseBlockers_of_perTypeSpanning_universal
    (hSpan_universal : CookLevinPerTypeSpanning_universal) :
    forall (M : DTM) (n : Nat) (hn : n >= 2)
      (_hn4 : n >= 4) (htb : M.timeBound <= 4) (hns : M.numStates <= n),
      CookLevinActiveProfileTypeCaseBlockers M n hn htb hns := by
  intro M n hn hn4 htb hns
  exact
    cookLevinActiveProfileTypeCaseBlockers_closed_by_concreteW
      M n hn htb hns hn4
      (CookLevinPerTypeRowEmbeddings_concreteW_of_universalSpanning
        hSpan_universal M n hn hn4 htb hns)

/-- Universal concreteW H3/H4/I5 closure is enough for universal active
type-case blockers. -/
theorem cookLevinActiveProfileTypeCaseBlockers_of_concreteWClosureFrontier_universal
    (hFrontier_universal :
      forall (M : DTM) (n : Nat) (hn : n >= 2)
        (hn4 : n >= 4) (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        CookLevinConcreteWRowEmbeddingClosureFrontier M n hn htb hns hn4) :
    forall (M : DTM) (n : Nat) (hn : n >= 2)
      (_hn4 : n >= 4) (htb : M.timeBound <= 4) (hns : M.numStates <= n),
      CookLevinActiveProfileTypeCaseBlockers M n hn htb hns := by
  intro M n hn hn4 htb hns
  exact
    cookLevinActiveProfileTypeCaseBlockers_of_concreteWClosureFrontier
      M n hn htb hns hn4
      (hFrontier_universal M n hn hn4 htb hns)

/-! ## Axiom audit anchors -/

#print axioms cookLevinActiveProfileConcreteWObligation_iff_closureFrontier
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_concreteWClosureFrontier
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_activeConcreteWObligation
#print axioms cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_concreteWClosureFrontier
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_concreteW_H3_H4_I5
#print axioms cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_concreteW_H3_H4_I5
#print axioms cookLevinActiveProfileConcreteWObligation_of_instantiationFrontier
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_concreteW_H3_H4_I123
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_directBranchShapes_transport_H4_I123
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_instantiationFrontier
#print axioms cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_instantiationFrontier
#print axioms not_CookLevinActiveProfileConcreteWObligation
#print axioms not_CookLevinActiveProfileConcreteWInstantiationFrontier
#print axioms activeProfileConcreteW_no_go_and_endpointH4
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_concreteWRowEmbeddings_universal
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_perTypeSpanning_universal
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_concreteWClosureFrontier_universal

end PallLean.Paper93.DeepMath.PathB
