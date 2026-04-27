import PallLean.Paper93.DeepMath.PathB.ConcreteWRowEmbeddingBridge
import PallLean.Paper93.DeepMath.PathB.ConcreteWRowEmbeddingsClosure

/-!
# Active-profile blocker progress from concreteW frontiers

This module records the current checked active/profile route:

* the active type-case blockers follow from the concreteW row-embedding bundle;
* the row-embedding bundle follows from the concrete H3/H4/I5 frontier;
* equivalently, a universal per-type spanning package also supplies the
  active blockers after specializing to concreteW.

No theorem below proves the concreteW H3/H4/I5 frontier.  The purpose is to
make the remaining active/profile obligation explicit and reusable.
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
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_concreteWRowEmbeddings_universal
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_perTypeSpanning_universal
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_concreteWClosureFrontier_universal

end PallLean.Paper93.DeepMath.PathB
