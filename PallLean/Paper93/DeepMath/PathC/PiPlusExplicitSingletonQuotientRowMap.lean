import PallLean.Paper93.DeepMath.PathC.PiPlusOneWindowConcreteRowMapBudget

/-!
# Explicit singleton-quotient concrete row map

This file provides the actual `ZeroProfileConcreteNormalFormRowMap` inhabitant
for the corrected one-window singleton-quotient socket, reducing it to the
single row-level geometric fact that the *projected* shifted rows land in the
zero-profile `concreteW` chart.

Unlike the dead identity/post-span containment, the hypothesis here is already
projected by `zeroProfileQuotientBySingletonShiftProjection`; it does not imply
the false unprojected one-window zero socket.
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

/-- The exact projected row-membership fact needed to build the concrete row
map.  Every one-window zero-profile shifted row, after singleton-quotient
projection, lies in the canonical zero-profile `concreteW` chart. -/
def CookLevinOneWindowSingletonQuotientConcreteWRowPreservation
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4) : Prop :=
  ∀ (S : List (Fin n)), S.length ≤ Nat.log 2 n + 1 →
    ∀ shift : MvPolynomial (Fin n) ℚ, shift.vars ⊆ S.toFinset →
      zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn htb hns).get i)
          (mlProj (shift *
            Finset.univ.prod
              (fun i => (cookLevinFactorList M n hn htb hns).get i))) ∈
        profileSubspace zeroProfileHistogram (concreteWCanonical n hn4)

/-- The projected row-preservation fact explicitly provides the concrete row
map required by `CookLevinOneWindowSingletonQuotientConcreteRowMap`. -/
noncomputable def cookLevinOneWindowSingletonQuotientConcreteRowMap_of_rowPreservation
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hpres : CookLevinOneWindowSingletonQuotientConcreteWRowPreservation
      M n hn htb hns hn4) :
    CookLevinOneWindowSingletonQuotientConcreteRowMap
      M n hn htb hns hn4 where
  rowNormalForm := fun _ _ _ _ => PUnit.unit
  projected_row_mem_profileSubspace := by
    intro S hS shift hshift
    have hmem := hpres S hS shift hshift
    simpa [CookLevinOneWindowSingletonQuotientConcreteRowMap,
      zeroProfileConcreteNormalFormData_singletonZeroProfile_concreteW,
      zeroProfileConcreteNormalFormData_singletonZeroProfile,
      zeroProfileConcreteLocalChart_concreteW,
      zeroProfileConcreteLocalChart_of_submoduleFamily,
      concreteWCanonical] using hmem

/-- Paper-scale version of the projected row-preservation fact. -/
abbrev PaperScaleCookLevinOneWindowSingletonQuotientConcreteWRowPreservation
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  CookLevinOneWindowSingletonQuotientConcreteWRowPreservation
    M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four

/-- Paper-scale explicit row map from projected row preservation. -/
noncomputable def paperScale_cookLevinOneWindowSingletonQuotientConcreteRowMap_of_rowPreservation
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpres : PaperScaleCookLevinOneWindowSingletonQuotientConcreteWRowPreservation
      M htb hns) :
    CookLevinOneWindowSingletonQuotientConcreteRowMap
      M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four :=
  cookLevinOneWindowSingletonQuotientConcreteRowMap_of_rowPreservation
    M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four hpres

/-- Consequently, projected row preservation discharges the paper-scale
singleton-quotient type-budget bound. -/
theorem paperScale_singletonQuotient_typeBudgetBound_of_rowPreservation
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpres : PaperScaleCookLevinOneWindowSingletonQuotientConcreteWRowPreservation
      M htb hns) :
    PaperScaleSingletonQuotientZeroProfileBudget M htb hns :=
  paperScaleSingletonQuotientZeroProfileBudget_of_concreteRowMap
    M htb hns
    (paperScale_cookLevinOneWindowSingletonQuotientConcreteRowMap_of_rowPreservation
      M htb hns hpres)

/-- Final frontier constructor using the explicit singleton-quotient row map
obtained from projected row preservation. -/
def singletonQuotientFinalFrontier_of_rowPreservation
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan M htb hns)
    (hcert : PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificateOneZero
      M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowRowInclusion M htb hns)
    (hpres : PaperScaleCookLevinOneWindowSingletonQuotientConcreteWRowPreservation
      M htb hns)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ))
    (W_finite : ∀ τ, Module.Finite ℚ ↥(W τ))
    (W_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (active_data : CookLevinOneWindowPerTypeSpanningActiveData
      M (2 ^ 804) paperScale_ge_two htb hns W)
    (routeB_bridge : PaperScaleSingletonQuotientRouteBBridge
      M htb hns
      (paperScale_singletonQuotient_typeBudgetBound_of_rowPreservation
        M htb hns hpres)
      W W_finite W_dim active_data) :
    PaperScalePiPlusSingletonQuotientFinalFrontier M htb hns :=
  singletonQuotientFinalFrontier_of_concreteRowMap
    M htb hns hpoly hcert hnp
    (paperScale_cookLevinOneWindowSingletonQuotientConcreteRowMap_of_rowPreservation
      M htb hns hpres)
    W W_finite W_dim active_data routeB_bridge

/-! ## Axiom audit anchors -/

#print axioms cookLevinOneWindowSingletonQuotientConcreteRowMap_of_rowPreservation
#print axioms paperScale_cookLevinOneWindowSingletonQuotientConcreteRowMap_of_rowPreservation
#print axioms paperScale_singletonQuotient_typeBudgetBound_of_rowPreservation
#print axioms singletonQuotientFinalFrontier_of_rowPreservation

end PallLean.Paper93.DeepMath.PathC
