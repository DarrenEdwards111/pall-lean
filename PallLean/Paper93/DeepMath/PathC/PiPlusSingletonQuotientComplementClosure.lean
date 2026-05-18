import PallLean.Paper93.DeepMath.PathC.PiPlusExplicitSingletonQuotientRowMap

/-!
# Chosen-complement closure for the singleton quotient row map

The singleton-quotient projection in Route B is defined by `Classical.choose` as
projection onto an arbitrary complement of the singleton-shift subspace.  Hence
the direct row-preservation statement is equivalent in practice to proving that
this *chosen complement* is contained in the concrete zero-profile chart.

This file isolates and proves that reduction: if the chosen singleton-shift
complement lies in the canonical zero-profile `concreteW` subspace, then the
projected row-preservation lemma follows immediately, and therefore the
explicit row map/type-budget/final-frontier constructors from the previous file
can be used.
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

/-- The exact complement-closure fact needed because
`zeroProfileQuotientBySingletonShiftProjection` projects onto the chosen
complement of singleton shifts. -/
def CookLevinOneWindowSingletonQuotientComplementLeConcreteW
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4) : Prop :=
  zeroProfileSingletonShiftComplement
      (fun i => (cookLevinFactorList M n hn htb hns).get i) ≤
    profileSubspace zeroProfileHistogram (concreteWCanonical n hn4)

/-- Complement closure implies projected row preservation: the quotient
projection always lands in the chosen complement, so if that complement is
inside `concreteW`, every projected row is in `concreteW`. -/
theorem singletonQuotientConcreteWRowPreservation_of_complementLeConcreteW
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hcomp : CookLevinOneWindowSingletonQuotientComplementLeConcreteW
      M n hn htb hns hn4) :
    CookLevinOneWindowSingletonQuotientConcreteWRowPreservation
      M n hn htb hns hn4 := by
  intro S hS shift hshift
  let factors : Fin (cookLevinFactorList M n hn htb hns).length →
      MvPolynomial (Fin n) ℚ :=
    fun i => (cookLevinFactorList M n hn htb hns).get i
  exact hcomp (by
    change zeroProfileQuotientBySingletonShiftProjection factors
        (mlProj (shift * Finset.univ.prod factors)) ∈
      zeroProfileSingletonShiftComplement factors
    simp [zeroProfileQuotientBySingletonShiftProjection, factors,
      Submodule.IsCompl.projection_apply_mem])

/-- Paper-scale complement closure. -/
abbrev PaperScaleCookLevinOneWindowSingletonQuotientComplementLeConcreteW
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  CookLevinOneWindowSingletonQuotientComplementLeConcreteW
    M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four

/-- Paper-scale projected row preservation from chosen-complement closure. -/
theorem paperScale_singletonQuotientConcreteWRowPreservation_of_complementLeConcreteW
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomp : PaperScaleCookLevinOneWindowSingletonQuotientComplementLeConcreteW
      M htb hns) :
    PaperScaleCookLevinOneWindowSingletonQuotientConcreteWRowPreservation
      M htb hns :=
  singletonQuotientConcreteWRowPreservation_of_complementLeConcreteW
    M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four hcomp

/-- Paper-scale explicit row map from chosen-complement closure. -/
noncomputable def paperScale_cookLevinOneWindowSingletonQuotientConcreteRowMap_of_complementLeConcreteW
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomp : PaperScaleCookLevinOneWindowSingletonQuotientComplementLeConcreteW
      M htb hns) :
    CookLevinOneWindowSingletonQuotientConcreteRowMap
      M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four :=
  paperScale_cookLevinOneWindowSingletonQuotientConcreteRowMap_of_rowPreservation
    M htb hns
    (paperScale_singletonQuotientConcreteWRowPreservation_of_complementLeConcreteW
      M htb hns hcomp)

/-- Paper-scale type-budget closeout from chosen-complement closure. -/
theorem paperScale_singletonQuotient_typeBudgetBound_of_complementLeConcreteW
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomp : PaperScaleCookLevinOneWindowSingletonQuotientComplementLeConcreteW
      M htb hns) :
    PaperScaleSingletonQuotientZeroProfileBudget M htb hns :=
  paperScale_singletonQuotient_typeBudgetBound_of_rowPreservation
    M htb hns
    (paperScale_singletonQuotientConcreteWRowPreservation_of_complementLeConcreteW
      M htb hns hcomp)

/-! ## Axiom audit anchors -/

#print axioms singletonQuotientConcreteWRowPreservation_of_complementLeConcreteW
#print axioms paperScale_singletonQuotientConcreteWRowPreservation_of_complementLeConcreteW
#print axioms paperScale_cookLevinOneWindowSingletonQuotientConcreteRowMap_of_complementLeConcreteW
#print axioms paperScale_singletonQuotient_typeBudgetBound_of_complementLeConcreteW

end PallLean.Paper93.DeepMath.PathC
