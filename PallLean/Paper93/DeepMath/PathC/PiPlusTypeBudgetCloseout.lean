import PallLean.Paper93.DeepMath.PathC.PiPlusOneWindowConcreteRowMapBudget

/-!
# Type-budget closeout for the singleton quotient zero-profile route

This file exposes the exact paper-scale type-budget inequality as a standalone
closeout theorem.  The only remaining mathematical input is the concrete
singleton-quotient zero-profile row map; the finite-normal-form/type-budget
arithmetic itself is discharged here.
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

/-- The exact paper-scale singleton-quotient type-budget bound, discharged from
the concrete one-window singleton-quotient row map. -/
theorem paperScale_singletonQuotient_typeBudgetBound_of_concreteRowMap
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hmap : CookLevinOneWindowSingletonQuotientConcreteRowMap
      M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four) :
    zeroProfileSingletonQuotientProjectedTypeBudget
        (Nat.log 2 (2 ^ 804) + 1)
        (fun i =>
          (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i) ≤
      withinProfileBound (Nat.log 2 (2 ^ 804) + 1) :=
  paperScaleSingletonQuotientZeroProfileBudget_of_concreteRowMap
    M htb hns hmap

/-- Same result stated through the named zero-profile budget predicate. -/
theorem paperScale_singletonQuotient_zeroBudget_of_concreteRowMap
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hmap : CookLevinOneWindowSingletonQuotientConcreteRowMap
      M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four) :
    PaperScaleSingletonQuotientZeroProfileBudget M htb hns :=
  paperScale_singletonQuotient_typeBudgetBound_of_concreteRowMap
    M htb hns hmap

/-! ## Axiom audit anchors -/

#print axioms paperScale_singletonQuotient_typeBudgetBound_of_concreteRowMap
#print axioms paperScale_singletonQuotient_zeroBudget_of_concreteRowMap

end PallLean.Paper93.DeepMath.PathC
