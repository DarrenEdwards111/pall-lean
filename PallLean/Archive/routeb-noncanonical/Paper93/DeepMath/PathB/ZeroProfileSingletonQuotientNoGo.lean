import PallLean.Paper93.DeepMath.PathB.ZeroProfileNormalFormInstantiationProgress

/-!
# Singleton-quotient zero-profile budget obstruction

The singleton quotient is the right correction to the raw support route, but
the current residual payment theorem pays the whole ambient singleton-shift
span with budget `n`.  At the paper-scale endpoint this cannot fit inside
`withinProfileBound (Nat.log 2 n)`.
-/

namespace PallLean
namespace Paper93
namespace DeepMath
namespace PathB

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP SPDP

attribute [local instance] Classical.dec

/-- At `n = 2^804`, no singleton-quotient zero-profile certificate can pay the
ambient singleton residual inside the within-profile budget. -/
theorem not_zeroProfileSingletonQuotientBudget_two_pow_804
    {typeBudget : ℕ} :
    ¬ typeBudget + (2 : ℕ) ^ 804 ≤
        withinProfileBound (Nat.log 2 ((2 : ℕ) ^ 804)) := by
  intro hbudget
  have hambient :
      (2 : ℕ) ^ 804 ≤ typeBudget + (2 : ℕ) ^ 804 :=
    Nat.le_add_left ((2 : ℕ) ^ 804) typeBudget
  exact
    (not_lt_of_ge (le_trans hambient hbudget))
      withinProfileBound_log_two_pow_804_lt_ambient

/-- Consequently, the current singleton-quotient normal-form row-map gate
cannot be instantiated at the paper-scale endpoint if it has to pay the
ambient `+ n` singleton residual.  A positive route must remove those
directions from the target or pay a strictly smaller residual. -/
theorem not_exists_cookLevinZeroProfileSingletonQuotientNormalFormRowMap_two_pow_804
    (M : DTM)
    (hn2 : (2 : ℕ) ^ 804 ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ (2 : ℕ) ^ 804) :
    ¬ ∃ typeBudget : ℕ,
      ∃ F :
        ZeroProfileProjectedNormalFormFamily ((2 : ℕ) ^ 804)
          (Nat.log 2 ((2 : ℕ) ^ 804)) typeBudget,
        Nonempty
          (ZeroProfileProjectedNormalFormRowMap
            (fun i =>
              (cookLevinFactorList M ((2 : ℕ) ^ 804) hn2 htb hns).get i)
            (zeroProfileQuotientBySingletonShiftProjection
              (fun i =>
                (cookLevinFactorList M ((2 : ℕ) ^ 804) hn2 htb hns).get i))
            F) ∧
        typeBudget + (2 : ℕ) ^ 804 ≤
          withinProfileBound (Nat.log 2 ((2 : ℕ) ^ 804)) := by
  rintro ⟨typeBudget, F, _hmap, hbudget⟩
  exact not_zeroProfileSingletonQuotientBudget_two_pow_804
    (typeBudget := typeBudget) hbudget

/-- The same budget obstruction for the lower-level quotient type-map gate. -/
theorem not_exists_cookLevinZeroProfileSingletonQuotientTypeMap_two_pow_804
    (M : DTM)
    (hn2 : (2 : ℕ) ^ 804 ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ (2 : ℕ) ^ 804) :
    ¬ ∃ typeBudget : ℕ,
      ∃ A : ZeroProfileQuotientTypeAlphabet ((2 : ℕ) ^ 804) typeBudget,
        Nonempty
          (ZeroProfileProjectedGeneratorTypeMap
            (Nat.log 2 ((2 : ℕ) ^ 804))
            (fun i =>
              (cookLevinFactorList M ((2 : ℕ) ^ 804) hn2 htb hns).get i)
            A
            (zeroProfileQuotientBySingletonShiftProjection
              (fun i =>
                (cookLevinFactorList M ((2 : ℕ) ^ 804) hn2 htb hns).get i))) ∧
        typeBudget + (2 : ℕ) ^ 804 ≤
          withinProfileBound (Nat.log 2 ((2 : ℕ) ^ 804)) := by
  rintro ⟨typeBudget, A, _hmap, hbudget⟩
  exact not_zeroProfileSingletonQuotientBudget_two_pow_804
    (typeBudget := typeBudget) hbudget

/-! ## Axiom audit anchors -/

#print axioms not_zeroProfileSingletonQuotientBudget_two_pow_804
#print axioms not_exists_cookLevinZeroProfileSingletonQuotientNormalFormRowMap_two_pow_804
#print axioms not_exists_cookLevinZeroProfileSingletonQuotientTypeMap_two_pow_804

end PathB
end DeepMath
end Paper93
end PallLean
