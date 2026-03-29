import PallLean.MonomialSupportIdentityReduction

/-!
# ExponentIndicatorReduction

Final atomic reduction for the exponent/support side.

For a multilinear exponent vector `α`, the statement

  α i = if i ∈ α.support then 1 else 0

reduces to the single atomic fact that support members carry exponent exactly `1`.
The zero case is already built into `Finsupp.mem_support_iff`.
-/

namespace ExponentIndicatorReduction

open SPDP
open MultilinearSPDP
open MonomialSupportIdentityReduction

/-- Atomic support-value fact for multilinear exponent vectors. -/
def SupportMemberHasValueOne {n : ℕ} : Prop :=
  ∀ (α : Fin n →₀ ℕ),
    Finsupp.IsMultilinear α →
    ∀ i : Fin n, i ∈ α.support → α i = 1

/-- The atomic support-value fact implies the support-indicator theorem. -/
theorem multilinearExponentIsSupportIndicator_of_supportValue
    {n : ℕ}
    (hval : SupportMemberHasValueOne (n := n)) :
    MultilinearExponentIsSupportIndicator (n := n) := by
  intro α hml i
  by_cases hi : i ∈ α.support
  · rw [if_pos hi]
    exact hval α hml i hi
  · rw [if_neg hi]
    exact by
      rw [Finsupp.mem_support_iff] at hi
      exact hi

end ExponentIndicatorReduction
