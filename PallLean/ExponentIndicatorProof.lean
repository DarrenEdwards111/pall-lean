import PallLean.ExponentIndicatorReduction

/-!
# ExponentIndicatorProof

A genuinely proved atomic fact on the ambient side:
for a multilinear exponent vector, every support member has exponent exactly `1`.
-/

namespace ExponentIndicatorProof

open SPDP
open MultilinearSPDP
open ExponentIndicatorReduction

/-- Proved atomic fact: support members of a multilinear exponent vector have value 1. -/
theorem supportMemberHasValueOne
    {n : ℕ} :
    SupportMemberHasValueOne (n := n) := by
  intro α hml i hi
  have hne : α i ≠ 0 := by
    exact Finsupp.mem_support_iff.mp hi
  have hle : α i ≤ 1 := hml i
  omega

end ExponentIndicatorProof
