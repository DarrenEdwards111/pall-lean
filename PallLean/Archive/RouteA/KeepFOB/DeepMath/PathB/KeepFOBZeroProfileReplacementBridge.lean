import PallLean.Archive.RouteA.KeepFOB.DeepMath.PathB.KeepFOBPsideTemplateCollapseBridge
import PallLean.Paper93.DeepMath.PathB.ZeroProfileScalarClosure

set_option exponentiation.threshold 1000

/-!
# keepFOB zero-profile replacement bridge

This file records the honest zero-profile replacement surface for the
`keepFOB` P-side bridge.

The support-basis cardinality route is false, and the scalar singleton route
is false for the actual Cook-Levin zero-profile base product.  Because the
zero-profile template bound is `1`, the weakest remaining local hypothesis is
therefore the exact zero-histogram template shift-collapse blocker itself.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation
open TuringMachine (DTM)

attribute [local instance] Classical.dec

private theorem ge_four_of_ge_two_pow_804 {n : Nat} (hn : n ≥ 2 ^ 804) :
    n ≥ 4 := by
  have hfour : (4 : Nat) ≤ 2 ^ 804 := by
    calc
      (4 : Nat) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
  exact le_trans hfour hn

/-- Exact zero-profile template replacement hypothesis.

This is intentionally the existing shifted-base-product template-collapse
blocker, not the false explicit support-basis cardinality route and not a new
scalar reformulation. -/
def CookLevinZeroProfileTemplateReplacement
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  CookLevinZeroHistogramTemplateShiftCollapse M n hn htb hns

/-- The named replacement is exactly the existing zero-histogram template
shift-collapse blocker. -/
theorem cookLevinZeroHistogramTemplateShiftCollapse_of_zeroProfileReplacement
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hzero : CookLevinZeroProfileTemplateReplacement M n hn htb hns) :
    CookLevinZeroHistogramTemplateShiftCollapse M n hn htb hns :=
  hzero

/-- The exact replacement hypothesis is not currently discharged: by the
zero-profile template-cardinality-one reduction, it implies the false scalar
singleton obligation. -/
theorem not_CookLevinZeroProfileTemplateReplacement
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ¬ CookLevinZeroProfileTemplateReplacement M n hn htb hns := by
  intro hzero
  exact
    not_CookLevinZeroProfileTemplateScalarObligation M n hn htb hns
      ((cookLevinZeroHistogramTemplateShiftCollapse_iff_scalar
        M n hn htb hns).mp hzero)

/-- Active admissible profile cases plus the exact zero-profile replacement
prove bounded-profile template collapse. -/
theorem cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_activeCases_zeroProfileReplacement
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hzero : CookLevinZeroProfileTemplateReplacement M n hn htb hns)
    (hcases :
      CookLevinProfileTemplateCollapseActiveAdmissibleProfileCases
        M n hn htb hns) :
    WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
      M n hn htb hns :=
  cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_activeAdmissibleProfileCases
    M n hn htb hns hn4
    (cookLevinZeroHistogramTemplateShiftCollapse_of_zeroProfileReplacement
      M n hn htb hns hzero)
    hcases

/-- Per-instance `keepFOB` rich-projection target from active cases and the
exact zero-profile replacement hypothesis. -/
theorem cookLevinRichProjectionTarget_of_keepFOB_activeCases_zeroProfileReplacement
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hzero :
      CookLevinZeroProfileTemplateReplacement M n hn2 htb hns)
    (hcases :
      CookLevinProfileTemplateCollapseActiveAdmissibleProfileCases
        M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_keepFOB_boundedProfileTemplateCollapse
    M n hn hn2 htb hns
    (cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_activeCases_zeroProfileReplacement
      M n hn2 htb hns (ge_four_of_ge_two_pow_804 hn) hzero hcases)

/-- Uniform active-profile cases plus the exact zero-profile replacement
hypothesis imply the existing `keepFOB` rich-projection discharge. -/
theorem cookLevinRichProjectionDischarge_of_keepFOB_activeCases_zeroProfileReplacement
    (hzero :
      ∀ (M : DTM) (n : Nat) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroProfileTemplateReplacement M n hn2 htb hns)
    (hcases :
      ∀ (M : DTM) (n : Nat) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinProfileTemplateCollapseActiveAdmissibleProfileCases
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge := by
  intro M n hn hn2 htb hns _hdec
  exact
    cookLevinRichProjectionTarget_of_keepFOB_activeCases_zeroProfileReplacement
      M n hn hn2 htb hns
      (hzero M n hn2 htb hns)
      (hcases M n hn2 htb hns)

/-! ## Axiom audit anchors -/

#print axioms CookLevinZeroProfileTemplateReplacement
#print axioms cookLevinZeroHistogramTemplateShiftCollapse_of_zeroProfileReplacement
#print axioms not_CookLevinZeroProfileTemplateReplacement
#print axioms cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_activeCases_zeroProfileReplacement
#print axioms cookLevinRichProjectionTarget_of_keepFOB_activeCases_zeroProfileReplacement
#print axioms cookLevinRichProjectionDischarge_of_keepFOB_activeCases_zeroProfileReplacement

end PallLean.Paper93.DeepMath.PathB
