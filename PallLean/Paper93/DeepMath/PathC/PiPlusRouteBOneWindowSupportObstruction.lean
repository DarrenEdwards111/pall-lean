import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedLocalWindowCertificate
import PallLean.Paper93.DeepMath.PathB.ZeroProfileSupportCardBound

/-!
# One-window zero-profile support-basis obstruction

The corrected one-window zero-profile blocker is a common-span statement, not a
support-basis cardinality statement.  A tempting route is to reuse the explicit
support basis from `ZeroProfileShiftSpanProgress` at `κ = log₂ n + 1` and prove
its cardinality fits inside `withinProfileBound κ`.

At paper scale this route is impossible: the support-basis cardinality bound
already forces `n ≤ withinProfileBound (log₂ n + 1)`, but for `n = 2^804` the
right-hand side is only `(806)^8`.

This file records that obstruction kernel-cleanly so the next attack does not
waste time on the false support-basis route.  The actual remaining target stays
`CookLevinOneWindowZeroHistogramShiftCommonSpan`, which must use quotient/common
span structure beyond the naive support basis.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine
open SymmetricPowerBound
open WithinProfileBound

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000
set_option maxHeartbeats 1000000

/-- Any one-window support-basis cardinality proof would force the ambient
variable count to fit inside the one-window within-profile budget. -/
theorem ambient_le_withinProfileBound_of_oneWindowSupportBasisCardBound_le
    {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hbound : zeroProfileShiftSupportBasisCardBound (Nat.log 2 n + 1) factors ≤
      withinProfileBound (Nat.log 2 n + 1)) :
    n ≤ withinProfileBound (Nat.log 2 n + 1) :=
  ambient_le_withinProfileBound_of_zeroProfileShiftSupportBasisCardBound_le
    (Nat.log 2 n + 1) factors (by omega) hbound

/-- At paper scale, the one-window within-profile budget is still far smaller
than the ambient variable count. -/
theorem paperScale_oneWindow_withinProfileBound_lt_ambient :
    withinProfileBound (Nat.log 2 ((2 : ℕ) ^ 804) + 1) < (2 : ℕ) ^ 804 := by
  rw [Nat.log_pow (by norm_num : (1 : ℕ) < 2)]
  norm_num [withinProfileBound]

/-- Therefore the support-basis-cardinality route to the one-window zero-profile
common span is impossible at paper scale. -/
theorem not_paperScale_oneWindowSupportBasisCardBound_le_withinProfileBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    ¬ zeroProfileShiftSupportBasisCardBound
        (Nat.log 2 ((2 : ℕ) ^ 804) + 1)
        (fun i => (cookLevinFactorList M ((2 : ℕ) ^ 804)
          paperScale_ge_two htb hns).get i)
      ≤ withinProfileBound (Nat.log 2 ((2 : ℕ) ^ 804) + 1) := by
  intro hbound
  have hamb : (2 : ℕ) ^ 804 ≤
      withinProfileBound (Nat.log 2 ((2 : ℕ) ^ 804) + 1) :=
    ambient_le_withinProfileBound_of_oneWindowSupportBasisCardBound_le
      (fun i => (cookLevinFactorList M ((2 : ℕ) ^ 804)
        paperScale_ge_two htb hns).get i)
      hbound
  exact not_le_of_gt paperScale_oneWindow_withinProfileBound_lt_ambient hamb

/-- The same obstruction applies to the support-basis sufficient theorem used
in the current one-window mixed frontier. -/
theorem not_paperScale_oneWindowZeroCommonSpan_via_supportBasisCardBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    ¬ (zeroProfileShiftSupportBasisCardBound
          (Nat.log 2 ((2 : ℕ) ^ 804) + 1)
          (fun i => (cookLevinFactorList M ((2 : ℕ) ^ 804)
            paperScale_ge_two htb hns).get i)
        ≤ withinProfileBound (Nat.log 2 ((2 : ℕ) ^ 804) + 1) ∧
      CookLevinOneWindowZeroHistogramShiftCommonSpan
        M ((2 : ℕ) ^ 804) paperScale_ge_two htb hns) := by
  intro h
  exact not_paperScale_oneWindowSupportBasisCardBound_le_withinProfileBound
    M htb hns h.1

/-! ## Axiom audit anchors -/

#print axioms ambient_le_withinProfileBound_of_oneWindowSupportBasisCardBound_le
#print axioms paperScale_oneWindow_withinProfileBound_lt_ambient
#print axioms not_paperScale_oneWindowSupportBasisCardBound_le_withinProfileBound
#print axioms not_paperScale_oneWindowZeroCommonSpan_via_supportBasisCardBound

end PallLean.Paper93.DeepMath.PathC
