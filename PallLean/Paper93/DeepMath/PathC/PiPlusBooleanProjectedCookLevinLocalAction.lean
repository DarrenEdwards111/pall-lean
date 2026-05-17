import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedLocalWindowCertificate

/-!
# The missing Cook--Levin local-action lemma for Boolean-projected Pi+

This file gives the remaining Route-C mathematical payload a single theorem
surface.  The point is to stop proliferating frontier packages: proving
`PaperScalePiPlusBooleanProjectedCookLevinLocalActionLemma` is exactly the local
Boolean-quotient Cook--Levin action theorem needed to fill the existing final
local-window certificate.

The lemma is intentionally generator-level on the P side and subspace-level on
the NP side:

* P side: every final-window generator of `Pi+ᵦ(compiledPoly)` has a raw
  `Pi+ᵦ` pullback in the one-window enlarged source SPDP subspace;
* NP side: the source final-window compiled SPDP subspace embeds into the
  Boolean-projected target final-window subspace.

This is not an axiom and not a fake proof.  It is the single missing lemma name
to attack next.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine
open SymmetricPowerBound

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- The concrete missing Route-C Cook--Levin local-action lemma for
Boolean-projected `Pi+ᵦ` at arbitrary SAT scale.

For `extraK = 1`, `extraL = 0`, this is the theorem that should be proved by
an actual local Cook--Levin/Boolean-quotient analysis of `Pi+ᵦ`. -/
structure PiPlusBooleanProjectedCookLevinLocalActionLemma
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop where
  /-- P-side local action: pull back each final-window generator of the
  Boolean-projected compiled polynomial into the enlarged source window. -/
  p_compiled_generator_pullback :
    PiPlusBooleanProjectedWindowedCompiledRawPullbackMembership
      extraK extraL M n hn2 htb hns piP
  /-- NP-side local action: preserve the final-window source compiled subspace
  inside the Boolean-projected target compiled subspace. -/
  np_compiled_window_preservation :
    PiPlusBooleanProjectedNPWindowSubspaceInclusion M n hn2 htb hns piP

/-- Paper-scale one-window name for the single missing Route-C lemma. -/
abbrev PaperScalePiPlusBooleanProjectedCookLevinLocalActionLemma
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedCookLevinLocalActionLemma 1 0
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- The missing local-action lemma fills the existing local-window certificate.
This is the exact bridge from the theorem we need to prove to the final Route-C
certificate shape already consumed downstream. -/
theorem localWindowCertificate_of_cookLevinLocalActionLemma
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hlocal : PiPlusBooleanProjectedCookLevinLocalActionLemma
      extraK extraL M n hn2 htb hns piP) :
    PiPlusBooleanProjectedCompiledLocalWindowCertificate
      extraK extraL M n hn2 htb hns piP where
  p_side_window_transport :=
    compiledPSubspaceInclusion_of_compiledRawPullbackMembership
      extraK extraL M n hn2 htb hns piP
      hlocal.p_compiled_generator_pullback
  np_window_preservation := hlocal.np_compiled_window_preservation

/-- Paper-scale specialization: proving the single missing local-action lemma
is enough to supply the Route-C local-window certificate used in the final
closure theorem. -/
theorem paperScale_localWindowCertificate_of_cookLevinLocalActionLemma
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hlocal : PaperScalePiPlusBooleanProjectedCookLevinLocalActionLemma
      M htb hns) :
    PaperScalePiPlusBooleanProjectedOneWindowLocalWindowCertificate M htb hns :=
  localWindowCertificate_of_cookLevinLocalActionLemma
    1 0 M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hlocal

/-- Final Route-C-only closure surface: the single missing local-action lemma,
together with the already explicit Route-B final data, fills the existing final
local-window package. -/
def localWindowFinalData_of_cookLevinLocalActionLemma
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hlocal : PaperScalePiPlusBooleanProjectedCookLevinLocalActionLemma
      M htb hns)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ))
    (W_finite : ∀ τ, Module.Finite ℚ ↥(W τ))
    (W_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (zero_common_span :
      CookLevinOneWindowZeroHistogramShiftCommonSpan
        M (2 ^ 804) paperScale_ge_two htb hns)
    (per_type_spanning :
      CookLevinOneWindowPerTypeSpanningActiveAdmissibleProfileCases
        M (2 ^ 804) paperScale_ge_two htb hns W) :
    PaperScalePiPlusBooleanProjectedLocalWindowFinalData M htb hns where
  route_c_local_window :=
    paperScale_localWindowCertificate_of_cookLevinLocalActionLemma
      M htb hns hlocal
  W := W
  W_finite := W_finite
  W_dim := W_dim
  zero_common_span := zero_common_span
  per_type_spanning := per_type_spanning

/-- If the single missing Route-C lemma and the two Route-B blockers are proved,
the final SAT-decider contradiction fires immediately. -/
theorem no_decidesSAT_at_paperScale_of_cookLevinLocalActionLemma
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hlocal : PaperScalePiPlusBooleanProjectedCookLevinLocalActionLemma
      M htb hns)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ))
    (W_finite : ∀ τ, Module.Finite ℚ ↥(W τ))
    (W_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (zero_common_span :
      CookLevinOneWindowZeroHistogramShiftCommonSpan
        M (2 ^ 804) paperScale_ge_two htb hns)
    (per_type_spanning :
      CookLevinOneWindowPerTypeSpanningActiveAdmissibleProfileCases
        M (2 ^ 804) paperScale_ge_two htb hns W) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_localWindowFinalData M htb hns
    (localWindowFinalData_of_cookLevinLocalActionLemma
      M htb hns hlocal W W_finite W_dim zero_common_span per_type_spanning)

/-! ## Axiom audit anchors -/

#print axioms localWindowCertificate_of_cookLevinLocalActionLemma
#print axioms paperScale_localWindowCertificate_of_cookLevinLocalActionLemma
#print axioms localWindowFinalData_of_cookLevinLocalActionLemma
#print axioms no_decidesSAT_at_paperScale_of_cookLevinLocalActionLemma

end PallLean.Paper93.DeepMath.PathC
