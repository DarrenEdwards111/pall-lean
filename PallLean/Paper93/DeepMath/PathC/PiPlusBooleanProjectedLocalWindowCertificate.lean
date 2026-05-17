import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedFinalFrontier

/-!
# Local-window certificate for the final Pi+ frontier

The final frontier has been narrowed to two Route-C subspace inclusions plus the
Route-B one-window blockers.  Directly proving those inclusions independently
would duplicate the same missing local algebra: Boolean-projected `Pi+` must
transport the final Cook--Levin SPDP windows in the expected directions.

This file packages that missing algebra as one bidirectional local-window
certificate and proves that it closes the Route-C side of the final frontier.
It is intentionally not an axiom and not a fake proof: it is a concrete Prop
whose fields are exactly the two subspace inclusions needed downstream.
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

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- A single Route-C local-window certificate for the Boolean-projected `Pi+`
action on the compiled Cook--Levin polynomial.

* `p_side_window_transport` is the one-extra-derivative P-side inclusion.
* `np_window_preservation` is same-window NP-side preservation.

This is the real remaining Route-C algebraic content after all packaging noise
has been removed. -/
structure PiPlusBooleanProjectedCompiledLocalWindowCertificate
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop where
  p_side_window_transport :
    PiPlusBooleanProjectedCompiledPSubspaceInclusion
      extraK extraL M n hn2 htb hns piP
  np_window_preservation :
    PiPlusBooleanProjectedNPWindowSubspaceInclusion
      M n hn2 htb hns piP

/-- Paper-scale one-window abbreviation for the local-window certificate. -/
abbrev PaperScalePiPlusBooleanProjectedOneWindowLocalWindowCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedCompiledLocalWindowCertificate 1 0
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- The local-window certificate supplies the P-side subspace inclusion. -/
theorem compiledPSubspaceInclusion_of_localWindowCertificate
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hcert : PiPlusBooleanProjectedCompiledLocalWindowCertificate
      extraK extraL M n hn2 htb hns piP) :
    PiPlusBooleanProjectedCompiledPSubspaceInclusion
      extraK extraL M n hn2 htb hns piP :=
  hcert.p_side_window_transport

/-- The local-window certificate supplies NP-window rank nondecrease. -/
theorem npWindowRankNondecreasing_of_localWindowCertificate
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hcert : PiPlusBooleanProjectedCompiledLocalWindowCertificate
      extraK extraL M n hn2 htb hns piP) :
    PiPlusBooleanProjectedNPWindowRankNondecreasing M n hn2 htb hns piP :=
  npWindowRankNondecreasing_of_npWindowSubspaceInclusion
    M n hn2 htb hns piP hcert.np_window_preservation

/-- Final paper-scale data with the Route-C side compressed to the single
local-window certificate and the Route-B side kept as the corrected two blocker
package. -/
structure PaperScalePiPlusBooleanProjectedLocalWindowFinalData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) where
  route_c_local_window :
    PaperScalePiPlusBooleanProjectedOneWindowLocalWindowCertificate M htb hns
  W : ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ)
  W_finite : ∀ τ, Module.Finite ℚ ↥(W τ)
  W_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3
  zero_common_span :
    CookLevinOneWindowZeroHistogramShiftCommonSpan
      M (2 ^ 804) paperScale_ge_two htb hns
  per_type_spanning :
    CookLevinOneWindowPerTypeSpanningActiveAdmissibleProfileCases
      M (2 ^ 804) paperScale_ge_two htb hns W

/-- The local-window final data fills the previous final-frontier package. -/
def finalFrontierData_of_localWindowFinalData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusBooleanProjectedLocalWindowFinalData M htb hns) :
    PaperScalePiPlusBooleanProjectedFinalFrontierData M htb hns where
  compiled_p_subspace_inclusion := D.route_c_local_window.p_side_window_transport
  W := D.W
  W_finite := D.W_finite
  W_dim := D.W_dim
  zero_common_span := D.zero_common_span
  per_type_spanning := D.per_type_spanning
  np_subspace_inclusion := D.route_c_local_window.np_window_preservation

/-- Final theorem using the unified Route-C local-window certificate. -/
theorem no_decidesSAT_at_paperScale_of_localWindowFinalData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusBooleanProjectedLocalWindowFinalData M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_finalFrontierData
    M htb hns (finalFrontierData_of_localWindowFinalData M htb hns D)

/-! ## Axiom audit anchors -/

#print axioms compiledPSubspaceInclusion_of_localWindowCertificate
#print axioms npWindowRankNondecreasing_of_localWindowCertificate
#print axioms finalFrontierData_of_localWindowFinalData
#print axioms no_decidesSAT_at_paperScale_of_localWindowFinalData

end PallLean.Paper93.DeepMath.PathC
