import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedLocalWindowCertificate
import PallLean.Paper93.DeepMath.PathC.PiPlusRouteBOneWindowPerTypeDischarge

/-!
# Final local-window assembly with local Route-B active data

This file plugs the new one-window per-type discharge data into the final
`Pi+ᵦ` local-window closure theorem.  The remaining final data is now:

* Route C: the Boolean-projected `Pi+` local-window certificate;
* Route B zero profile: the corrected common-span blocker;
* Route B nonzero profiles: local one-window derivative membership plus
  shift/`mlProj` closure data.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine
open SymmetricPowerBound

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- Final paper-scale package after replacing the nonzero per-type spanning
blocker by the smaller local active-data interface. -/
structure PaperScalePiPlusBooleanProjectedLocalWindowActiveData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) where
  route_c_local_window :
    PaperScalePiPlusBooleanProjectedOneWindowLocalWindowCertificate M htb hns
  W : ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ)
  W_finite : ∀ τ, Module.Finite ℚ ↥(W τ)
  W_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3
  zero_common_span :
    CookLevinOneWindowZeroHistogramShiftCommonSpan
      M (2 ^ 804) paperScale_ge_two htb hns
  per_type_active_data :
    CookLevinOneWindowPerTypeSpanningActiveData
      M (2 ^ 804) paperScale_ge_two htb hns W

/-- Local active data fills the previous final local-window package. -/
def localWindowFinalData_of_activeData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusBooleanProjectedLocalWindowActiveData M htb hns) :
    PaperScalePiPlusBooleanProjectedLocalWindowFinalData M htb hns where
  route_c_local_window := D.route_c_local_window
  W := D.W
  W_finite := D.W_finite
  W_dim := D.W_dim
  zero_common_span := D.zero_common_span
  per_type_spanning :=
    paperScale_cookLevinOneWindowPerTypeSpanningActiveAdmissibleProfileCases_of_activeData
      M htb hns D.W D.per_type_active_data

/-- Final theorem with the Route-B nonzero side expressed as local active data. -/
theorem no_decidesSAT_at_paperScale_of_localWindowActiveData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusBooleanProjectedLocalWindowActiveData M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_localWindowFinalData
    M htb hns (localWindowFinalData_of_activeData M htb hns D)

/-! ## Axiom audit anchors -/

#print axioms localWindowFinalData_of_activeData
#print axioms no_decidesSAT_at_paperScale_of_localWindowActiveData

end PallLean.Paper93.DeepMath.PathC
