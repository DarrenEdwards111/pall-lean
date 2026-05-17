import PallLean.Paper93.DeepMath.PathC.PiPlusPayloadCloseout
import PallLean.Paper93.DeepMath.PathC.PiPlusRouteBOneWindowZeroCommonSpanObstruction
import PallLean.Paper93.DeepMath.PathB.ZeroProfileQuotientTypeCompression

/-!
# Projected payload closeout for the corrected Pi+ route

The previous payload structure used an unprojected one-window zero-profile
common-span socket.  `PiPlusRouteBOneWindowZeroCommonSpanObstruction` proves that
socket is false at paper scale: it already contains all singleton-shift rows and
therefore needs ambient-size budget.

This file introduces the replacement interface: the zero-profile socket is now
projected/quotiented.  We deliberately do **not** pretend this alone closes the
P-side bound.  Instead, the final theorem exposes the new honest socket:

* prove the Pi+ raw-pullback row certificate;
* prove the NP-window row inclusion;
* prove the projected/quotient zero-profile certificate;
* prove the remaining Route-B bridge from that projected zero-profile data and
  active-profile data to the inclusive P-side rank bound.
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

/-- Corrected one-window zero-profile target: common span only after a chosen
linear projection/quotient.  This is the replacement for the unprojected
`CookLevinOneWindowZeroHistogramShiftCommonSpan`, which is false at paper scale.
-/
def CookLevinOneWindowProjectedZeroHistogramShiftCommonSpan
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project : MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ) : Prop :=
  ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n + 1)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    project
    (withinProfileBound (Nat.log 2 n + 1))

/-- The old unprojected socket implies every projected socket.  This is useful
for compatibility only; the old socket is later proved impossible at paper
scale. -/
theorem cookLevinOneWindowProjectedZeroHistogramShiftCommonSpan_of_unprojected
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project : MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hzero : CookLevinOneWindowZeroHistogramShiftCommonSpan M n hn htb hns) :
    CookLevinOneWindowProjectedZeroHistogramShiftCommonSpan
      M n hn htb hns project := by
  classical
  have hid : ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n + 1)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (LinearMap.id : MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
      (withinProfileBound (Nat.log 2 n + 1)) := by
    rcases hzero with ⟨G, hG_card, hG_span⟩
    refine ⟨G, hG_card, ?_⟩
    intro q hq
    rcases hq with ⟨row, hrow, rfl⟩
    simpa using hG_span hrow
  exact
    zeroProfileProjectedCommonSpanWithBudget_of_id_projectedCommonSpan
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      project hid

/-- Paper-scale abbreviation for the corrected projected zero-profile socket. -/
abbrev PaperScaleCookLevinOneWindowProjectedZeroHistogramShiftCommonSpan
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (project :
      MvPolynomial (Fin (2 ^ 804)) ℚ →ₗ[ℚ]
        MvPolynomial (Fin (2 ^ 804)) ℚ) : Prop :=
  CookLevinOneWindowProjectedZeroHistogramShiftCommonSpan
    M (2 ^ 804) paperScale_ge_two htb hns project

/-- The singleton quotient is the canonical candidate projection for the new
zero-profile socket: it kills the singleton-shift obstruction isolated by the
previous file. -/
noncomputable abbrev paperScaleCookLevinSingletonQuotientProjection
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    MvPolynomial (Fin (2 ^ 804)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (2 ^ 804)) ℚ :=
  zeroProfileQuotientBySingletonShiftProjection
    (fun i =>
      (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i)

/-- Projected payload data: the obsolete unprojected zero-profile field is
replaced by an explicit projection and projected zero-profile certificate.

This is intentionally a frontier object, not a fake final proof package.  The
missing theorem is the Route-B bridge that consumes projected zero-profile data
without reintroducing the impossible unprojected socket. -/
structure PaperScalePiPlusProjectedPayloadData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Type where
  p_windowed_row_certificate :
    PaperScalePiPlusBooleanProjectedWindowedRawPullbackRowCertificate
      1 0 M htb hns
  np_window_row_inclusion :
    PaperScalePiPlusBooleanProjectedNPWindowRowInclusion M htb hns
  project :
    MvPolynomial (Fin (2 ^ 804)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (2 ^ 804)) ℚ
  project_idempotent : project.comp project = project
  killsSingleton :
    ZeroProfileProjectionKillsSingletonShifts
      (fun i =>
        (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i)
      project
  projected_zero_common_span :
    PaperScaleCookLevinOneWindowProjectedZeroHistogramShiftCommonSpan
      M htb hns project
  W : ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ)
  W_finite : ∀ τ, Module.Finite ℚ ↥(W τ)
  W_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3
  active_data :
    CookLevinOneWindowPerTypeSpanningActiveData
      M (2 ^ 804) paperScale_ge_two htb hns W

/-- Candidate singleton-quotient payload specialization.  This is the shape of
the next concrete zero-profile target; the remaining burden is to prove the
projected common span for this projection. -/
structure PaperScalePiPlusSingletonQuotientPayloadData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Type where
  p_windowed_row_certificate :
    PaperScalePiPlusBooleanProjectedWindowedRawPullbackRowCertificate
      1 0 M htb hns
  np_window_row_inclusion :
    PaperScalePiPlusBooleanProjectedNPWindowRowInclusion M htb hns
  projected_zero_common_span :
    PaperScaleCookLevinOneWindowProjectedZeroHistogramShiftCommonSpan
      M htb hns
      (paperScaleCookLevinSingletonQuotientProjection M htb hns)
  W : ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ)
  W_finite : ∀ τ, Module.Finite ℚ ↥(W τ)
  W_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3
  active_data :
    CookLevinOneWindowPerTypeSpanningActiveData
      M (2 ^ 804) paperScale_ge_two htb hns W

/-- The singleton-quotient payload is a projected payload with the canonical
projection and its proved singleton-killing/idempotence facts. -/
noncomputable def projectedPayloadData_of_singletonQuotientPayloadData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusSingletonQuotientPayloadData M htb hns) :
    PaperScalePiPlusProjectedPayloadData M htb hns where
  p_windowed_row_certificate := D.p_windowed_row_certificate
  np_window_row_inclusion := D.np_window_row_inclusion
  project := paperScaleCookLevinSingletonQuotientProjection M htb hns
  project_idempotent := by
    change
      (zeroProfileQuotientBySingletonShiftProjection
          (fun i =>
            (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i)).comp
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i =>
            (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i)) =
      zeroProfileQuotientBySingletonShiftProjection
        (fun i =>
          (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i)
    exact zeroProfileQuotientBySingletonShiftProjection_idempotent
      (fun i =>
        (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i)
  killsSingleton := by
    change
      ZeroProfileProjectionKillsSingletonShifts
        (fun i =>
          (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i)
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i =>
            (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i))
    exact zeroProfileQuotientBySingletonShiftProjection_killsSingletonShifts
      (fun i =>
        (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i)
  projected_zero_common_span := D.projected_zero_common_span
  W := D.W
  W_finite := D.W_finite
  W_dim := D.W_dim
  active_data := D.active_data

/-- The exact remaining P-side bridge after switching to projected zero-profile
data.  Proving this, rather than proving the false unprojected zero socket, is
the next real Route-B mathematical payload. -/
def PaperScaleProjectedPayloadRouteBBridge
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (_D : PaperScalePiPlusProjectedPayloadData M htb hns) : Prop :=
  RouteBSATWindowedIncPSideRankBound
    1 0 M (2 ^ 804) paperScale_ge_two htb hns

/-- Projected payload data plus the new Route-B projected-zero bridge fills the
existing compiled-almost-closed endpoint. -/
def oneWindowCompiledAlmostClosedData_of_projectedPayloadData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusProjectedPayloadData M htb hns)
    (hbridge : PaperScaleProjectedPayloadRouteBBridge M htb hns D) :
    PaperScalePiPlusBooleanProjectedOneWindowCompiledAlmostClosedData
      M htb hns where
  compiled_pullback_membership :=
    compiledRawPullbackMembership_of_windowedRowCertificate
      1 0 M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusSATTransform_paperScale M htb hns)
      D.p_windowed_row_certificate
  windowed_p_side_bound := hbridge
  np_window_rank_nondecreasing :=
    paperScale_npWindowRankNondecreasing_of_npWindowSubspaceInclusion
      M htb hns
      (paperScale_npWindowSubspaceInclusion_of_npWindowRowInclusion
        M htb hns D.np_window_row_inclusion)

/-- Final projected-payload closeout.  This theorem is honest: the only new
mathematical P-side burden is explicitly named as
`PaperScaleProjectedPayloadRouteBBridge`. -/
theorem no_decidesSAT_at_paperScale_of_projectedPayloadData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusProjectedPayloadData M htb hns)
    (hbridge : PaperScaleProjectedPayloadRouteBBridge M htb hns D) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_oneWindowCompiledAlmostClosedData
    M htb hns
    (oneWindowCompiledAlmostClosedData_of_projectedPayloadData
      M htb hns D hbridge)

/-- Formal marker that the previous payload package is obsolete: at paper scale
it is uninhabitable because its zero-profile socket is false. -/
theorem oldPayloadData_uninhabited_due_to_zeroSocket
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    ¬ Nonempty (PaperScalePiPlusPayloadData M htb hns) :=
  not_paperScalePiPlusPayloadData_current_zeroSocket M htb hns

/-! ## Axiom audit anchors -/

#print axioms cookLevinOneWindowProjectedZeroHistogramShiftCommonSpan_of_unprojected
#print axioms projectedPayloadData_of_singletonQuotientPayloadData
#print axioms oneWindowCompiledAlmostClosedData_of_projectedPayloadData
#print axioms no_decidesSAT_at_paperScale_of_projectedPayloadData
#print axioms oldPayloadData_uninhabited_due_to_zeroSocket

end PallLean.Paper93.DeepMath.PathC
