import PallLean.Paper93.DeepMath.PathC.PiPlusStrictCookLevinCloseout
import PallLean.Paper93.DeepMath.PathC.PiPlusRouteBOneWindowPerTypeDischarge

/-!
# Payload-level Pi+ closeout

This file strips the remaining endpoint down to the concrete mathematical
payloads that are not packaging:

1. the corrected one-window raw-pullback row theorem for the P side;
2. the NP-window generator-row inclusion theorem;
3. the Route-B one-window local data: zero-profile common span plus local
   factor-derivative/shift-closure active data with finite three-dimensional
   type spaces.
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

/-- Generator-row form of the NP-window inclusion.  Every source NP-window row
for the Cook--Levin compiled polynomial is already a row in the Boolean-projected
`Pi+ᵦ` target subspace. -/
def PiPlusBooleanProjectedNPWindowRowInclusion
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : SATDeciderGaugeSpace M n hn2 htb hns),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
      mlProj (m * iterDerivList S
        (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ∈
        mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (piPlusBooleanProjectedGauge M n hn2 htb hns piP
            (compiledPoly (cook_levin_compilation M n hn2 htb hns)))

/-- NP-window row inclusion gives the subspace inclusion consumed downstream. -/
theorem npWindowSubspaceInclusion_of_npWindowRowInclusion
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hrow : PiPlusBooleanProjectedNPWindowRowInclusion
      M n hn2 htb hns piP) :
    PiPlusBooleanProjectedNPWindowSubspaceInclusion M n hn2 htb hns piP := by
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
  rw [hq]
  exact hrow S m hlen hdeg hvars hadm

/-- Paper-scale NP-window row inclusion. -/
abbrev PaperScalePiPlusBooleanProjectedNPWindowRowInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedNPWindowRowInclusion
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- Paper-scale row version of NP-window inclusion. -/
theorem paperScale_npWindowSubspaceInclusion_of_npWindowRowInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hrow : PaperScalePiPlusBooleanProjectedNPWindowRowInclusion M htb hns) :
    PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns :=
  npWindowSubspaceInclusion_of_npWindowRowInclusion
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hrow

/-- Payload-level almost-closed data: the exact remaining proof obligations after
all endpoint packaging has been removed. -/
structure PaperScalePiPlusPayloadData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Type where
  p_windowed_row_certificate :
    PaperScalePiPlusBooleanProjectedWindowedRawPullbackRowCertificate
      1 0 M htb hns
  np_window_row_inclusion :
    PaperScalePiPlusBooleanProjectedNPWindowRowInclusion M htb hns
  W : ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ)
  W_finite : ∀ τ, Module.Finite ℚ ↥(W τ)
  W_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3
  zero_common_span :
    CookLevinOneWindowZeroHistogramShiftCommonSpan
      M (2 ^ 804) paperScale_ge_two htb hns
  active_data :
    CookLevinOneWindowPerTypeSpanningActiveData
      M (2 ^ 804) paperScale_ge_two htb hns W

/-- Payload data fills the compiled-almost-closed endpoint directly. -/
def oneWindowCompiledAlmostClosedData_of_payloadData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusPayloadData M htb hns) :
    PaperScalePiPlusBooleanProjectedOneWindowCompiledAlmostClosedData
      M htb hns where
  compiled_pullback_membership :=
    compiledRawPullbackMembership_of_windowedRowCertificate
      1 0 M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusSATTransform_paperScale M htb hns)
      D.p_windowed_row_certificate
  windowed_p_side_bound :=
    paperScale_routeBSATWindowedIncPSideRankBound_one_zero_of_zeroCommonSpan_and_activeData
      M htb hns D.W D.W_finite D.W_dim D.zero_common_span D.active_data
  np_window_rank_nondecreasing :=
    paperScale_npWindowRankNondecreasing_of_npWindowSubspaceInclusion
      M htb hns
      (paperScale_npWindowSubspaceInclusion_of_npWindowRowInclusion
        M htb hns D.np_window_row_inclusion)

/-- Final payload-level theorem.  To close the proof from here, prove the three
fields of `PaperScalePiPlusPayloadData`; no remaining wrapper/assembly theorem is
needed. -/
theorem no_decidesSAT_at_paperScale_of_payloadData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusPayloadData M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_oneWindowCompiledAlmostClosedData
    M htb hns
    (oneWindowCompiledAlmostClosedData_of_payloadData M htb hns D)

/-! ## Axiom audit anchors -/

#print axioms npWindowSubspaceInclusion_of_npWindowRowInclusion
#print axioms paperScale_npWindowSubspaceInclusion_of_npWindowRowInclusion
#print axioms oneWindowCompiledAlmostClosedData_of_payloadData
#print axioms no_decidesSAT_at_paperScale_of_payloadData

end PallLean.Paper93.DeepMath.PathC
