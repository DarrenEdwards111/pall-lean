import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedCompiledMembershipClosure
import PallLean.Paper93.DeepMath.PathC.PiPlusRouteBOneWindowPerTypeFrontier

/-!
# Final narrowed Route-C/Route-B frontier

This file packages the three remaining payloads in their sharpest currently
useful form:

1. Route-C P-side transport as a single compiled-polynomial subspace inclusion;
2. Route-B one-window P-side compression via the corrected zero/per-type
   blockers;
3. Route-C NP-side preservation as a single NP-window subspace inclusion.

The result is not a fake proof of the remaining mathematics.  It removes the
last packaging noise around the final contradiction, leaving only the concrete
subspace inclusions and the already-isolated Route-B blockers.
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

/-- The sharp P-side Route-C inclusion actually needed for final closure: the
SPDP subspace of the Boolean-projected compiled polynomial at the final window
is contained in the image of the enlarged inclusive source compiled subspace. -/
def PiPlusBooleanProjectedCompiledPSubspaceInclusion
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  mlBlockedSpdpSubspace
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (piPlusBooleanProjectedGauge M n hn2 htb hns piP
        (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ≤
    Submodule.map (piPlusBooleanProjectedGauge M n hn2 htb hns piP)
      (mlBlockedSpdpSubspaceInc
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) )

/-- Paper-scale abbreviation for the sharp P-side inclusion. -/
abbrev PaperScalePiPlusBooleanProjectedCompiledPSubspaceInclusion
    (extraK extraL : Nat)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedCompiledPSubspaceInclusion extraK extraL
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- The generator-membership formulation implies the sharper subspace-inclusion
formulation. -/
theorem compiledPSubspaceInclusion_of_compiledRawPullbackMembership
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hpull : PiPlusBooleanProjectedWindowedCompiledRawPullbackMembership
      extraK extraL M n hn2 htb hns piP) :
    PiPlusBooleanProjectedCompiledPSubspaceInclusion
      extraK extraL M n hn2 htb hns piP :=
  piPlusBooleanProjectedCompiledSubspace_le_map_inc_of_compiledMembership
    extraK extraL M n hn2 htb hns piP hpull

/-- The sharp P-side inclusion gives the final P-side rank comparison. -/
theorem piPlusBooleanProjected_compiledRank_le_rankInc_of_compiledPSubspaceInclusion
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hincl : PiPlusBooleanProjectedCompiledPSubspaceInclusion
      extraK extraL M n hn2 htb hns piP) :
    mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (piPlusBooleanProjectedGauge M n hn2 htb hns piP
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ≤
      mlBlockedSpdpRankInc
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) := by
  unfold mlBlockedSpdpRank mlBlockedSpdpRankInc
  calc
    Module.finrank ℚ
        (mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (piPlusBooleanProjectedGauge M n hn2 htb hns piP
            (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
        ≤ Module.finrank ℚ
            (Submodule.map (piPlusBooleanProjectedGauge M n hn2 htb hns piP)
              (mlBlockedSpdpSubspaceInc
                (cook_levin_compilation M n hn2 htb hns).partition
                (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
                (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) :=
          Submodule.finrank_mono hincl
    _ ≤ Module.finrank ℚ
          (mlBlockedSpdpSubspaceInc
            (cook_levin_compilation M n hn2 htb hns).partition
            (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
            (compiledPoly (cook_levin_compilation M n hn2 htb hns))) :=
          Submodule.finrank_map_le _ _

/-- Sharp P-side inclusion plus the enlarged Route-B P-side rank bound gives
the ordinary projected P-side field. -/
theorem piPlusBooleanProjected_pSideBound_of_compiledPSubspaceInclusion_of_windowedIncPSide
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hincl : PiPlusBooleanProjectedCompiledPSubspaceInclusion
      extraK extraL M n hn2 htb hns piP)
    (hpside : RouteBSATWindowedIncPSideRankBound
      extraK extraL M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (piPlusBooleanProjectedGauge M n hn2 htb hns piP) := by
  unfold SATDeciderGaugePSideBound RouteBSATWindowedIncPSideRankBound at *
  exact le_trans
    (piPlusBooleanProjected_compiledRank_le_rankInc_of_compiledPSubspaceInclusion
      extraK extraL M n hn2 htb hns piP hincl)
    hpside

/-- The sharp NP-side Route-C inclusion needed for final closure: the source
compiled SPDP subspace at the NP window embeds into the Boolean-projected target
compiled SPDP subspace at the same NP window. -/
def PiPlusBooleanProjectedNPWindowSubspaceInclusion
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  mlBlockedSpdpSubspace
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≤
    mlBlockedSpdpSubspace
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (piPlusBooleanProjectedGauge M n hn2 htb hns piP
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)))

/-- Paper-scale abbreviation for the sharp NP-side subspace inclusion. -/
abbrev PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedNPWindowSubspaceInclusion
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- NP-window subspace inclusion implies the NP-window rank nondecrease field. -/
theorem npWindowRankNondecreasing_of_npWindowSubspaceInclusion
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hincl : PiPlusBooleanProjectedNPWindowSubspaceInclusion
      M n hn2 htb hns piP) :
    PiPlusBooleanProjectedNPWindowRankNondecreasing M n hn2 htb hns piP := by
  unfold PiPlusBooleanProjectedNPWindowRankNondecreasing mlBlockedSpdpRank
  exact Submodule.finrank_mono hincl

/-- Paper-scale specialization of the NP inclusion to rank nondecrease. -/
theorem paperScale_npWindowRankNondecreasing_of_npWindowSubspaceInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hincl : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion
      M htb hns) :
    PaperScalePiPlusBooleanProjectedNPWindowRankNondecreasing M htb hns :=
  npWindowRankNondecreasing_of_npWindowSubspaceInclusion
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hincl

/-- Final narrowed paper-scale data.  Only the two concrete Route-C subspace
inclusions and the corrected Route-B one-window blockers remain. -/
structure PaperScalePiPlusBooleanProjectedFinalFrontierData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) where
  compiled_p_subspace_inclusion :
    PaperScalePiPlusBooleanProjectedCompiledPSubspaceInclusion 1 0 M htb hns
  W : ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ)
  W_finite : ∀ τ, Module.Finite ℚ ↥(W τ)
  W_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3
  zero_common_span :
    CookLevinOneWindowZeroHistogramShiftCommonSpan
      M (2 ^ 804) paperScale_ge_two htb hns
  per_type_spanning :
    CookLevinOneWindowPerTypeSpanningActiveAdmissibleProfileCases
      M (2 ^ 804) paperScale_ge_two htb hns W
  np_subspace_inclusion :
    PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns

/-- Final narrowed data directly gives the P/NP incompatible pair without trying
to reconstruct generator-wise raw-pullback membership from a subspace inclusion. -/
theorem pSide_and_npIdentityMinor_of_finalFrontierData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusBooleanProjectedFinalFrontierData M htb hns) :
    SATDeciderGaugePSideBound M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns) ∧
      SATDeciderGaugeNPIdentityMinorPreservation M (2 ^ 804)
        paperScale_ge_two htb hns
        (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns) := by
  refine ⟨?_, ?_⟩
  · exact piPlusBooleanProjected_pSideBound_of_compiledPSubspaceInclusion_of_windowedIncPSide
      1 0 M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusSATTransform_paperScale M htb hns)
      D.compiled_p_subspace_inclusion
      (paperScale_routeBSATWindowedIncPSideRankBound_one_zero_of_zeroCommonSpan_and_perTypeSpanning
        M htb hns D.W D.W_finite D.W_dim D.zero_common_span D.per_type_spanning)
  · exact piPlusBooleanProjected_npIdentityMinorPreservation_of_projectedLowerBound
      M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusSATTransform_paperScale M htb hns)
      (paperScale_routeBSATProjectedNPIdentityMinorLowerBound_of_npWindowRankNondecreasing
        M htb hns
        (paperScale_npWindowRankNondecreasing_of_npWindowSubspaceInclusion
          M htb hns D.np_subspace_inclusion))

/-- Final narrowed Route-C/Route-B frontier theorem. -/
theorem no_decidesSAT_at_paperScale_of_finalFrontierData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusBooleanProjectedFinalFrontierData M htb hns) :
    ¬ DecidesSAT M := by
  intro hdec
  rcases pSide_and_npIdentityMinor_of_finalFrontierData M htb hns D with ⟨hP, hNP⟩
  exact satDeciderGauge_pSide_and_npIdentityMinor_incompatible_at_large_n
    M (2 ^ 804) (le_rfl : 2 ^ 804 ≥ 2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns)
    hdec hP hNP

/-! ## Axiom audit anchors -/

#print axioms compiledPSubspaceInclusion_of_compiledRawPullbackMembership
#print axioms piPlusBooleanProjected_compiledRank_le_rankInc_of_compiledPSubspaceInclusion
#print axioms piPlusBooleanProjected_pSideBound_of_compiledPSubspaceInclusion_of_windowedIncPSide
#print axioms npWindowRankNondecreasing_of_npWindowSubspaceInclusion
#print axioms paperScale_npWindowRankNondecreasing_of_npWindowSubspaceInclusion
#print axioms pSide_and_npIdentityMinor_of_finalFrontierData
#print axioms no_decidesSAT_at_paperScale_of_finalFrontierData

end PallLean.Paper93.DeepMath.PathC
