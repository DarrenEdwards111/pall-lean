import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedNPLowerBridge

/-!
# Compiled-polynomial-only Route C membership closure

The previous membership interface still quantified over every polynomial `p`.
For the final SAT-decider contradiction, the P-side uses only the compiled
Cook--Levin polynomial at the final `(log n, log n)` window.  This file exposes
that exact weaker Route-C target.

This is the honest next reduction of the Route C pullback problem:
prove membership only for pulled-back generators of
`Pi+ᵦ(compiledPoly)`, not a global transport theorem for arbitrary `p`.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Paper283
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- Compiled-polynomial-only windowed raw-pullback membership.

This is weaker than `PiPlusBooleanProjectedWindowedRawPullbackGeneratorMembership`:
it only asks for the final P-side generators of the Boolean-projected compiled
polynomial at `(κ,ℓ) = (log₂ n, log₂ n)`. -/
def PiPlusBooleanProjectedWindowedCompiledRawPullbackMembership
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : SATDeciderGaugeSpace M n hn2 htb hns),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
      piP.equiv.symm
        (mlProj (m * iterDerivList S
          (piPlusBooleanProjectedGauge M n hn2 htb hns piP
            (compiledPoly (cook_levin_compilation M n hn2 htb hns))))) ∈
        mlBlockedSpdpSubspaceInc
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))

/-- Paper-scale compiled-only membership abbreviation. -/
abbrev PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembership
    (extraK extraL : Nat)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedWindowedCompiledRawPullbackMembership extraK extraL
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- Full windowed raw-pullback membership implies the compiled-only target. -/
theorem compiledRawPullbackMembership_of_windowedRawPullbackMembership
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hpull : PiPlusBooleanProjectedWindowedRawPullbackGeneratorMembership
      extraK extraL M n hn2 htb hns piP) :
    PiPlusBooleanProjectedWindowedCompiledRawPullbackMembership
      extraK extraL M n hn2 htb hns piP := by
  intro S m hlen hdeg hvars hadm
  exact hpull (Nat.log 2 n) (Nat.log 2 n)
    (compiledPoly (cook_levin_compilation M n hn2 htb hns))
    S m hlen hdeg hvars hadm

/-- Paper-scale full membership implies paper-scale compiled-only membership. -/
theorem paperScale_compiledRawPullbackMembership_of_windowedRawPullbackMembership
    (extraK extraL : Nat)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpull : PaperScalePiPlusBooleanProjectedWindowedRawPullbackMembership
      extraK extraL M htb hns) :
    PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembership
      extraK extraL M htb hns :=
  compiledRawPullbackMembership_of_windowedRawPullbackMembership
    extraK extraL M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hpull

/-- Compiled-only pullback membership gives the final projected compiled
subspace inclusion into the Boolean-projected image of the enlarged source
inclusive SPDP subspace. -/
theorem piPlusBooleanProjectedCompiledSubspace_le_map_inc_of_compiledMembership
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hpull : PiPlusBooleanProjectedWindowedCompiledRawPullbackMembership
      extraK extraL M n hn2 htb hns piP) :
      mlBlockedSpdpSubspace
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (piPlusBooleanProjectedGauge M n hn2 htb hns piP
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ≤
    Submodule.map (piPlusBooleanProjectedGauge M n hn2 htb hns piP)
        (mlBlockedSpdpSubspaceInc
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))) := by
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
  rw [hq]
  refine ⟨piP.equiv.symm
      (mlProj (m * iterDerivList S
        (piPlusBooleanProjectedGauge M n hn2 htb hns piP
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))))),
    hpull S m hlen hdeg hvars hadm, ?_⟩
  exact piPlusBooleanProjectedGauge_rawPullback_targetGenerator
    M n hn2 htb hns piP
    (compiledPoly (cook_levin_compilation M n hn2 htb hns)) S m

/-- Compiled-only membership gives the P-side rank comparison needed for final
closure. -/
theorem piPlusBooleanProjected_compiledRank_le_rankInc_of_compiledMembership
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hpull : PiPlusBooleanProjectedWindowedCompiledRawPullbackMembership
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
          Submodule.finrank_mono
            (piPlusBooleanProjectedCompiledSubspace_le_map_inc_of_compiledMembership
              extraK extraL M n hn2 htb hns piP hpull)
    _ ≤ Module.finrank ℚ
          (mlBlockedSpdpSubspaceInc
            (cook_levin_compilation M n hn2 htb hns).partition
            (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
            (compiledPoly (cook_levin_compilation M n hn2 htb hns))) :=
          Submodule.finrank_map_le _ _

/-- Compiled-only membership plus the matching Route-B enlarged P-side bound
gives the ordinary projected P-side field. -/
theorem piPlusBooleanProjected_pSideBound_of_compiledMembership_of_windowedIncPSide
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hpull : PiPlusBooleanProjectedWindowedCompiledRawPullbackMembership
      extraK extraL M n hn2 htb hns piP)
    (hpside : RouteBSATWindowedIncPSideRankBound
      extraK extraL M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (piPlusBooleanProjectedGauge M n hn2 htb hns piP) := by
  unfold SATDeciderGaugePSideBound RouteBSATWindowedIncPSideRankBound at *
  exact le_trans
    (piPlusBooleanProjected_compiledRank_le_rankInc_of_compiledMembership
      extraK extraL M n hn2 htb hns piP hpull)
    hpside

/-- Paper-scale compiled-membership P-side bridge. -/
theorem cookLevinPiPlusBooleanProjected_pSideBound_paperScale_of_compiledMembership_of_windowedIncPSide
    (extraK extraL : Nat)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpull : PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembership
      extraK extraL M htb hns)
    (hpside : RouteBSATWindowedIncPSideRankBound
      extraK extraL M (2 ^ 804) paperScale_ge_two htb hns) :
    SATDeciderGaugePSideBound M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns) :=
  piPlusBooleanProjected_pSideBound_of_compiledMembership_of_windowedIncPSide
    extraK extraL M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hpull hpside

/-- Final one-window closure data with Route C membership reduced to exactly the
compiled-polynomial P-side rows. -/
structure PaperScalePiPlusBooleanProjectedOneWindowCompiledAlmostClosedData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  compiled_pullback_membership :
    PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembership
      1 0 M htb hns
  windowed_p_side_bound :
    RouteBSATWindowedIncPSideRankBound
      1 0 M (2 ^ 804) paperScale_ge_two htb hns
  np_window_rank_nondecreasing :
    PaperScalePiPlusBooleanProjectedNPWindowRankNondecreasing M htb hns

/-- Compiled-almost-closed data implies the projected P/NP incompatible pair. -/
theorem pSide_and_npIdentityMinor_of_oneWindowCompiledAlmostClosedData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusBooleanProjectedOneWindowCompiledAlmostClosedData
      M htb hns) :
    SATDeciderGaugePSideBound M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns) ∧
      SATDeciderGaugeNPIdentityMinorPreservation M (2 ^ 804)
        paperScale_ge_two htb hns
        (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns) := by
  refine ⟨?_, ?_⟩
  · exact cookLevinPiPlusBooleanProjected_pSideBound_paperScale_of_compiledMembership_of_windowedIncPSide
      1 0 M htb hns D.compiled_pullback_membership D.windowed_p_side_bound
  · exact piPlusBooleanProjected_npIdentityMinorPreservation_of_projectedLowerBound
      M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusSATTransform_paperScale M htb hns)
      (paperScale_routeBSATProjectedNPIdentityMinorLowerBound_of_npWindowRankNondecreasing
        M htb hns D.np_window_rank_nondecreasing)

/-- One-window final theorem with both Route-C rank obligations reduced to the
compiled-polynomial P-side membership and NP-window rank nondecrease. -/
theorem no_decidesSAT_at_paperScale_of_oneWindowCompiledAlmostClosedData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusBooleanProjectedOneWindowCompiledAlmostClosedData
      M htb hns) :
    ¬ DecidesSAT M := by
  intro hdec
  rcases pSide_and_npIdentityMinor_of_oneWindowCompiledAlmostClosedData
    M htb hns D with ⟨hP, hNP⟩
  exact satDeciderGauge_pSide_and_npIdentityMinor_incompatible_at_large_n
    M (2 ^ 804) (le_rfl : 2 ^ 804 ≥ 2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns)
    hdec hP hNP

/-! ## Axiom audit anchors -/

#print axioms compiledRawPullbackMembership_of_windowedRawPullbackMembership
#print axioms piPlusBooleanProjectedCompiledSubspace_le_map_inc_of_compiledMembership
#print axioms piPlusBooleanProjected_compiledRank_le_rankInc_of_compiledMembership
#print axioms piPlusBooleanProjected_pSideBound_of_compiledMembership_of_windowedIncPSide
#print axioms cookLevinPiPlusBooleanProjected_pSideBound_paperScale_of_compiledMembership_of_windowedIncPSide
#print axioms pSide_and_npIdentityMinor_of_oneWindowCompiledAlmostClosedData
#print axioms no_decidesSAT_at_paperScale_of_oneWindowCompiledAlmostClosedData

end PallLean.Paper93.DeepMath.PathC
