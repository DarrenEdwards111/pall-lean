import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailFrontier
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadSpanOrbitClosure
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadSpanOrbitClosureBridge
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailComplementProof
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailEscape

/-!
# Sharp head-tail frontier for Route B holographic invariance

This module gathers the narrowed Route B frontier around the canonical
log-window head-span tail.  The positive route is now explicitly:

* finite-row log-window closure for the prepended head-tail rows;
* descent of every log-window generator through the chosen projection.

The negative route is also explicit: a log-window projection-escape witness
refutes the same Section 39-facing holographic-invariance interface.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- The sharp positive frontier after specializing to the canonical head-span
tail: prove finite-row log-window closure and chosen-projection descent, then
the existing preimage and P-window cover fields finish the projected P-side
bound. -/
structure RouteBRicherSPDPStableCandidateHeadTailRowClosureDescentFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    Type where
  row_closure :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowRowClosure M n hn2 htb hns
      (routeBRicherSPDPStableCandidateRows M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns))
  projection_descent :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
      M n hn2 htb hns
  unprojected_preimage :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowUnprojectedPreimage
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateRows M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns))
  p_window_cover :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns

/-- Finite-row closure plus chosen-projection descent is exactly enough to
produce the specialized head-tail frontier. -/
def routeBRicherSPDPStableCandidate_headTailFrontier_of_rowClosureDescentFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailRowClosureDescentFrontier
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHeadTailFrontier M n hn2 htb hns where
  tail_finite_orbit_closure :=
    routeBRicherSPDPStableCandidate_tailFiniteOrbitClosure_for_headSpanTail_of_logWindowRowClosure
      M n hn2 htb hns frontier.row_closure
  complement_invariant :=
    (routeBRicherSPDPStableCandidate_logWindowChosenComplementInvariant_for_headSpanTail_iff_descent
      M n hn2 htb hns).mpr frontier.projection_descent
  unprojected_preimage := frontier.unprojected_preimage
  p_window_cover := frontier.p_window_cover

/-- The narrowed row-closure/descent obligations are the formal Section 39
holographic-invariance seam for the canonical head-span tail. -/
theorem routeBRicherSPDPStableCandidate_holographicInvariance_of_rowClosure_descent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (rowClosure :
      RouteBRicherGaugeFiniteRowsSPDPLogWindowRowClosure M n hn2 htb hns
        (routeBRicherSPDPStableCandidateRows M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail
            M n hn2 htb hns)))
    (descent :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHolographicInvariance
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_holographicInvariance_for_headSpanTail_of_tailFiniteOrbitClosure_complementInvariant
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_tailFiniteOrbitClosure_for_headSpanTail_of_logWindowRowClosure
      M n hn2 htb hns rowClosure)
    ((routeBRicherSPDPStableCandidate_logWindowChosenComplementInvariant_for_headSpanTail_iff_descent
      M n hn2 htb hns).mpr descent)

/-- The sharp row-closure/descent frontier proves the projected P-side bound. -/
theorem routeBRicherSPDPStableCandidate_projectedPSideBound_of_rowClosureDescentFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailRowClosureDescentFrontier
        M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)) :=
  routeBRicherSPDPStableCandidate_projectedPSideBound_of_headTailFrontier
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headTailFrontier_of_rowClosureDescentFrontier
      M n hn2 htb hns frontier)

/-- Under the existing explicit log-window consumer bridge, the sharp
row-closure/descent frontier discharges the stable-candidate obligations. -/
theorem routeBRicherSPDPStableCandidate_obligations_of_rowClosureDescentFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailRowClosureDescentFrontier
        M n hn2 htb hns)
    (hwindow :
      RouteBRicherSPDPStableCandidateAdmissibleQueriesLogWindowed
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateObligations
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_obligations_of_headTailFrontier
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headTailFrontier_of_rowClosureDescentFrontier
      M n hn2 htb hns frontier)
    hwindow

/-- A log-window projection escape for the canonical head-span tail refutes
the same holographic-invariance interface. -/
theorem routeBRicherSPDPStableCandidate_not_holographicInvariance_for_headSpanTail_of_logWindowProjectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateHolographicInvariance
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns) := by
  apply
    routeBRicherSPDPStableCandidate_not_holographicInvariance_of_logWindowComplement_escape
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
  obtain ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm,
    hpComplement, hprojNe⟩ := hbad
  refine ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm, ?_, ?_⟩
  · simpa [routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement]
      using hpComplement
  · intro hrowComplement
    apply hprojNe
    exact
      (routeBRicherSPDPStableCandidateProjectionWithComplement_apply_eq_zero_iff
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
        (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
          M n hn2 htb hns)
        (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement_isCompl
          M n hn2 htb hns)
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)).mpr
        (by
          simpa [routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement]
            using hrowComplement)

/-- The empty-generator `mlProj` escape is already enough to refute the
Section 39-facing holographic-invariance interface. -/
theorem routeBRicherSPDPStableCandidate_not_holographicInvariance_for_headSpanTail_of_mlProjProjectionEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateHeadSpanTailMlProjProjectionEscapeWitness
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateHolographicInvariance
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_not_holographicInvariance_for_headSpanTail_of_logWindowProjectionEscapeWitness
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_mlProjProjectionEscape
      M n hn2 htb hns hbad)

/-- Kernel-form empty-generator escape also refutes the same
holographic-invariance interface. -/
theorem routeBRicherSPDPStableCandidate_not_holographicInvariance_for_headSpanTail_of_kernelMlProjProjectionEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateHeadSpanTailKernelMlProjProjectionEscapeWitness
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateHolographicInvariance
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_not_holographicInvariance_for_headSpanTail_of_logWindowProjectionEscapeWitness
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_kernelMlProjProjectionEscape
      M n hn2 htb hns hbad)

/-! ## Axiom audit anchors -/

#print axioms RouteBRicherSPDPStableCandidateHeadTailRowClosureDescentFrontier
#print axioms routeBRicherSPDPStableCandidate_headTailFrontier_of_rowClosureDescentFrontier
#print axioms routeBRicherSPDPStableCandidate_holographicInvariance_of_rowClosure_descent
#print axioms routeBRicherSPDPStableCandidate_projectedPSideBound_of_rowClosureDescentFrontier
#print axioms routeBRicherSPDPStableCandidate_obligations_of_rowClosureDescentFrontier
#print axioms routeBRicherSPDPStableCandidate_not_holographicInvariance_for_headSpanTail_of_logWindowProjectionEscapeWitness
#print axioms routeBRicherSPDPStableCandidate_not_holographicInvariance_for_headSpanTail_of_mlProjProjectionEscape
#print axioms routeBRicherSPDPStableCandidate_not_holographicInvariance_for_headSpanTail_of_kernelMlProjProjectionEscape

end PallLean.Paper93.Paper283
