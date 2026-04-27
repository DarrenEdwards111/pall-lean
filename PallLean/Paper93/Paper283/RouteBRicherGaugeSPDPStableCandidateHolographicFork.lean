import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadSpanStableMapsProof
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailKernelCriterionProof
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailConcreteEscapeWitness

/-!
# Route B head-tail holographic fork

This module is the roll-up for the Section 39 head-tail fork exposed by the
canonical log-window head-span tail.

The positive branch is now stated through the sharper proof interfaces:

* second-pass closure of finite head-span generators;
* stability of the chosen-projection kernel, or the stronger residual-row
  annihilation condition.

The negative branch is the concrete coordinate obstruction:

* a visible monomial coefficient after the selected projection refutes the
  same holographic-invariance interface.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Positive Route B head-tail fork package using the newest proof-facing
interfaces: finite head-span second-pass closure plus chosen-projection kernel
stability, together with the two existing P-side consumer fields. -/
structure RouteBRicherSPDPStableCandidateHeadTailSecondPassKernelFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    Type where
  head_second_pass_closure :
    RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorSecondPassClosure
      M n hn2 htb hns
  projection_kernel_stable :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
      M n hn2 htb hns
  unprojected_preimage :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowUnprojectedPreimage
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateRows M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns))
  p_window_cover :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns

/-- Second-pass head-span closure and chosen-projection kernel stability lower
to the existing row-closure/descent frontier. -/
def routeBRicherSPDPStableCandidate_headTailRowClosureDescentFrontier_of_secondPass_kernelStable
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailSecondPassKernelFrontier
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHeadTailRowClosureDescentFrontier
      M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_headTailRowClosureDescentFrontier_of_headSpanStableGeneratorMaps
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_of_generatorSecondPassClosure
      M n hn2 htb hns frontier.head_second_pass_closure)
    (routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_of_projectionKernelStableGeneratorMaps
      M n hn2 htb hns frontier.projection_kernel_stable)
    frontier.unprojected_preimage
    frontier.p_window_cover

/-- The positive fork package proves the Section 39-facing holographic
invariance interface for the canonical head-span tail. -/
theorem routeBRicherSPDPStableCandidate_holographicInvariance_of_secondPass_kernelStable
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailSecondPassKernelFrontier
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHolographicInvariance
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_holographicInvariance_for_headSpanTail_of_headSpanStableGeneratorMaps_descent
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_of_generatorSecondPassClosure
      M n hn2 htb hns frontier.head_second_pass_closure)
    (routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_of_projectionKernelStableGeneratorMaps
      M n hn2 htb hns frontier.projection_kernel_stable)

/-- The same positive fork package proves the projected P-side bound, once
the preimage and P-window consumer fields are supplied. -/
theorem routeBRicherSPDPStableCandidate_projectedPSideBound_of_secondPass_kernelStable
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailSecondPassKernelFrontier
        M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)) :=
  routeBRicherSPDPStableCandidate_projectedPSideBound_of_rowClosureDescentFrontier
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headTailRowClosureDescentFrontier_of_secondPass_kernelStable
      M n hn2 htb hns frontier)

/-- Second-pass head-span closure plus residual-row annihilation is a stronger
positive route to the same holographic-invariance interface. -/
theorem routeBRicherSPDPStableCandidate_holographicInvariance_of_secondPass_residualGeneratorZero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hhead :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorSecondPassClosure
        M n hn2 htb hns)
    (hzero :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHolographicInvariance
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_holographicInvariance_for_headSpanTail_of_headSpanStableGeneratorMaps_descent
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_of_generatorSecondPassClosure
      M n hn2 htb hns hhead)
    (routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_of_residualGeneratorZero
      M n hn2 htb hns hzero)

/-- A visible projected monomial coefficient refutes the same Section 39
holographic-invariance interface. -/
theorem routeBRicherSPDPStableCandidate_not_holographicInvariance_of_visibleCoefficientEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hcoord :
      RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateHolographicInvariance
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_not_holographicInvariance_for_headSpanTail_of_logWindowProjectionEscapeWitness
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_visibleCoefficientEscapeObstruction
      M n hn2 htb hns hcoord)

/-- The empty-generator visible coefficient obstruction also refutes the same
Section 39 holographic-invariance interface. -/
theorem routeBRicherSPDPStableCandidate_not_holographicInvariance_of_mlProjVisibleCoefficientEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hcoord :
      RouteBRicherSPDPStableCandidateHeadSpanTailMlProjVisibleCoefficientEscapeWitness
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateHolographicInvariance
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_not_holographicInvariance_for_headSpanTail_of_logWindowProjectionEscapeWitness
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_mlProjVisibleCoefficientEscape
      M n hn2 htb hns hcoord)

/-! ## Axiom audit anchors -/

#print axioms RouteBRicherSPDPStableCandidateHeadTailSecondPassKernelFrontier
#print axioms routeBRicherSPDPStableCandidate_headTailRowClosureDescentFrontier_of_secondPass_kernelStable
#print axioms routeBRicherSPDPStableCandidate_holographicInvariance_of_secondPass_kernelStable
#print axioms routeBRicherSPDPStableCandidate_projectedPSideBound_of_secondPass_kernelStable
#print axioms routeBRicherSPDPStableCandidate_holographicInvariance_of_secondPass_residualGeneratorZero
#print axioms routeBRicherSPDPStableCandidate_not_holographicInvariance_of_visibleCoefficientEscape
#print axioms routeBRicherSPDPStableCandidate_not_holographicInvariance_of_mlProjVisibleCoefficientEscape

end PallLean.Paper93.Paper283
