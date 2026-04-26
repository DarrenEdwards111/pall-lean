import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateLogWindowAssembly
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailOrbit
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailComplement

/-!
# Head-tail frontier for the Route B SPDP-stable candidate

This module specializes the log-window finite-orbit frontier to the canonical
finite head-span tail.  At this exact candidate, the head cover is already
proved, so the remaining Section 39-facing obligations are only:

* tail finite-orbit closure for the head-span basis tail;
* log-window complement invariance;
* the existing log-window unprojected-preimage and P-window cover inputs.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Specialized frontier for the canonical finite log-window head-span tail.
The head-subspace cover is not a field because it is already proved by
`routeBRicherSPDPStableCandidate_logWindowHeadSPDPSubspaceCovered_for_headSpanTail`. -/
structure RouteBRicherSPDPStableCandidateHeadTailFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    Type where
  tail_finite_orbit_closure :
    RouteBRicherSPDPStableCandidateLogWindowTailFiniteOrbitClosure
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns)
  complement_invariant :
    RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns)
  unprojected_preimage :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowUnprojectedPreimage
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateRows M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns))
  p_window_cover :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns

/-- Head-tail frontier stated with the sharper head-span orbit coefficient
closure obligation.  This is often the natural proof target: prove closure for
every element of the head span, then the selected basis tail is automatically
tail-row finite-orbit closed. -/
structure RouteBRicherSPDPStableCandidateHeadTailClosureFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    Type where
  head_span_orbit_closure :
    RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitCoefficientClosure
      M n hn2 htb hns
  complement_invariant :
    RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns)
  unprojected_preimage :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowUnprojectedPreimage
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateRows M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns))
  p_window_cover :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns

/-- Head-tail frontier whose complement side is stated as generator-map
stability of the chosen complement. -/
structure RouteBRicherSPDPStableCandidateHeadTailStableMapsFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    Type where
  head_span_orbit_closure :
    RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitCoefficientClosure
      M n hn2 htb hns
  complement_stable_maps :
    RouteBRicherSPDPStableCandidateLogWindowChosenComplementStableGeneratorMaps
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns)
  unprojected_preimage :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowUnprojectedPreimage
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateRows M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns))
  p_window_cover :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns

/-- Head-tail frontier whose complement side is stated as chosen-projection
intertwining. -/
structure RouteBRicherSPDPStableCandidateHeadTailProjectionIntertwiningFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    Type where
  head_span_orbit_closure :
    RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitCoefficientClosure
      M n hn2 htb hns
  projection_intertwines :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionIntertwines
      M n hn2 htb hns
  unprojected_preimage :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowUnprojectedPreimage
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateRows M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns))
  p_window_cover :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns

/-- The head-span closure frontier lowers to the direct head-tail frontier. -/
def routeBRicherSPDPStableCandidate_headTailFrontier_of_headTailClosureFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailClosureFrontier
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHeadTailFrontier M n hn2 htb hns where
  tail_finite_orbit_closure :=
    routeBRicherSPDPStableCandidate_tailFiniteOrbitClosure_for_headSpanTail_of_headSpanOrbitCoefficientClosure
      M n hn2 htb hns frontier.head_span_orbit_closure
  complement_invariant := frontier.complement_invariant
  unprojected_preimage := frontier.unprojected_preimage
  p_window_cover := frontier.p_window_cover

/-- Generator-map stability lowers to the direct closure frontier. -/
def routeBRicherSPDPStableCandidate_headTailClosureFrontier_of_stableMapsFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailStableMapsFrontier
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHeadTailClosureFrontier
      M n hn2 htb hns where
  head_span_orbit_closure := frontier.head_span_orbit_closure
  complement_invariant :=
    routeBRicherSPDPStableCandidate_logWindowChosenComplementInvariant_for_headSpanTail_of_stableGeneratorMaps
      M n hn2 htb hns frontier.complement_stable_maps
  unprojected_preimage := frontier.unprojected_preimage
  p_window_cover := frontier.p_window_cover

/-- Projection-intertwining lowers to the direct closure frontier. -/
def routeBRicherSPDPStableCandidate_headTailClosureFrontier_of_projectionIntertwiningFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailProjectionIntertwiningFrontier
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHeadTailClosureFrontier
      M n hn2 htb hns where
  head_span_orbit_closure := frontier.head_span_orbit_closure
  complement_invariant :=
    routeBRicherSPDPStableCandidate_logWindowChosenComplementInvariant_for_headSpanTail_of_projectionIntertwines
      M n hn2 htb hns frontier.projection_intertwines
  unprojected_preimage := frontier.unprojected_preimage
  p_window_cover := frontier.p_window_cover

/-- The specialized head-tail frontier lowers to the generic finite-orbit
component frontier. -/
def routeBRicherSPDPStableCandidate_finiteOrbitComponentFrontier_of_headTailFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailFrontier M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowFiniteOrbitComponentFrontier
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_finiteOrbitComponentFrontier_for_headSpanTail
    M n hn2 htb hns
    frontier.tail_finite_orbit_closure
    frontier.complement_invariant
    frontier.unprojected_preimage
    frontier.p_window_cover

/-- A specialized head-tail frontier supplies the Section 39-facing
holographic-invariance interface. -/
theorem routeBRicherSPDPStableCandidate_holographicInvariance_of_headTailFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailFrontier M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHolographicInvariance
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_holographicInvariance_for_headSpanTail_of_tailFiniteOrbitClosure_complementInvariant
    M n hn2 htb hns
    frontier.tail_finite_orbit_closure
    frontier.complement_invariant

/-- The specialized head-tail frontier proves the projected P-side bound. -/
theorem routeBRicherSPDPStableCandidate_projectedPSideBound_of_headTailFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailFrontier M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)) :=
  routeBRicherSPDPStableCandidate_projectedPSideBound_of_finiteOrbitComponentFrontier
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidateLogWindowHeadTail
      M n hn2 htb hns)
    (routeBRicherSPDPStableCandidate_finiteOrbitComponentFrontier_of_headTailFrontier
      M n hn2 htb hns frontier)

/-- Under a log-window consumer bridge, the specialized head-tail frontier
discharges the stable-candidate row-closure and kernel-invisibility
obligations. -/
theorem routeBRicherSPDPStableCandidate_obligations_of_headTailFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailFrontier M n hn2 htb hns)
    (hwindow :
      RouteBRicherSPDPStableCandidateAdmissibleQueriesLogWindowed
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateObligations
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_obligations_of_finiteOrbitComponentFrontier
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidateLogWindowHeadTail
      M n hn2 htb hns)
    (routeBRicherSPDPStableCandidate_finiteOrbitComponentFrontier_of_headTailFrontier
      M n hn2 htb hns frontier)
    hwindow

/-- The sharper head-span closure frontier proves the projected P-side bound. -/
theorem routeBRicherSPDPStableCandidate_projectedPSideBound_of_headTailClosureFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailClosureFrontier
        M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)) :=
  routeBRicherSPDPStableCandidate_projectedPSideBound_of_headTailFrontier
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headTailFrontier_of_headTailClosureFrontier
      M n hn2 htb hns frontier)

/-- Under a log-window consumer bridge, the sharper head-span closure frontier
discharges the stable-candidate row-closure and kernel-invisibility
obligations. -/
theorem routeBRicherSPDPStableCandidate_obligations_of_headTailClosureFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailClosureFrontier
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
    (routeBRicherSPDPStableCandidate_headTailFrontier_of_headTailClosureFrontier
      M n hn2 htb hns frontier)
    hwindow

/-- The stable-generator-map frontier proves the projected P-side bound. -/
theorem routeBRicherSPDPStableCandidate_projectedPSideBound_of_headTailStableMapsFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailStableMapsFrontier
        M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)) :=
  routeBRicherSPDPStableCandidate_projectedPSideBound_of_headTailClosureFrontier
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headTailClosureFrontier_of_stableMapsFrontier
      M n hn2 htb hns frontier)

/-- The projection-intertwining frontier proves the projected P-side bound. -/
theorem routeBRicherSPDPStableCandidate_projectedPSideBound_of_headTailProjectionIntertwiningFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailProjectionIntertwiningFrontier
        M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)) :=
  routeBRicherSPDPStableCandidate_projectedPSideBound_of_headTailClosureFrontier
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headTailClosureFrontier_of_projectionIntertwiningFrontier
      M n hn2 htb hns frontier)

/-- Under a log-window consumer bridge, the stable-generator-map frontier
discharges the stable-candidate row-closure and kernel-invisibility
obligations. -/
theorem routeBRicherSPDPStableCandidate_obligations_of_headTailStableMapsFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailStableMapsFrontier
        M n hn2 htb hns)
    (hwindow :
      RouteBRicherSPDPStableCandidateAdmissibleQueriesLogWindowed
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateObligations
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_obligations_of_headTailClosureFrontier
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headTailClosureFrontier_of_stableMapsFrontier
      M n hn2 htb hns frontier)
    hwindow

/-- Under a log-window consumer bridge, the projection-intertwining frontier
discharges the stable-candidate row-closure and kernel-invisibility
obligations. -/
theorem routeBRicherSPDPStableCandidate_obligations_of_headTailProjectionIntertwiningFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailProjectionIntertwiningFrontier
        M n hn2 htb hns)
    (hwindow :
      RouteBRicherSPDPStableCandidateAdmissibleQueriesLogWindowed
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateObligations
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_obligations_of_headTailClosureFrontier
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headTailClosureFrontier_of_projectionIntertwiningFrontier
      M n hn2 htb hns frontier)
    hwindow

/-! ## Axiom audit anchors -/

#print axioms RouteBRicherSPDPStableCandidateHeadTailFrontier
#print axioms RouteBRicherSPDPStableCandidateHeadTailClosureFrontier
#print axioms RouteBRicherSPDPStableCandidateHeadTailStableMapsFrontier
#print axioms RouteBRicherSPDPStableCandidateHeadTailProjectionIntertwiningFrontier
#print axioms routeBRicherSPDPStableCandidate_headTailFrontier_of_headTailClosureFrontier
#print axioms routeBRicherSPDPStableCandidate_headTailClosureFrontier_of_stableMapsFrontier
#print axioms routeBRicherSPDPStableCandidate_headTailClosureFrontier_of_projectionIntertwiningFrontier
#print axioms routeBRicherSPDPStableCandidate_finiteOrbitComponentFrontier_of_headTailFrontier
#print axioms routeBRicherSPDPStableCandidate_holographicInvariance_of_headTailFrontier
#print axioms routeBRicherSPDPStableCandidate_projectedPSideBound_of_headTailFrontier
#print axioms routeBRicherSPDPStableCandidate_obligations_of_headTailFrontier
#print axioms routeBRicherSPDPStableCandidate_projectedPSideBound_of_headTailClosureFrontier
#print axioms routeBRicherSPDPStableCandidate_obligations_of_headTailClosureFrontier
#print axioms routeBRicherSPDPStableCandidate_projectedPSideBound_of_headTailStableMapsFrontier
#print axioms routeBRicherSPDPStableCandidate_projectedPSideBound_of_headTailProjectionIntertwiningFrontier
#print axioms routeBRicherSPDPStableCandidate_obligations_of_headTailStableMapsFrontier
#print axioms routeBRicherSPDPStableCandidate_obligations_of_headTailProjectionIntertwiningFrontier

end PallLean.Paper93.Paper283
