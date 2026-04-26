import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateProfileTail

/-!
# Log-window assembly for the Route B SPDP-stable candidate

This module packages the Section 39-facing holographic-invariance interface
with the log-window-only finite-row SPDP consumer.  It keeps the genuinely
mathematical obligations explicit:

* log-window orbit coverage and log-window complement invariance;
* log-window unprojected preimage for the selected finite rows;
* an unprojected P-window finite-span cover.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- The log-window frontier needed by the SPDP-stable finite-row candidate:
Section 39 holographic invariance, the log-window unprojected preimage side of
the SPDP map-preimage check, and the unprojected P-window finite-span cover. -/
structure RouteBRicherSPDPStableCandidateLogWindowPFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    Type where
  holographic_invariance :
    RouteBRicherSPDPStableCandidateHolographicInvariance
      M n hn2 htb hns tail
  unprojected_preimage :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowUnprojectedPreimage
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail)
  p_window_cover :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns

/-- Holographic invariance plus log-window unprojected preimage and a P-window
cover prove the projected P-side bound for the SPDP-stable finite-row
candidate. -/
theorem routeBRicherSPDPStableCandidate_projectedPSideBound_of_holographicInvariance_logWindowPreimage_cover
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (holo :
      RouteBRicherSPDPStableCandidateHolographicInvariance
        M n hn2 htb hns tail)
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPLogWindowUnprojectedPreimage
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail))
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail) :=
  routeBRicherConcreteNPPrependedRows_projectedPSideBound_of_logWindowRowClosurePackage_unprojectedPreimage_finiteSpanCover
    M n hn2 htb hns tail
    (routeBRicherSPDPStableCandidate_spdpLogWindowRowClosurePackage_of_logWindowOrbitMlCovering
      M n hn2 htb hns tail holo.log_window_orbit_coverage)
    preimage
    cover

/-- The packaged log-window frontier proves the projected P-side bound. -/
theorem routeBRicherSPDPStableCandidate_projectedPSideBound_of_logWindowPFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (frontier :
      RouteBRicherSPDPStableCandidateLogWindowPFrontier
        M n hn2 htb hns tail) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail) :=
  routeBRicherSPDPStableCandidate_projectedPSideBound_of_holographicInvariance_logWindowPreimage_cover
    M n hn2 htb hns tail
    frontier.holographic_invariance
    frontier.unprojected_preimage
    frontier.p_window_cover

/-- If the current unbounded SPDP API is restricted to log-window queries, the
same packaged frontier also discharges the stable-candidate row-closure and
kernel-invisibility obligations. -/
theorem routeBRicherSPDPStableCandidate_obligations_of_logWindowPFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (frontier :
      RouteBRicherSPDPStableCandidateLogWindowPFrontier
        M n hn2 htb hns tail)
    (hwindow :
      RouteBRicherSPDPStableCandidateAdmissibleQueriesLogWindowed
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateObligations
      M n hn2 htb hns tail :=
  routeBRicherSPDPStableCandidate_obligations_of_holographicInvariance
    M n hn2 htb hns tail
    frontier.holographic_invariance
    hwindow

/-! ## Axiom audit anchors -/

#print axioms RouteBRicherSPDPStableCandidateLogWindowPFrontier
#print axioms routeBRicherSPDPStableCandidate_projectedPSideBound_of_holographicInvariance_logWindowPreimage_cover
#print axioms routeBRicherSPDPStableCandidate_projectedPSideBound_of_logWindowPFrontier
#print axioms routeBRicherSPDPStableCandidate_obligations_of_logWindowPFrontier

end PallLean.Paper93.Paper283
