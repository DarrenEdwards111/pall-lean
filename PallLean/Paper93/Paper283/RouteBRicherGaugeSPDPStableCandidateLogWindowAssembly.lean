import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadCover
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateTailStability
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateComplement

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

/-- Component form of the log-window frontier.  This is the precise current
worklist: head subspace cover, tail-row stability, complement invariance,
log-window unprojected preimage, and the P-window finite-span cover. -/
structure RouteBRicherSPDPStableCandidateLogWindowComponentFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    Type where
  head_subspace_cover :
    RouteBRicherSPDPStableCandidateLogWindowHeadSPDPSubspaceCovered
      M n hn2 htb hns tail
  tail_row_stable :
    RouteBRicherSPDPStableCandidateLogWindowTailRowStable
      M n hn2 htb hns tail
  complement_invariant :
    RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
      M n hn2 htb hns tail
  unprojected_preimage :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowUnprojectedPreimage
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail)
  p_window_cover :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns

/-- Coefficient-level component form of the log-window frontier.  This is the
same current worklist, but with actual finite-orbit witnesses for the tail
rows instead of only the span-membership tail-stability predicate. -/
structure RouteBRicherSPDPStableCandidateLogWindowFiniteOrbitComponentFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    Type where
  head_subspace_cover :
    RouteBRicherSPDPStableCandidateLogWindowHeadSPDPSubspaceCovered
      M n hn2 htb hns tail
  tail_finite_orbit_closure :
    RouteBRicherSPDPStableCandidateLogWindowTailFiniteOrbitClosure
      M n hn2 htb hns tail
  complement_invariant :
    RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
      M n hn2 htb hns tail
  unprojected_preimage :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowUnprojectedPreimage
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail)
  p_window_cover :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns

/-- Head subspace cover plus tail-row stability and log-window complement
invariance assemble the Section 39-facing holographic-invariance interface. -/
theorem routeBRicherSPDPStableCandidate_holographicInvariance_of_headCover_tailStable_complementInvariant
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hhead :
      RouteBRicherSPDPStableCandidateLogWindowHeadSPDPSubspaceCovered
        M n hn2 htb hns tail)
    (htail :
      RouteBRicherSPDPStableCandidateLogWindowTailRowStable
        M n hn2 htb hns tail)
    (hcompl :
      RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateHolographicInvariance
      M n hn2 htb hns tail where
  log_window_orbit_coverage :=
    routeBRicherSPDPStableCandidate_logWindowOrbitMlCovering_of_head_tailStable
      M n hn2 htb hns tail
      (routeBRicherSPDPStableCandidate_logWindowHeadMlCovering_of_headSPDPSubspaceCovered
        M n hn2 htb hns tail hhead)
      htail
  log_window_complement_invariant := hcompl

/-- Head subspace cover plus coefficient-level tail finite-orbit closure and
log-window complement invariance assemble the Section 39-facing
holographic-invariance interface. -/
theorem routeBRicherSPDPStableCandidate_holographicInvariance_of_headCover_tailFiniteOrbitClosure_complementInvariant
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hhead :
      RouteBRicherSPDPStableCandidateLogWindowHeadSPDPSubspaceCovered
        M n hn2 htb hns tail)
    (htail :
      RouteBRicherSPDPStableCandidateLogWindowTailFiniteOrbitClosure
        M n hn2 htb hns tail)
    (hcompl :
      RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateHolographicInvariance
      M n hn2 htb hns tail :=
  routeBRicherSPDPStableCandidate_holographicInvariance_of_headCover_tailStable_complementInvariant
    M n hn2 htb hns tail hhead
    (routeBRicherSPDPStableCandidate_logWindowTailRowStable_of_tailFiniteOrbitClosure
      M n hn2 htb hns tail htail)
    hcompl

/-- The component worklist assembles the packaged log-window P-frontier. -/
def routeBRicherSPDPStableCandidate_logWindowPFrontier_of_componentFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (frontier :
      RouteBRicherSPDPStableCandidateLogWindowComponentFrontier
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateLogWindowPFrontier
      M n hn2 htb hns tail where
  holographic_invariance :=
    routeBRicherSPDPStableCandidate_holographicInvariance_of_headCover_tailStable_complementInvariant
      M n hn2 htb hns tail
      frontier.head_subspace_cover
      frontier.tail_row_stable
      frontier.complement_invariant
  unprojected_preimage := frontier.unprojected_preimage
  p_window_cover := frontier.p_window_cover

/-- The coefficient-level component worklist lowers to the span-membership
component worklist. -/
def routeBRicherSPDPStableCandidate_componentFrontier_of_finiteOrbitComponentFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (frontier :
      RouteBRicherSPDPStableCandidateLogWindowFiniteOrbitComponentFrontier
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateLogWindowComponentFrontier
      M n hn2 htb hns tail where
  head_subspace_cover := frontier.head_subspace_cover
  tail_row_stable :=
    routeBRicherSPDPStableCandidate_logWindowTailRowStable_of_tailFiniteOrbitClosure
      M n hn2 htb hns tail frontier.tail_finite_orbit_closure
  complement_invariant := frontier.complement_invariant
  unprojected_preimage := frontier.unprojected_preimage
  p_window_cover := frontier.p_window_cover

/-- The coefficient-level component worklist assembles the packaged
log-window P-frontier. -/
def routeBRicherSPDPStableCandidate_logWindowPFrontier_of_finiteOrbitComponentFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (frontier :
      RouteBRicherSPDPStableCandidateLogWindowFiniteOrbitComponentFrontier
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateLogWindowPFrontier
      M n hn2 htb hns tail :=
  routeBRicherSPDPStableCandidate_logWindowPFrontier_of_componentFrontier
    M n hn2 htb hns tail
    (routeBRicherSPDPStableCandidate_componentFrontier_of_finiteOrbitComponentFrontier
      M n hn2 htb hns tail frontier)

/-- For the constructed log-window head-span tail, the remaining Section 39
obligations are exactly tail finite-orbit closure plus complement invariance. -/
theorem routeBRicherSPDPStableCandidate_holographicInvariance_for_headSpanTail_of_tailFiniteOrbitClosure_complementInvariant
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (htail :
      RouteBRicherSPDPStableCandidateLogWindowTailFiniteOrbitClosure
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns))
    (hcompl :
      RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)) :
    RouteBRicherSPDPStableCandidateHolographicInvariance
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_holographicInvariance_of_headCover_tailFiniteOrbitClosure_complementInvariant
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidateLogWindowHeadTail
      M n hn2 htb hns)
    (routeBRicherSPDPStableCandidate_logWindowHeadSPDPSubspaceCovered_for_headSpanTail
      M n hn2 htb hns)
    htail
    hcompl

/-- Component-frontier constructor specialized to the finite log-window
head-span tail. -/
def routeBRicherSPDPStableCandidate_finiteOrbitComponentFrontier_for_headSpanTail
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (htail :
      RouteBRicherSPDPStableCandidateLogWindowTailFiniteOrbitClosure
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns))
    (hcompl :
      RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns))
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPLogWindowUnprojectedPreimage
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateRows M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail
            M n hn2 htb hns)))
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowFiniteOrbitComponentFrontier
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns) where
  head_subspace_cover :=
    routeBRicherSPDPStableCandidate_logWindowHeadSPDPSubspaceCovered_for_headSpanTail
      M n hn2 htb hns
  tail_finite_orbit_closure := htail
  complement_invariant := hcompl
  unprojected_preimage := preimage
  p_window_cover := cover

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

/-- The component worklist proves the projected P-side bound. -/
theorem routeBRicherSPDPStableCandidate_projectedPSideBound_of_componentFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (frontier :
      RouteBRicherSPDPStableCandidateLogWindowComponentFrontier
        M n hn2 htb hns tail) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail) :=
  routeBRicherSPDPStableCandidate_projectedPSideBound_of_logWindowPFrontier
    M n hn2 htb hns tail
    (routeBRicherSPDPStableCandidate_logWindowPFrontier_of_componentFrontier
      M n hn2 htb hns tail frontier)

/-- The coefficient-level component worklist proves the projected P-side
bound. -/
theorem routeBRicherSPDPStableCandidate_projectedPSideBound_of_finiteOrbitComponentFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (frontier :
      RouteBRicherSPDPStableCandidateLogWindowFiniteOrbitComponentFrontier
        M n hn2 htb hns tail) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail) :=
  routeBRicherSPDPStableCandidate_projectedPSideBound_of_logWindowPFrontier
    M n hn2 htb hns tail
    (routeBRicherSPDPStableCandidate_logWindowPFrontier_of_finiteOrbitComponentFrontier
      M n hn2 htb hns tail frontier)

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

/-- Under the same log-window consumer bridge, the component worklist
discharges the stable-candidate row-closure and kernel-invisibility
obligations. -/
theorem routeBRicherSPDPStableCandidate_obligations_of_componentFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (frontier :
      RouteBRicherSPDPStableCandidateLogWindowComponentFrontier
        M n hn2 htb hns tail)
    (hwindow :
      RouteBRicherSPDPStableCandidateAdmissibleQueriesLogWindowed
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateObligations
      M n hn2 htb hns tail :=
  routeBRicherSPDPStableCandidate_obligations_of_logWindowPFrontier
    M n hn2 htb hns tail
    (routeBRicherSPDPStableCandidate_logWindowPFrontier_of_componentFrontier
      M n hn2 htb hns tail frontier)
    hwindow

/-- Under the same log-window consumer bridge, the coefficient-level component
worklist discharges the stable-candidate row-closure and kernel-invisibility
obligations. -/
theorem routeBRicherSPDPStableCandidate_obligations_of_finiteOrbitComponentFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (frontier :
      RouteBRicherSPDPStableCandidateLogWindowFiniteOrbitComponentFrontier
        M n hn2 htb hns tail)
    (hwindow :
      RouteBRicherSPDPStableCandidateAdmissibleQueriesLogWindowed
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateObligations
      M n hn2 htb hns tail :=
  routeBRicherSPDPStableCandidate_obligations_of_logWindowPFrontier
    M n hn2 htb hns tail
    (routeBRicherSPDPStableCandidate_logWindowPFrontier_of_finiteOrbitComponentFrontier
      M n hn2 htb hns tail frontier)
    hwindow

/-! ## Axiom audit anchors -/

#print axioms RouteBRicherSPDPStableCandidateLogWindowPFrontier
#print axioms RouteBRicherSPDPStableCandidateLogWindowComponentFrontier
#print axioms RouteBRicherSPDPStableCandidateLogWindowFiniteOrbitComponentFrontier
#print axioms routeBRicherSPDPStableCandidate_holographicInvariance_of_headCover_tailStable_complementInvariant
#print axioms routeBRicherSPDPStableCandidate_holographicInvariance_of_headCover_tailFiniteOrbitClosure_complementInvariant
#print axioms routeBRicherSPDPStableCandidate_logWindowPFrontier_of_componentFrontier
#print axioms routeBRicherSPDPStableCandidate_componentFrontier_of_finiteOrbitComponentFrontier
#print axioms routeBRicherSPDPStableCandidate_logWindowPFrontier_of_finiteOrbitComponentFrontier
#print axioms routeBRicherSPDPStableCandidate_holographicInvariance_for_headSpanTail_of_tailFiniteOrbitClosure_complementInvariant
#print axioms routeBRicherSPDPStableCandidate_finiteOrbitComponentFrontier_for_headSpanTail
#print axioms routeBRicherSPDPStableCandidate_projectedPSideBound_of_holographicInvariance_logWindowPreimage_cover
#print axioms routeBRicherSPDPStableCandidate_projectedPSideBound_of_logWindowPFrontier
#print axioms routeBRicherSPDPStableCandidate_projectedPSideBound_of_componentFrontier
#print axioms routeBRicherSPDPStableCandidate_projectedPSideBound_of_finiteOrbitComponentFrontier
#print axioms routeBRicherSPDPStableCandidate_obligations_of_logWindowPFrontier
#print axioms routeBRicherSPDPStableCandidate_obligations_of_componentFrontier
#print axioms routeBRicherSPDPStableCandidate_obligations_of_finiteOrbitComponentFrontier

end PallLean.Paper93.Paper283
