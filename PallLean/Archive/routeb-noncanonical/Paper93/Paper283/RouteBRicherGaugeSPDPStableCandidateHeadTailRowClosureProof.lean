import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailClosureEquiv
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailSharpFrontier

/-!
# Head-tail row closure for the Route B SPDP-stable candidate

This module pins down the positive finite-row log-window row-closure input for
the canonical head-span tail.  The exact row-closure field is equivalent to
head-span orbit coefficient closure; the remaining sharp input is stability of
the finite log-window head span under the log-window SPDP generator maps.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Stability of the canonical head span under the log-window generator maps
is the remaining sharp blocker for the requested finite-row row-closure input. -/
theorem routeBRicherSPDPStableCandidate_headTailLogWindowRowClosure_of_headSpanStableGeneratorMaps
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hstable :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanStableGeneratorMaps
        M n hn2 htb hns) :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowRowClosure M n hn2 htb hns
      (routeBRicherSPDPStableCandidateRows M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)) :=
  routeBRicherSPDPStableCandidate_headTailLogWindowRowClosure_of_headSpanOrbitCoefficientClosure
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_logWindowHeadSpanOrbitCoefficientClosure_of_stableGeneratorMaps
      M n hn2 htb hns hstable)

/-- Head-span generator-map stability, chosen-projection descent, and the two
existing P-side consumer fields instantiate the sharp head-tail
row-closure/descent frontier. -/
def routeBRicherSPDPStableCandidate_headTailRowClosureDescentFrontier_of_headSpanStableGeneratorMaps
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hstable :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanStableGeneratorMaps
        M n hn2 htb hns)
    (descent :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
        M n hn2 htb hns)
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPLogWindowUnprojectedPreimage
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateRows M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail
            M n hn2 htb hns)))
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHeadTailRowClosureDescentFrontier
      M n hn2 htb hns where
  row_closure :=
    routeBRicherSPDPStableCandidate_headTailLogWindowRowClosure_of_headSpanStableGeneratorMaps
      M n hn2 htb hns hstable
  projection_descent := descent
  unprojected_preimage := preimage
  p_window_cover := cover

/-- Consequently, the same reduced positive inputs prove the Section 39-facing
holographic-invariance theorem for the canonical head-span tail. -/
theorem routeBRicherSPDPStableCandidate_holographicInvariance_for_headSpanTail_of_headSpanStableGeneratorMaps_descent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hstable :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanStableGeneratorMaps
        M n hn2 htb hns)
    (descent :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHolographicInvariance
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_holographicInvariance_of_rowClosure_descent
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headTailLogWindowRowClosure_of_headSpanStableGeneratorMaps
      M n hn2 htb hns hstable)
    descent

/-! ## Axiom audit anchors -/

#print axioms routeBRicherSPDPStableCandidate_headTailLogWindowRowClosure_of_headSpanStableGeneratorMaps
#print axioms routeBRicherSPDPStableCandidate_headTailRowClosureDescentFrontier_of_headSpanStableGeneratorMaps
#print axioms routeBRicherSPDPStableCandidate_holographicInvariance_for_headSpanTail_of_headSpanStableGeneratorMaps_descent

end PallLean.Paper93.Paper283
