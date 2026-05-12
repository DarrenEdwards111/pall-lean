import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadSpanOrbitClosureBridge

/-!
# Exact row-closure form of the head-tail orbit obligation

For the canonical log-window head-span tail, the finite-row log-window
row-closure input is equivalent to the head-span orbit-coefficient closure
input.  The zero row is handled by the already-proved log-window head cover;
the tail rows are basis elements of the head span.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Head-span orbit coefficient closure implies finite-row log-window
row-closure for the prepended concrete-NP row plus canonical head-span tail. -/
theorem routeBRicherSPDPStableCandidate_headTailLogWindowRowClosure_of_headSpanOrbitCoefficientClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hclosure :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitCoefficientClosure
        M n hn2 htb hns) :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowRowClosure M n hn2 htb hns
      (routeBRicherSPDPStableCandidateRows M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)) := by
  constructor
  intro spdpKappa ell S shift
    hSlen hshiftDegree hKappaLog hEllLog hshiftVars hadm i
  refine Fin.cases ?zero ?succ i
  · simpa [routeBRicherSPDPStableCandidateRows,
      routeBRicherConcreteNPPrependedRows] using
      routeBRicherSPDPStableCandidate_logWindowHeadMlCovering_for_headSpanTail
        M n hn2 htb hns
        spdpKappa ell S shift
        hSlen hshiftDegree
        (by simpa [hSlen] using hKappaLog)
        (le_trans hshiftDegree hEllLog)
        hshiftVars hadm
  · intro j
    have hcoeff :=
      hclosure spdpKappa ell
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns j)
        S shift
        (routeBRicherSPDPStableCandidateLogWindowHeadTail_mem_headSpan
          M n hn2 htb hns j)
        hSlen hshiftDegree
        (by simpa [hSlen] using hKappaLog)
        (le_trans hshiftDegree hEllLog)
        hshiftVars hadm
    exact
      (mem_finiteRowsSubmodule_iff_exists_linearCombination
        (routeBRicherSPDPStableCandidateRows M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail
            M n hn2 htb hns))
        (routeBSPDPGeneratorRow M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail
            M n hn2 htb hns j)
          S shift)).2 hcoeff

/-- For the canonical head-span tail, finite-row log-window row closure is
exactly the head-span orbit-coefficient closure obligation. -/
theorem routeBRicherSPDPStableCandidate_headTailLogWindowRowClosure_iff_headSpanOrbitCoefficientClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowRowClosure M n hn2 htb hns
        (routeBRicherSPDPStableCandidateRows M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail
            M n hn2 htb hns)) ↔
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitCoefficientClosure
        M n hn2 htb hns := by
  constructor
  · exact
      routeBRicherSPDPStableCandidate_headSpanOrbitCoefficientClosure_of_logWindowRowClosure
        M n hn2 htb hns
  · exact
      routeBRicherSPDPStableCandidate_headTailLogWindowRowClosure_of_headSpanOrbitCoefficientClosure
        M n hn2 htb hns

/-! ## Axiom audit anchors -/

#print axioms routeBRicherSPDPStableCandidate_headTailLogWindowRowClosure_of_headSpanOrbitCoefficientClosure
#print axioms routeBRicherSPDPStableCandidate_headTailLogWindowRowClosure_iff_headSpanOrbitCoefficientClosure

end PallLean.Paper93.Paper283
