import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailOrbit

/-!
# Head-span orbit closure bridge for the Route B SPDP-stable candidate

This file reduces the head-span orbit coefficient-closure obligation to the
existing finite-row log-window row-closure API.  The key point is that the
finite head span is already contained in the prepended head-tail row span, so
row closure of those selected rows propagates to every head-span element by
linearity of `routeBSPDPGeneratorRow`.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Finite-row log-window row closure of the prepended head-tail rows implies
coefficient-level log-window orbit closure for every element of the finite
head span. -/
theorem routeBRicherSPDPStableCandidate_headSpanOrbitCoefficientClosure_of_logWindowRowClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (rowClosure :
      RouteBRicherGaugeFiniteRowsSPDPLogWindowRowClosure M n hn2 htb hns
        (routeBRicherSPDPStableCandidateRows M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail
            M n hn2 htb hns))) :
    RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitCoefficientClosure
      M n hn2 htb hns := by
  intro spdpKappa ell p S shift hpHead _hSlen _hshiftDegree
    hSlog hshiftLog hshiftVars hadm
  let tail := routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns
  let rows := routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail
  have hpRows : p ∈ finiteRowsSubmodule rows := by
    exact
      routeBRicherSPDPStableCandidateLogWindowHeadSpan_le_candidateRowsSpan
        M n hn2 htb hns hpHead
  have hrowClosure :
      forall i,
        routeBSPDPGeneratorRow M n hn2 htb hns (rows i) S shift
          ∈ finiteRowsSubmodule rows := by
    intro i
    exact
      rowClosure.row_closure S.length shift.totalDegree S shift
        rfl le_rfl hSlog hshiftLog hshiftVars hadm i
  have hmem :
      routeBSPDPGeneratorRow M n hn2 htb hns p S shift
        ∈ finiteRowsSubmodule rows :=
    routeBSPDPGeneratorRow_mem_finiteRowsSubmodule_of_mem_of_rowClosure
      M n hn2 htb hns rows S shift hpRows hrowClosure
  exact
    (mem_finiteRowsSubmodule_iff_exists_linearCombination rows
      (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)).1 hmem

/-- Consequently, log-window row closure of the prepended head-tail rows gives
the concrete finite-orbit closure field used by the head-tail frontier. -/
theorem routeBRicherSPDPStableCandidate_tailFiniteOrbitClosure_for_headSpanTail_of_logWindowRowClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (rowClosure :
      RouteBRicherGaugeFiniteRowsSPDPLogWindowRowClosure M n hn2 htb hns
        (routeBRicherSPDPStableCandidateRows M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail
            M n hn2 htb hns))) :
    RouteBRicherSPDPStableCandidateLogWindowTailFiniteOrbitClosure
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_tailFiniteOrbitClosure_for_headSpanTail_of_headSpanOrbitCoefficientClosure
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headSpanOrbitCoefficientClosure_of_logWindowRowClosure
      M n hn2 htb hns rowClosure)

/-! ## Axiom audit anchors -/

#print axioms routeBRicherSPDPStableCandidate_headSpanOrbitCoefficientClosure_of_logWindowRowClosure
#print axioms routeBRicherSPDPStableCandidate_tailFiniteOrbitClosure_for_headSpanTail_of_logWindowRowClosure

end PallLean.Paper93.Paper283
