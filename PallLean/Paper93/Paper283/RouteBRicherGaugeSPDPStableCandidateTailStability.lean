import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateProfileTail

/-!
# Tail-row stability bridges for the Route B SPDP-stable candidate

This module isolates the finite-orbit closure interface for log-window tail
rows.  The interface is coefficient-level: every log-window SPDP generator row
from a selected tail row is explicitly a finite linear combination of the
prepended head/tail rows.  It is equivalent to the existing span-membership
tail-stability predicate, but is closer to finite/profile row-enumeration
proofs.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Coefficient-level finite-orbit closure for selected tail rows inside the
canonical log window.  This is the finite/profile proof target: every
log-window generator row from a tail row is represented by coefficients on the
prepended concrete-NP head row plus selected tail rows. -/
def RouteBRicherSPDPStableCandidateLogWindowTailFiniteOrbitClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) : Prop :=
  forall (spdpKappa ell : Nat)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    S.length <= Nat.log 2 n ->
    shift.totalDegree <= Nat.log 2 n ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    forall i : Fin m,
      ∃ coeff : Fin (m + 1) -> Rat,
        routeBSPDPGeneratorRow M n hn2 htb hns (tail i) S shift =
          Finset.univ.sum
            (fun j =>
              coeff j •
                routeBRicherSPDPStableCandidateRows
                  M n hn2 htb hns tail j)

/-- The coefficient-level finite-orbit interface is exactly strong enough to
prove the existing log-window tail-row stability predicate. -/
theorem routeBRicherSPDPStableCandidate_logWindowTailRowStable_of_tailFiniteOrbitClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hclosure :
      RouteBRicherSPDPStableCandidateLogWindowTailFiniteOrbitClosure
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateLogWindowTailRowStable
      M n hn2 htb hns tail := by
  intro spdpKappa ell S shift
    hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm i
  exact
    (mem_finiteRowsSubmodule_iff_exists_linearCombination
      (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail)
      (routeBSPDPGeneratorRow M n hn2 htb hns (tail i) S shift)).2
      (hclosure spdpKappa ell S shift
        hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm i)

/-- Conversely, existing log-window tail-row stability exposes explicit
finite-row coefficients for every tail generator row. -/
theorem routeBRicherSPDPStableCandidate_tailFiniteOrbitClosure_of_logWindowTailRowStable
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hstable :
      RouteBRicherSPDPStableCandidateLogWindowTailRowStable
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateLogWindowTailFiniteOrbitClosure
      M n hn2 htb hns tail := by
  intro spdpKappa ell S shift
    hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm i
  exact
    (mem_finiteRowsSubmodule_iff_exists_linearCombination
      (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail)
      (routeBSPDPGeneratorRow M n hn2 htb hns (tail i) S shift)).1
      (hstable spdpKappa ell S shift
        hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm i)

/-- The coefficient-level finite-orbit interface is equivalent to the existing
span-membership tail-row stability predicate. -/
theorem routeBRicherSPDPStableCandidate_tailFiniteOrbitClosure_iff_logWindowTailRowStable
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowTailFiniteOrbitClosure
        M n hn2 htb hns tail ↔
      RouteBRicherSPDPStableCandidateLogWindowTailRowStable
        M n hn2 htb hns tail := by
  constructor
  · exact
      routeBRicherSPDPStableCandidate_logWindowTailRowStable_of_tailFiniteOrbitClosure
        M n hn2 htb hns tail
  · exact
      routeBRicherSPDPStableCandidate_tailFiniteOrbitClosure_of_logWindowTailRowStable
        M n hn2 htb hns tail

/-- A standard finite-row log-window row-closure proof for the prepended
stable-candidate rows supplies the coefficient-level tail finite-orbit
closure by querying the `Fin.succ` tail rows. -/
theorem routeBRicherSPDPStableCandidate_tailFiniteOrbitClosure_of_finiteRowsLogWindowRowClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (rowClosure :
      RouteBRicherGaugeFiniteRowsSPDPLogWindowRowClosure M n hn2 htb hns
        (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail)) :
    RouteBRicherSPDPStableCandidateLogWindowTailFiniteOrbitClosure
      M n hn2 htb hns tail := by
  intro spdpKappa ell S shift
    hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm i
  have hKappaLog : spdpKappa <= Nat.log 2 n := by
    simpa [hSlen] using hSlog
  have hmem :
      routeBSPDPGeneratorRow M n hn2 htb hns (tail i) S shift ∈
        finiteRowsSubmodule
          (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail) := by
    simpa [routeBRicherSPDPStableCandidateRows,
      routeBRicherConcreteNPPrependedRows] using
      rowClosure.row_closure
        spdpKappa shift.totalDegree S shift
        hSlen le_rfl hKappaLog hshiftLog hshiftVars hadm
        (Fin.succ i)
  exact
    (mem_finiteRowsSubmodule_iff_exists_linearCombination
      (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail)
      (routeBSPDPGeneratorRow M n hn2 htb hns (tail i) S shift)).1
      hmem

/-- The concrete prepended-row log-window package also supplies the
coefficient-level tail finite-orbit closure. -/
theorem routeBRicherSPDPStableCandidate_tailFiniteOrbitClosure_of_spdpLogWindowRowClosurePackage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (pkg :
      RouteBRicherConcreteNPPrependedRowsSPDPLogWindowRowClosurePackage
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateLogWindowTailFiniteOrbitClosure
      M n hn2 htb hns tail := by
  apply
    routeBRicherSPDPStableCandidate_tailFiniteOrbitClosure_of_finiteRowsLogWindowRowClosure
      M n hn2 htb hns tail
  simpa [routeBRicherSPDPStableCandidateRows] using
    routeBRicherConcreteNPPrependedRows_spdpLogWindowRowClosure_of_package
      M n hn2 htb hns tail pkg

/-- Head coverage plus coefficient-level tail finite-orbit closure gives full
log-window orbit coverage for the stable candidate. -/
theorem routeBRicherSPDPStableCandidate_logWindowOrbitMlCovering_of_head_tailFiniteOrbitClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hhead :
      RouteBRicherSPDPStableCandidateLogWindowHeadMlCovering
        M n hn2 htb hns tail)
    (htail :
      RouteBRicherSPDPStableCandidateLogWindowTailFiniteOrbitClosure
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateLogWindowOrbitMlCovering
      M n hn2 htb hns tail :=
  routeBRicherSPDPStableCandidate_logWindowOrbitMlCovering_of_head_tailStable
    M n hn2 htb hns tail hhead
    (routeBRicherSPDPStableCandidate_logWindowTailRowStable_of_tailFiniteOrbitClosure
      M n hn2 htb hns tail htail)

/-- Head coverage plus coefficient-level tail finite-orbit closure gives the
concrete prepended-row log-window package consumed by the finite-row SPDP
frontier. -/
theorem routeBRicherSPDPStableCandidate_spdpLogWindowRowClosurePackage_of_head_tailFiniteOrbitClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hhead :
      RouteBRicherSPDPStableCandidateLogWindowHeadMlCovering
        M n hn2 htb hns tail)
    (htail :
      RouteBRicherSPDPStableCandidateLogWindowTailFiniteOrbitClosure
        M n hn2 htb hns tail) :
    RouteBRicherConcreteNPPrependedRowsSPDPLogWindowRowClosurePackage
      M n hn2 htb hns tail :=
  routeBRicherSPDPStableCandidate_spdpLogWindowRowClosurePackage_of_head_tailStable
    M n hn2 htb hns tail hhead
    (routeBRicherSPDPStableCandidate_logWindowTailRowStable_of_tailFiniteOrbitClosure
      M n hn2 htb hns tail htail)

/-- Any full multilinear-covering tail is tail-row stable inside the log
window.  This separates the tail-stability consequence from head coverage. -/
theorem routeBRicherSPDPStableCandidate_logWindowTailRowStable_of_mlCovering
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcov :
      RouteBRicherSPDPStableCandidateMlCovering
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateLogWindowTailRowStable
      M n hn2 htb hns tail :=
  routeBRicherSPDPStableCandidate_logWindowTailRowStable_of_logWindowOrbitMlCovering
    M n hn2 htb hns tail
    (routeBRicherSPDPStableCandidate_logWindowOrbitMlCovering_of_mlCovering
      M n hn2 htb hns tail hcov)

/-- Actual tail-row stability for the existing concrete multilinear tail. -/
theorem routeBRicherSPDPStableCandidate_logWindowTailRowStable_for_multilinearTail
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowTailRowStable
      M n hn2 htb hns
      (routeBRicherMultilinearTailRows M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_logWindowTailRowStable_of_mlCovering
    M n hn2 htb hns
    (routeBRicherMultilinearTailRows M n hn2 htb hns)
    (routeBRicherSPDPStableCandidate_mlCovering_for_multilinearTail
      M n hn2 htb hns)

/-- Coefficient-level finite-orbit closure for the existing concrete
multilinear tail. -/
theorem routeBRicherSPDPStableCandidate_tailFiniteOrbitClosure_for_multilinearTail
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowTailFiniteOrbitClosure
      M n hn2 htb hns
      (routeBRicherMultilinearTailRows M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_tailFiniteOrbitClosure_of_logWindowTailRowStable
    M n hn2 htb hns
    (routeBRicherMultilinearTailRows M n hn2 htb hns)
    (routeBRicherSPDPStableCandidate_logWindowTailRowStable_for_multilinearTail
      M n hn2 htb hns)

/-! ## Axiom audit anchors -/

#print axioms RouteBRicherSPDPStableCandidateLogWindowTailFiniteOrbitClosure
#print axioms routeBRicherSPDPStableCandidate_logWindowTailRowStable_of_tailFiniteOrbitClosure
#print axioms routeBRicherSPDPStableCandidate_tailFiniteOrbitClosure_of_logWindowTailRowStable
#print axioms routeBRicherSPDPStableCandidate_tailFiniteOrbitClosure_iff_logWindowTailRowStable
#print axioms routeBRicherSPDPStableCandidate_tailFiniteOrbitClosure_of_finiteRowsLogWindowRowClosure
#print axioms routeBRicherSPDPStableCandidate_tailFiniteOrbitClosure_of_spdpLogWindowRowClosurePackage
#print axioms routeBRicherSPDPStableCandidate_logWindowOrbitMlCovering_of_head_tailFiniteOrbitClosure
#print axioms routeBRicherSPDPStableCandidate_spdpLogWindowRowClosurePackage_of_head_tailFiniteOrbitClosure
#print axioms routeBRicherSPDPStableCandidate_logWindowTailRowStable_of_mlCovering
#print axioms routeBRicherSPDPStableCandidate_logWindowTailRowStable_for_multilinearTail
#print axioms routeBRicherSPDPStableCandidate_tailFiniteOrbitClosure_for_multilinearTail

end PallLean.Paper93.Paper283
