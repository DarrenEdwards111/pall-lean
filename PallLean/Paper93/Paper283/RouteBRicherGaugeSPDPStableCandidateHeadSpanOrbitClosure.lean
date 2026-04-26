import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailOrbit

/-!
# Head-span orbit-closure reductions for the Route B SPDP-stable candidate

This file records checked reductions for the remaining head-span orbit closure
obligation.  The useful mathematical target is invariance of the finite
log-window head span under each log-window generator linear map; once that is
proved, the existing finite basis tail and prepended concrete-NP row give the
required coefficient representation.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Direct row-span membership form of the head-span orbit-closure target.

This is the closest span-level version of
`RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitCoefficientClosure`:
for every head-span element and every log-window query, the produced generator
row already lies in the finite span of the prepended concrete-NP row and the
head-span basis tail. -/
def RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitRowsClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  forall (spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    p ∈ routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns ->
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    S.length <= Nat.log 2 n ->
    shift.totalDegree <= Nat.log 2 n ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∈
      finiteRowsSubmodule
        (routeBRicherSPDPStableCandidateRows M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail
            M n hn2 htb hns))

/-- Linear-map stability of the log-window head span under the same
log-window generator maps.

This is the sharp subspace-invariance target left by the head-span
construction.  It avoids mentioning coordinates on the chosen finite basis;
the coefficient statement follows by applying the already-proved containment
of the head span in the prepended candidate row span. -/
def RouteBRicherSPDPStableCandidateLogWindowHeadSpanStableGeneratorMaps
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
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
    Submodule.map
      (routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift)
      (routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns) <=
    routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns

/-- Span-level head-span orbit closure exposes the coefficient-level closure
predicate by converting finite-row-span membership to explicit coefficients. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadSpanOrbitCoefficientClosure_of_rowsClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hrows :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitRowsClosure
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitCoefficientClosure
      M n hn2 htb hns := by
  intro spdpKappa ell p S shift hp hSlen hshiftDegree hSlog hshiftLog
    hshiftVars hadm
  exact
    (mem_finiteRowsSubmodule_iff_exists_linearCombination
      (routeBRicherSPDPStableCandidateRows M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns))
      (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)).1
      (hrows spdpKappa ell p S shift hp hSlen hshiftDegree hSlog
        hshiftLog hshiftVars hadm)

/-- Stability of the head span under log-window generator maps gives the
span-level orbit closure, because the head-span basis tail already spans the
head span and the concrete-NP row is prepended to those finite rows. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadSpanOrbitRowsClosure_of_stableGeneratorMaps
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hstable :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanStableGeneratorMaps
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitRowsClosure
      M n hn2 htb hns := by
  intro spdpKappa ell p S shift hp hSlen hshiftDegree hSlog hshiftLog
    hshiftVars hadm
  have hmap :
      routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∈
        Submodule.map
          (routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift)
          (routeBRicherSPDPStableCandidateLogWindowHeadSpan
            M n hn2 htb hns) := by
    exact ⟨p, hp, rfl⟩
  have hhead :
      routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∈
        routeBRicherSPDPStableCandidateLogWindowHeadSpan
          M n hn2 htb hns := by
    simpa [routeBSPDPGeneratorRowLinearMap_apply] using
      (hstable spdpKappa ell S shift hSlen hshiftDegree hSlog hshiftLog
        hshiftVars hadm hmap)
  exact
    (routeBRicherSPDPStableCandidateLogWindowHeadSpan_le_candidateRowsSpan
      M n hn2 htb hns) hhead

/-- The main head-span coefficient closure reduces to the invariant-subspace
statement for the head span under all log-window generator maps. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadSpanOrbitCoefficientClosure_of_stableGeneratorMaps
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hstable :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanStableGeneratorMaps
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitCoefficientClosure
      M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_logWindowHeadSpanOrbitCoefficientClosure_of_rowsClosure
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_logWindowHeadSpanOrbitRowsClosure_of_stableGeneratorMaps
      M n hn2 htb hns hstable)

/-! ## Axiom audit anchors -/

#print axioms RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitRowsClosure
#print axioms RouteBRicherSPDPStableCandidateLogWindowHeadSpanStableGeneratorMaps
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadSpanOrbitCoefficientClosure_of_rowsClosure
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadSpanOrbitRowsClosure_of_stableGeneratorMaps
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadSpanOrbitCoefficientClosure_of_stableGeneratorMaps

end PallLean.Paper93.Paper283
