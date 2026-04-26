import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadCover
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateTailStability

/-!
# Head-span tail orbit interface for the Route B SPDP-stable candidate

The finite head-span tail is a basis for the supremum of the concrete head's
log-window strict blocked-SPDP subspaces.  This file records the remaining
closure obligation needed to make that finite tail self-stable under the same
log-window generator rows.

The missing mathematical input is coefficient-level: every log-window generator
row of every element of the head span must be a finite linear combination of
the prepended concrete-NP row and the selected head-span basis rows.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- The head-span basis tail actually lands in the finite log-window head
span. -/
theorem routeBRicherSPDPStableCandidateLogWindowHeadTail_mem_headSpan
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (i :
      Fin
        (Module.finrank Rat
          (routeBRicherSPDPStableCandidateLogWindowHeadSpan
            M n hn2 htb hns))) :
    routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns i ∈
      routeBRicherSPDPStableCandidateLogWindowHeadSpan
        M n hn2 htb hns := by
  let U := routeBRicherSPDPStableCandidateLogWindowHeadSpan
    M n hn2 htb hns
  let b : Module.Basis (Fin (Module.finrank Rat U)) Rat U :=
    Module.finBasis Rat U
  change ((b i : U) : SATDeciderGaugeSpace M n hn2 htb hns) ∈ U
  exact (b i).property

/-- Coefficient-level log-window orbit closure for the whole finite head span.

This is the narrow missing closure statement for the head-span construction:
if `p` belongs to the finite supremum of head SPDP subspaces, then every
log-window generator row of `p` is represented by coefficients on the concrete
NP head row plus the head-span basis tail rows. -/
def RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitCoefficientClosure
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
    ∃ coeff :
        Fin
          (Module.finrank Rat
              (routeBRicherSPDPStableCandidateLogWindowHeadSpan
                M n hn2 htb hns) + 1) ->
          Rat,
      routeBSPDPGeneratorRow M n hn2 htb hns p S shift =
        Finset.univ.sum
          (fun j =>
            coeff j •
              routeBRicherSPDPStableCandidateRows
                M n hn2 htb hns
                (routeBRicherSPDPStableCandidateLogWindowHeadTail
                  M n hn2 htb hns) j)

/-- The head-span coefficient-closure obligation is exactly strong enough to
prove coefficient-level finite-orbit closure for the concrete head-span basis
tail. -/
theorem routeBRicherSPDPStableCandidate_tailFiniteOrbitClosure_for_headSpanTail_of_headSpanOrbitCoefficientClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hclosure :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitCoefficientClosure
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowTailFiniteOrbitClosure
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns) := by
  intro spdpKappa ell S shift
    hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm i
  exact
    hclosure spdpKappa ell
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns i)
      S shift
      (routeBRicherSPDPStableCandidateLogWindowHeadTail_mem_headSpan
        M n hn2 htb hns i)
      hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm

/-! ## Axiom audit anchors -/

#print axioms routeBRicherSPDPStableCandidateLogWindowHeadTail_mem_headSpan
#print axioms RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitCoefficientClosure
#print axioms routeBRicherSPDPStableCandidate_tailFiniteOrbitClosure_for_headSpanTail_of_headSpanOrbitCoefficientClosure

end PallLean.Paper93.Paper283
