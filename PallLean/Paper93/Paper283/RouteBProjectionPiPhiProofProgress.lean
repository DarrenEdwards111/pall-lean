import PallLean.Paper93.Paper283.RouteBProjectionRetargetProgress
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadSpanStableMapsProof
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailKernelCriterionProof
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailDescentObstruction

/-!
# PiPhi/head-span projection proof progress

This file keeps the Route B PiPhi/head-span retarget work separate from the
ruled-out broad multilinear-tail/complement route.

It records two checked facts:

* the orbit-closure and chosen-projection fields reduce to the current
  second-pass and chosen-kernel stability frontiers;
* the retarget package, as currently defined, cannot be fully constructed
  because its global admissible-query log-window side condition is refuted by
  a one-variable high-degree admissible shift.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- The finite head-span second-pass closure proves the coefficient-level
orbit closure required by the PiPhi/head-span retarget rows. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_orbitCoefficientClosure_of_secondPassClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hsecond :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorSecondPassClosure
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitCoefficientClosure
      M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_logWindowHeadSpanOrbitCoefficientClosure_of_stableGeneratorMaps
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_of_generatorSecondPassClosure
      M n hn2 htb hns hsecond)

/-- Chosen projection-kernel stability proves the descent field for the
canonical head-span tail projection. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_projectionDescent_of_projectionKernelStable
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hstable :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
      M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_of_projectionKernelStableGeneratorMaps
    M n hn2 htb hns hstable

/-- The same chosen-kernel stability proves the projection-intertwining
surface used by the retarget constructor. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_projectionIntertwines_of_projectionKernelStable
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hstable :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionIntertwines
      M n hn2 htb hns :=
  (routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionIntertwines_iff_descent
    M n hn2 htb hns).mpr
    (routeBPaperFaithfulPiPhiHeadSpan_projectionDescent_of_projectionKernelStable
      M n hn2 htb hns hstable)

/-- Positive constructor for every non-window PiPhi/head-span proof field:
second-pass head-span closure supplies row closure, chosen-kernel stability
supplies descent, and the remaining global log-window consumer bridge is kept
as an explicit hypothesis. -/
theorem routeBPaperFaithfulPiPhiHeadSpanProjectionRetarget_of_secondPass_kernelStable_window
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hsecond :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorSecondPassClosure
        M n hn2 htb hns)
    (hstable :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
        M n hn2 htb hns)
    (hwindow :
      RouteBRicherSPDPStableCandidateAdmissibleQueriesLogWindowed
        M n hn2 htb hns) :
    RouteBPaperFaithfulPiPhiHeadSpanProjectionRetarget
      M n hn2 htb hns :=
  routeBPaperFaithfulPiPhiHeadSpanProjectionRetarget_of_headSpanOrbitCoefficientClosure_descent
    M n hn2 htb hns
    (routeBPaperFaithfulPiPhiHeadSpan_orbitCoefficientClosure_of_secondPassClosure
      M n hn2 htb hns hsecond)
    (routeBPaperFaithfulPiPhiHeadSpan_projectionDescent_of_projectionKernelStable
      M n hn2 htb hns hstable)
    hwindow

/-- Escape-free form of the same constructor: absence of a head-span
generator-map escape closes orbit closure, and absence of a chosen-kernel
obstruction closes descent. -/
theorem routeBPaperFaithfulPiPhiHeadSpanProjectionRetarget_of_no_headSpanGeneratorMapEscape_no_kernelObstruction_window
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hnoHead :
      ¬ RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorMapEscapeWitness
        M n hn2 htb hns)
    (hnoKernel :
      ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelObstruction
        M n hn2 htb hns)
    (hwindow :
      RouteBRicherSPDPStableCandidateAdmissibleQueriesLogWindowed
        M n hn2 htb hns) :
    RouteBPaperFaithfulPiPhiHeadSpanProjectionRetarget
      M n hn2 htb hns :=
  routeBPaperFaithfulPiPhiHeadSpanProjectionRetarget_of_headSpanOrbitCoefficientClosure_descent
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_logWindowHeadSpanOrbitCoefficientClosure_of_stableGeneratorMaps
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_of_no_headSpanGeneratorMapEscape
        M n hn2 htb hns hnoHead))
    (routeBRicherSPDPStableCandidate_headSpanTailChosenProjectionDescent_of_no_kernelObstruction
      M n hn2 htb hns hnoKernel)
    hwindow

/-- A one-variable query is block-admissible for any Cook-Levin block
partition. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_firstVar_singleton_blockAdmissible
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition
      [satDeciderGaugeFirstVar M n hn2 htb hns] := by
  constructor
  · simp
  · intro b
    by_cases hb :
        (cook_levin_compilation M n hn2 htb hns).partition.assign
            (satDeciderGaugeFirstVar M n hn2 htb hns) = b
    · simp [hb]
    · simp [hb]

/-- Concrete obstruction to the global log-window consumer bridge: the current
unbounded admissible-query API accepts a singleton derivative list with an
arbitrarily high-degree shift. -/
theorem routeBRicherSPDPStableCandidate_not_admissibleQueriesLogWindowed_of_highDegree_firstVar
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    ¬ RouteBRicherSPDPStableCandidateAdmissibleQueriesLogWindowed
        M n hn2 htb hns := by
  classical
  refine
    routeBRicherSPDPStableCandidate_not_admissibleQueriesLogWindowed_of_highDegree_admissible
      M n hn2 htb hns ?_
  let first := satDeciderGaugeFirstVar M n hn2 htb hns
  refine
    ⟨1, Nat.log 2 n + 1, [first],
      (MvPolynomial.X first : SATDeciderGaugeSpace M n hn2 htb hns) ^
        (Nat.log 2 n + 1),
      ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp [first]
  · intro v hv
    have hv' : v ∈ (MvPolynomial.X first : SATDeciderGaugeSpace M n hn2 htb hns).vars := by
      exact MvPolynomial.vars_pow
        (MvPolynomial.X first : SATDeciderGaugeSpace M n hn2 htb hns)
        (Nat.log 2 n + 1) hv
    have hvfirst : v = first := by
      simpa using hv'
    simpa [first] using hvfirst
  · simpa [first] using
      routeBPaperFaithfulPiPhiHeadSpan_firstVar_singleton_blockAdmissible
        M n hn2 htb hns
  · simp [first]

/-- Therefore the current PiPhi/head-span retarget package is not
constructible as stated: its `admissible_queries_log_windowed` field is a
false global side condition, independently of the head-span row choice. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_noProjectionRetarget
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    ¬ RouteBPaperFaithfulPiPhiHeadSpanProjectionRetarget
        M n hn2 htb hns := by
  intro retarget
  exact
    (routeBRicherSPDPStableCandidate_not_admissibleQueriesLogWindowed_of_highDegree_firstVar
      M n hn2 htb hns)
      retarget.admissible_queries_log_windowed

/-! ## Axiom audit anchors -/

#print axioms routeBPaperFaithfulPiPhiHeadSpan_orbitCoefficientClosure_of_secondPassClosure
#print axioms routeBPaperFaithfulPiPhiHeadSpan_projectionDescent_of_projectionKernelStable
#print axioms routeBPaperFaithfulPiPhiHeadSpan_projectionIntertwines_of_projectionKernelStable
#print axioms routeBPaperFaithfulPiPhiHeadSpanProjectionRetarget_of_secondPass_kernelStable_window
#print axioms routeBPaperFaithfulPiPhiHeadSpanProjectionRetarget_of_no_headSpanGeneratorMapEscape_no_kernelObstruction_window
#print axioms routeBPaperFaithfulPiPhiHeadSpan_firstVar_singleton_blockAdmissible
#print axioms routeBRicherSPDPStableCandidate_not_admissibleQueriesLogWindowed_of_highDegree_firstVar
#print axioms routeBPaperFaithfulPiPhiHeadSpan_noProjectionRetarget

end PallLean.Paper93.Paper283
