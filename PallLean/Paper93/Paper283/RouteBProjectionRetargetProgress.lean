import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailSharpFrontier
import PallLean.Paper93.Paper283.RouteBTransportNPIdentityMinor

/-!
# Route B projection retarget progress

This file records the current projection retarget away from the ruled-out broad
multilinear-tail selected complement.

The target here is the paper-faithful finite head-span row family: the concrete
coupled-sheet NP head row, prepended to a basis for the log-window SPDP head
span.  The corrected projection obligation is deliberately narrow:

* log-window row closure for this finite head-span row family;
* descent of the log-window generator maps through its chosen finite-row
  projection;
* the explicit bridge saying the current unbounded SPDP API only queries the
  log window.

Those three fields are enough to recover the finite-row kernel compatibility
and map-preimage surfaces consumed by the Route B SPDP side, without asserting
anything about the broad multilinear-tail complement.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- The retargeted PiPhi/head-span tail: a basis for the finite log-window
SPDP head span. -/
noncomputable abbrev routeBPaperFaithfulPiPhiHeadSpanTail
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    Fin
      (Module.finrank Rat
        (routeBRicherSPDPStableCandidateLogWindowHeadSpan
          M n hn2 htb hns)) ->
      SATDeciderGaugeSpace M n hn2 htb hns :=
  routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns

/-- The retargeted finite rows: coupled-sheet NP head row plus the log-window
head-span tail. -/
noncomputable abbrev routeBPaperFaithfulPiPhiHeadSpanRows
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    Fin
      (Module.finrank Rat
        (routeBRicherSPDPStableCandidateLogWindowHeadSpan
          M n hn2 htb hns) + 1) ->
      SATDeciderGaugeSpace M n hn2 htb hns :=
  routeBRicherSPDPStableCandidateRows M n hn2 htb hns
    (routeBPaperFaithfulPiPhiHeadSpanTail M n hn2 htb hns)

/-- The finite-row candidate gauge for the retargeted PiPhi/head-span rows. -/
noncomputable abbrev routeBPaperFaithfulPiPhiHeadSpanGauge
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidateGauge M n hn2 htb hns
    (routeBPaperFaithfulPiPhiHeadSpanTail M n hn2 htb hns)

/-- SAT-side projection map for the retargeted PiPhi/head-span rows. -/
noncomputable abbrev routeBPaperFaithfulPiPhiHeadSpanProjection
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    SATDeciderGaugeSpace M n hn2 htb hns →ₗ[Rat]
      SATDeciderGaugeSpace M n hn2 htb hns :=
  routeBNFrameCandidateAsSATGauge M n hn2 htb hns
    (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns)

/-- Minimal corrected projection obligation for the retargeted head-span rows.

The broad multilinear-tail complement is not part of this statement.  The
projection side is exactly the log-window descent condition for the chosen
finite-row projection on the head-span rows. -/
structure RouteBPaperFaithfulPiPhiHeadSpanProjectionRetarget
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    Prop where
  row_closure :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowRowClosure M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanRows M n hn2 htb hns)
  projection_descent :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
      M n hn2 htb hns
  admissible_queries_log_windowed :
    RouteBRicherSPDPStableCandidateAdmissibleQueriesLogWindowed
      M n hn2 htb hns

/-- Head-span orbit coefficient closure closes the row-closure field for the
retargeted PiPhi/head-span rows. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_rowClosure_of_headSpanOrbitCoefficientClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hclosure :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitCoefficientClosure
        M n hn2 htb hns) :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowRowClosure M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanRows M n hn2 htb hns) := by
  constructor
  intro spdpKappa ell S shift
    hSlen hshiftDegree hKappaLog hEllLog hshiftVars hadm i
  refine Fin.cases ?zero ?succ i
  · simpa [routeBPaperFaithfulPiPhiHeadSpanRows,
      routeBPaperFaithfulPiPhiHeadSpanTail,
      routeBRicherSPDPStableCandidateRows,
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
        (routeBPaperFaithfulPiPhiHeadSpanTail M n hn2 htb hns j)
        S shift
        (by
          simpa [routeBPaperFaithfulPiPhiHeadSpanTail] using
            routeBRicherSPDPStableCandidateLogWindowHeadTail_mem_headSpan
              M n hn2 htb hns j)
        hSlen hshiftDegree
        (by simpa [hSlen] using hKappaLog)
        (le_trans hshiftDegree hEllLog)
        hshiftVars hadm
    exact
      (mem_finiteRowsSubmodule_iff_exists_linearCombination
        (routeBPaperFaithfulPiPhiHeadSpanRows M n hn2 htb hns)
        (routeBSPDPGeneratorRow M n hn2 htb hns
          (routeBPaperFaithfulPiPhiHeadSpanTail M n hn2 htb hns j)
          S shift)).2 hcoeff

/-- Constructor for the minimal retarget obligation from head-span orbit
coefficient closure, direct chosen-projection descent, and the explicit
log-window query bridge. -/
theorem routeBPaperFaithfulPiPhiHeadSpanProjectionRetarget_of_headSpanOrbitCoefficientClosure_descent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hclosure :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitCoefficientClosure
        M n hn2 htb hns)
    (hdescent :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
        M n hn2 htb hns)
    (hwindow :
      RouteBRicherSPDPStableCandidateAdmissibleQueriesLogWindowed
        M n hn2 htb hns) :
    RouteBPaperFaithfulPiPhiHeadSpanProjectionRetarget
      M n hn2 htb hns where
  row_closure :=
    routeBPaperFaithfulPiPhiHeadSpan_rowClosure_of_headSpanOrbitCoefficientClosure
      M n hn2 htb hns hclosure
  projection_descent := hdescent
  admissible_queries_log_windowed := hwindow

/-- Constructor for the minimal retarget obligation using the existing
projection-intertwining criterion as the descent input. -/
theorem routeBPaperFaithfulPiPhiHeadSpanProjectionRetarget_of_headSpanOrbitCoefficientClosure_projectionIntertwines
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hclosure :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitCoefficientClosure
        M n hn2 htb hns)
    (hintertwines :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionIntertwines
        M n hn2 htb hns)
    (hwindow :
      RouteBRicherSPDPStableCandidateAdmissibleQueriesLogWindowed
        M n hn2 htb hns) :
    RouteBPaperFaithfulPiPhiHeadSpanProjectionRetarget
      M n hn2 htb hns :=
  routeBPaperFaithfulPiPhiHeadSpanProjectionRetarget_of_headSpanOrbitCoefficientClosure_descent
    M n hn2 htb hns
    hclosure
    ((routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionIntertwines_iff_descent
      M n hn2 htb hns).mp hintertwines)
    hwindow

/-- The minimal retarget obligation supplies the Section-39-facing
holographic-invariance interface for the head-span rows. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_holographicInvariance_of_retarget
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (retarget :
      RouteBPaperFaithfulPiPhiHeadSpanProjectionRetarget
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHolographicInvariance
      M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanTail M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_holographicInvariance_of_rowClosure_descent
    M n hn2 htb hns
    (by
      simpa [routeBPaperFaithfulPiPhiHeadSpanRows,
        routeBPaperFaithfulPiPhiHeadSpanTail] using
        retarget.row_closure)
    retarget.projection_descent

/-- The retargeted head-span obligation discharges the stable-candidate
row-closure and kernel-invisibility package. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_obligations_of_retarget
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (retarget :
      RouteBPaperFaithfulPiPhiHeadSpanProjectionRetarget
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateObligations
      M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanTail M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_obligations_of_holographicInvariance
    M n hn2 htb hns
    (routeBPaperFaithfulPiPhiHeadSpanTail M n hn2 htb hns)
    (routeBPaperFaithfulPiPhiHeadSpan_holographicInvariance_of_retarget
      M n hn2 htb hns retarget)
    retarget.admissible_queries_log_windowed

/-- Retarget theorem: the head-span PiPhi projection gives finite-row
kernel/complement compatibility for its own row family. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_kernelCompatibility_of_retarget
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (retarget :
      RouteBPaperFaithfulPiPhiHeadSpanProjectionRetarget
        M n hn2 htb hns) :
    RouteBRicherGaugeFiniteRowsSPDPKernelCompatibility
      M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanRows M n hn2 htb hns) := by
  have obligations :=
    routeBPaperFaithfulPiPhiHeadSpan_obligations_of_retarget
      M n hn2 htb hns retarget
  simpa [routeBPaperFaithfulPiPhiHeadSpanRows,
    routeBPaperFaithfulPiPhiHeadSpanTail] using
    routeBRicherSPDPStableCandidate_kernelCompatibility_of_residualInvisible
      M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanTail M n hn2 htb hns)
      obligations.residual_invisible

/-- Retarget theorem: the head-span PiPhi projection gives the finite-row
SPDP map-preimage surface for its own row family. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_spdpMapPreimage_of_retarget
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (retarget :
      RouteBPaperFaithfulPiPhiHeadSpanProjectionRetarget
        M n hn2 htb hns) :
    RouteBRicherGaugeFiniteRowsSPDPMapPreimage
      M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanRows M n hn2 htb hns) := by
  have obligations :=
    routeBPaperFaithfulPiPhiHeadSpan_obligations_of_retarget
      M n hn2 htb hns retarget
  simpa [routeBPaperFaithfulPiPhiHeadSpanRows,
    routeBPaperFaithfulPiPhiHeadSpanTail] using
    routeBRicherSPDPStableCandidate_spdpMapPreimage
      M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanTail M n hn2 htb hns)
      obligations

/-- The retargeted head-span projection fixes the coupled-sheet NP witness and
therefore supplies the fixed-embed/extraction certificate for the projected
identity-minor lower-bound route, once the source minor lower bound is supplied
for that witness. -/
noncomputable def routeBPaperFaithfulPiPhiHeadSpan_identityMinorFixedEmbedCertificate
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (routeBRicherConcreteNPWitnessQ M n hn2 htb hns)) :
    RouteBNPIdentityMinorFixedEmbedCertificate M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns) := by
  refine
    ⟨routeBRicherConcreteNPWitnessQ M n hn2 htb hns, ?_, ?_, hsource⟩
  · have hfix :=
      routeBRicherSPDPStableCandidateGauge_fixes_concreteNPRow
        M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanTail M n hn2 htb hns)
    have hrow :=
      routeBRicherSPDPStableCandidateRows_zero_eq_embed
        M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanTail M n hn2 htb hns)
    rw [hrow] at hfix
    simpa [routeBPaperFaithfulPiPhiHeadSpanGauge] using hfix
  · simpa [routeBPaperFaithfulPiPhiHeadSpanGauge,
      routeBPaperFaithfulPiPhiHeadSpanProjection,
      routeBPaperFaithfulPiPhiHeadSpanTail] using
      routeBRicherSPDPStableCandidate_extracts_compiled
        M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanTail M n hn2 htb hns)

/-- Coupled-sheet identity-minor extraction for the retargeted head-span
projection. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_projectedNPIdentityMinorLowerBound_of_source
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (routeBRicherConcreteNPWitnessQ M n hn2 htb hns)) :
    RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns) := by
  simpa [routeBPaperFaithfulPiPhiHeadSpanProjection] using
    routeBSATProjectedNPIdentityMinorLowerBound_of_fixed_embed_certificate
      M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns)
      (routeBPaperFaithfulPiPhiHeadSpan_identityMinorFixedEmbedCertificate
        M n hn2 htb hns hsource)

/-! ## Axiom audit anchors -/

#print axioms RouteBPaperFaithfulPiPhiHeadSpanProjectionRetarget
#print axioms routeBPaperFaithfulPiPhiHeadSpan_rowClosure_of_headSpanOrbitCoefficientClosure
#print axioms routeBPaperFaithfulPiPhiHeadSpanProjectionRetarget_of_headSpanOrbitCoefficientClosure_descent
#print axioms routeBPaperFaithfulPiPhiHeadSpanProjectionRetarget_of_headSpanOrbitCoefficientClosure_projectionIntertwines
#print axioms routeBPaperFaithfulPiPhiHeadSpan_holographicInvariance_of_retarget
#print axioms routeBPaperFaithfulPiPhiHeadSpan_obligations_of_retarget
#print axioms routeBPaperFaithfulPiPhiHeadSpan_kernelCompatibility_of_retarget
#print axioms routeBPaperFaithfulPiPhiHeadSpan_spdpMapPreimage_of_retarget
#print axioms routeBPaperFaithfulPiPhiHeadSpan_projectedNPIdentityMinorLowerBound_of_source

end PallLean.Paper93.Paper283
