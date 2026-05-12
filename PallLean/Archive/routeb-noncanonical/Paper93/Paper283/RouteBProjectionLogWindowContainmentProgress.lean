import PallLean.Paper93.Paper283.RouteBProjectionPiPhiProofProgress

/-!
# PiPhi/head-span log-window containment progress

This file keeps the PiPhi/head-span SPDP containment route on the checked
log-window consumer surfaces.  It deliberately does not use the false global
`RouteBRicherSPDPStableCandidateAdmissibleQueriesLogWindowed` bridge.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- For the PiPhi/head-span rows, log-window row closure plus chosen-projection
descent gives the checked finite-row log-window map-preimage surface.

The raw preimage is the unprojected generator row `L p`.  Descent gives
`Pi (L p) = Pi (L (Pi p))`, and row closure makes `L (Pi p)` fixed by the
finite-row projection. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowMapPreimage_of_rowClosure_projectionDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (rowClosure :
      RouteBRicherGaugeFiniteRowsSPDPLogWindowRowClosure M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanRows M n hn2 htb hns))
    (descent :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
        M n hn2 htb hns) :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowMapPreimage M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanRows M n hn2 htb hns) := by
  constructor
  intro spdpKappa ell p S shift
    hSlen hshiftDegree hSlog hellLog hshiftVars hadm
  let rows := routeBPaperFaithfulPiPhiHeadSpanRows M n hn2 htb hns
  let Pi :=
    routeBNFrameCandidateAsSATGauge M n hn2 htb hns
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
  let L := routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift
  refine ⟨routeBSPDPGeneratorRow M n hn2 htb hns p S shift, ?_, ?_⟩
  · exact
      Submodule.subset_span
        ⟨S, shift, hSlen, hshiftDegree, hshiftVars, hadm, rfl⟩
  · have hdesc : Pi.comp L = (Pi.comp L).comp Pi := by
      simpa [RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent,
        routeBPaperFaithfulPiPhiHeadSpanRows,
        routeBPaperFaithfulPiPhiHeadSpanTail,
        routeBRicherSPDPStableCandidateProjection,
        routeBRicherSPDPStableCandidateGauge,
        Pi, L] using
        descent spdpKappa ell S shift hSlen hshiftDegree
          (by simpa [hSlen] using hSlog)
          (le_trans hshiftDegree hellLog)
          hshiftVars hadm
    have hdescPoint : Pi (L p) = Pi (L (Pi p)) := by
      have happ := congrArg (fun F => F p) hdesc
      simpa [LinearMap.comp_apply] using happ
    have hmem :
        L (Pi p) ∈ finiteRowsSubmodule rows := by
      simpa [L, Pi, routeBSPDPGeneratorRowLinearMap_apply] using
        routeBSPDPGeneratorRow_projected_mem_finiteRowsSubmodule_of_rowClosure
          M n hn2 htb hns rows p S shift
          (rowClosure.row_closure
            spdpKappa ell S shift
            hSlen hshiftDegree hSlog hellLog hshiftVars hadm)
    have hfixed : Pi (L (Pi p)) = L (Pi p) := by
      simpa [Pi] using
        routeBRicherFiniteRowsCandidateGauge_fixed_of_mem
          M n hn2 htb hns rows hmem
    calc
      Pi (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)
          = Pi (L p) := by
              simp [L, routeBSPDPGeneratorRowLinearMap_apply]
      _ = Pi (L (Pi p)) := hdescPoint
      _ = L (Pi p) := hfixed
      _ = routeBSPDPGeneratorRow M n hn2 htb hns (Pi p) S shift := by
              simp [L, routeBSPDPGeneratorRowLinearMap_apply]

/-- Head-span orbit coefficient closure supplies the PiPhi/head-span
log-window row closure, so projection descent closes the log-window
map-preimage consumer surface. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowMapPreimage_of_headSpanOrbitCoefficientClosure_projectionDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hclosure :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitCoefficientClosure
        M n hn2 htb hns)
    (descent :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
        M n hn2 htb hns) :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowMapPreimage M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanRows M n hn2 htb hns) :=
  routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowMapPreimage_of_rowClosure_projectionDescent
    M n hn2 htb hns
    (routeBPaperFaithfulPiPhiHeadSpan_rowClosure_of_headSpanOrbitCoefficientClosure
      M n hn2 htb hns hclosure)
    descent

/-- The corresponding checked log-window subspace-containment surface for the
PiPhi/head-span gauge. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowSubspaceContainment_of_headSpanOrbitCoefficientClosure_projectionDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hclosure :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitCoefficientClosure
        M n hn2 htb hns)
    (descent :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
        M n hn2 htb hns) :
    RouteBRicherGaugeSPDPLogWindowSubspaceContainment M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns) := by
  simpa [routeBPaperFaithfulPiPhiHeadSpanGauge] using
    routeBRicherFiniteRowsCandidateGauge_spdpLogWindowSubspaceContainment_of_logWindowMapPreimage
      M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanRows M n hn2 htb hns)
      (routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowMapPreimage_of_headSpanOrbitCoefficientClosure_projectionDescent
        M n hn2 htb hns hclosure descent)

/-- Constructor from the already named PiPhi progress frontiers: second-pass
head-span closure and chosen-kernel stability close the checked log-window
map-preimage surface. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowMapPreimage_of_secondPass_projectionKernelStable
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hsecond :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorSecondPassClosure
        M n hn2 htb hns)
    (hstable :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
        M n hn2 htb hns) :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowMapPreimage M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanRows M n hn2 htb hns) :=
  routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowMapPreimage_of_headSpanOrbitCoefficientClosure_projectionDescent
    M n hn2 htb hns
    (routeBPaperFaithfulPiPhiHeadSpan_orbitCoefficientClosure_of_secondPassClosure
      M n hn2 htb hns hsecond)
    (routeBPaperFaithfulPiPhiHeadSpan_projectionDescent_of_projectionKernelStable
      M n hn2 htb hns hstable)

/-- Constructor from the already named PiPhi progress frontiers for the
checked log-window subspace-containment surface. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowSubspaceContainment_of_secondPass_projectionKernelStable
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hsecond :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorSecondPassClosure
        M n hn2 htb hns)
    (hstable :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
        M n hn2 htb hns) :
    RouteBRicherGaugeSPDPLogWindowSubspaceContainment M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns) :=
  routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowSubspaceContainment_of_headSpanOrbitCoefficientClosure_projectionDescent
    M n hn2 htb hns
    (routeBPaperFaithfulPiPhiHeadSpan_orbitCoefficientClosure_of_secondPassClosure
      M n hn2 htb hns hsecond)
    (routeBPaperFaithfulPiPhiHeadSpan_projectionDescent_of_projectionKernelStable
      M n hn2 htb hns hstable)

/-- Alternative preimage-route constructor: if the descent/kernel route is not
used, the exact remaining SPDP-side obligation is the log-window
unprojected-preimage statement for the PiPhi/head-span row family. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowMapPreimage_of_headSpanOrbitCoefficientClosure_unprojectedPreimage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hclosure :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitCoefficientClosure
        M n hn2 htb hns)
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPLogWindowUnprojectedPreimage
        M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanRows M n hn2 htb hns)) :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowMapPreimage M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanRows M n hn2 htb hns) :=
  routeBRicherGaugeFiniteRowsSPDPLogWindowMapPreimage_of_rowClosure_unprojectedPreimage
    M n hn2 htb hns
    (routeBPaperFaithfulPiPhiHeadSpanRows M n hn2 htb hns)
    (routeBPaperFaithfulPiPhiHeadSpan_rowClosure_of_headSpanOrbitCoefficientClosure
      M n hn2 htb hns hclosure)
    preimage

/-! ## Axiom audit anchors -/

#print axioms routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowMapPreimage_of_rowClosure_projectionDescent
#print axioms routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowMapPreimage_of_headSpanOrbitCoefficientClosure_projectionDescent
#print axioms routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowSubspaceContainment_of_headSpanOrbitCoefficientClosure_projectionDescent
#print axioms routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowMapPreimage_of_secondPass_projectionKernelStable
#print axioms routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowSubspaceContainment_of_secondPass_projectionKernelStable
#print axioms routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowMapPreimage_of_headSpanOrbitCoefficientClosure_unprojectedPreimage

end PallLean.Paper93.Paper283
