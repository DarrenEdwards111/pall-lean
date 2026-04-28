import PallLean.Paper93.Paper283.RouteBProjectionLogWindowContainmentProgress

/-!
# PiPhi/head-span checked log-window closure frontier

This file keeps the checked log-window Route B consumer away from the false
global admissible-query window bridge.  The current algebraic frontier is:

* head-span generator-map stability, equivalently no log-window head-span
  generator escape;
* chosen projection-kernel stability, equivalently no log-window projection
  escape for the selected head-span tail complement.

Those two checked inputs are sufficient for the PiPhi/head-span log-window
map-preimage and subspace-containment consumers.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- The two stable-map inputs that close the checked PiPhi/head-span
log-window consumer. -/
def RouteBPaperFaithfulPiPhiHeadSpanCheckedStableMapInputs
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  RouteBRicherSPDPStableCandidateLogWindowHeadSpanStableGeneratorMaps
      M n hn2 htb hns ∧
    RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
      M n hn2 htb hns

/-- The exact pair of escape witnesses left by the checked PiPhi/head-span
stable-map frontier. -/
def RouteBPaperFaithfulPiPhiHeadSpanCheckedEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorMapEscapeWitness
      M n hn2 htb hns ∨
    RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
      M n hn2 htb hns

/-- Projection-kernel stability for the selected head-span tail is exactly
absence of the existing log-window projection-escape witness. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_projectionKernelStable_iff_no_logWindowProjectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
        M n hn2 htb hns ↔
      ¬ RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
        M n hn2 htb hns := by
  rw [
    routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_iff_kernelCriterion]
  exact
    routeBRicherSPDPStableCandidate_headSpanTailKernelCriterion_iff_no_logWindowProjectionEscapeWitness
      M n hn2 htb hns

/-- Head-span stable maps and projection-kernel stability are exactly absence
of the two checked escape witnesses. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_checkedStableMapInputs_iff_no_escapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBPaperFaithfulPiPhiHeadSpanCheckedStableMapInputs
        M n hn2 htb hns ↔
      ¬ RouteBPaperFaithfulPiPhiHeadSpanCheckedEscapeWitness
        M n hn2 htb hns := by
  constructor
  · rintro ⟨hhead, hkernel⟩ hbad
    rcases hbad with hbad | hbad
    · exact
        ((routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_iff_no_headSpanGeneratorMapEscape
          M n hn2 htb hns).mp hhead) hbad
    · exact
        ((routeBPaperFaithfulPiPhiHeadSpan_projectionKernelStable_iff_no_logWindowProjectionEscapeWitness
          M n hn2 htb hns).mp hkernel) hbad
  · intro hno
    refine ⟨?_, ?_⟩
    · exact
        (routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_iff_no_headSpanGeneratorMapEscape
          M n hn2 htb hns).mpr
          (fun hbad => hno (Or.inl hbad))
    · exact
        (routeBPaperFaithfulPiPhiHeadSpan_projectionKernelStable_iff_no_logWindowProjectionEscapeWitness
          M n hn2 htb hns).mpr
          (fun hbad => hno (Or.inr hbad))

/-- Stable head-span generator maps supply the orbit-coefficient closure input
for the checked PiPhi/head-span consumer. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_orbitCoefficientClosure_of_headSpanStableGeneratorMaps
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hhead :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanStableGeneratorMaps
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitCoefficientClosure
      M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_logWindowHeadSpanOrbitCoefficientClosure_of_stableGeneratorMaps
    M n hn2 htb hns hhead

/-- Absence of a head-span generator-map escape supplies the orbit-coefficient
closure input for the checked PiPhi/head-span consumer. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_orbitCoefficientClosure_of_no_headSpanGeneratorMapEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hno :
      ¬ RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorMapEscapeWitness
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadSpanOrbitCoefficientClosure
      M n hn2 htb hns :=
  routeBPaperFaithfulPiPhiHeadSpan_orbitCoefficientClosure_of_headSpanStableGeneratorMaps
    M n hn2 htb hns
    ((routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_iff_no_headSpanGeneratorMapEscape
      M n hn2 htb hns).mpr hno)

/-- Absence of a log-window projection-escape witness supplies the
projection-kernel stable-map input. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_projectionKernelStable_of_no_logWindowProjectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hno :
      ¬ RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
      M n hn2 htb hns :=
  (routeBPaperFaithfulPiPhiHeadSpan_projectionKernelStable_iff_no_logWindowProjectionEscapeWitness
    M n hn2 htb hns).mpr hno

/-- Absence of a log-window projection-escape witness supplies the chosen
projection descent input. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_projectionDescent_of_no_logWindowProjectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hno :
      ¬ RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
      M n hn2 htb hns :=
  routeBPaperFaithfulPiPhiHeadSpan_projectionDescent_of_projectionKernelStable
    M n hn2 htb hns
    (routeBPaperFaithfulPiPhiHeadSpan_projectionKernelStable_of_no_logWindowProjectionEscapeWitness
      M n hn2 htb hns hno)

/-- The checked stable-map package closes the finite-row log-window
map-preimage consumer for the PiPhi/head-span rows. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowMapPreimage_of_checkedStableMapInputs
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hinputs :
      RouteBPaperFaithfulPiPhiHeadSpanCheckedStableMapInputs
        M n hn2 htb hns) :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowMapPreimage M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanRows M n hn2 htb hns) :=
  routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowMapPreimage_of_headSpanOrbitCoefficientClosure_projectionDescent
    M n hn2 htb hns
    (routeBPaperFaithfulPiPhiHeadSpan_orbitCoefficientClosure_of_headSpanStableGeneratorMaps
      M n hn2 htb hns hinputs.1)
    (routeBPaperFaithfulPiPhiHeadSpan_projectionDescent_of_projectionKernelStable
      M n hn2 htb hns hinputs.2)

/-- Escape-free checked form of the finite-row log-window map-preimage
consumer for the PiPhi/head-span rows. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowMapPreimage_of_no_checkedEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hno :
      ¬ RouteBPaperFaithfulPiPhiHeadSpanCheckedEscapeWitness
        M n hn2 htb hns) :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowMapPreimage M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanRows M n hn2 htb hns) :=
  routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowMapPreimage_of_checkedStableMapInputs
    M n hn2 htb hns
    ((routeBPaperFaithfulPiPhiHeadSpan_checkedStableMapInputs_iff_no_escapeWitness
      M n hn2 htb hns).mpr hno)

/-- Escape-free checked form of the log-window subspace-containment consumer
for the PiPhi/head-span gauge. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowSubspaceContainment_of_no_checkedEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hno :
      ¬ RouteBPaperFaithfulPiPhiHeadSpanCheckedEscapeWitness
        M n hn2 htb hns) :
    RouteBRicherGaugeSPDPLogWindowSubspaceContainment M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns) := by
  simpa [routeBPaperFaithfulPiPhiHeadSpanGauge] using
    routeBRicherFiniteRowsCandidateGauge_spdpLogWindowSubspaceContainment_of_logWindowMapPreimage
      M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanRows M n hn2 htb hns)
      (routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowMapPreimage_of_no_checkedEscapeWitness
        M n hn2 htb hns hno)

/-! ## Axiom audit anchors -/

#print axioms RouteBPaperFaithfulPiPhiHeadSpanCheckedStableMapInputs
#print axioms RouteBPaperFaithfulPiPhiHeadSpanCheckedEscapeWitness
#print axioms routeBPaperFaithfulPiPhiHeadSpan_projectionKernelStable_iff_no_logWindowProjectionEscapeWitness
#print axioms routeBPaperFaithfulPiPhiHeadSpan_checkedStableMapInputs_iff_no_escapeWitness
#print axioms routeBPaperFaithfulPiPhiHeadSpan_orbitCoefficientClosure_of_headSpanStableGeneratorMaps
#print axioms routeBPaperFaithfulPiPhiHeadSpan_orbitCoefficientClosure_of_no_headSpanGeneratorMapEscape
#print axioms routeBPaperFaithfulPiPhiHeadSpan_projectionKernelStable_of_no_logWindowProjectionEscapeWitness
#print axioms routeBPaperFaithfulPiPhiHeadSpan_projectionDescent_of_no_logWindowProjectionEscapeWitness
#print axioms routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowMapPreimage_of_checkedStableMapInputs
#print axioms routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowMapPreimage_of_no_checkedEscapeWitness
#print axioms routeBPaperFaithfulPiPhiHeadSpan_spdpLogWindowSubspaceContainment_of_no_checkedEscapeWitness

end PallLean.Paper93.Paper283
