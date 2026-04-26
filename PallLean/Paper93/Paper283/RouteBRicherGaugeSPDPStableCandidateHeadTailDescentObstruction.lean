import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailDescentKernel
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailEscapeProof

/-!
# Kernel obstruction versus projection escape for the head-span tail

This file connects the checkable chosen-kernel obstruction to the existing
log-window projection-escape witness.  The result is a concrete obstruction
surface for the canonical Route B head-span tail:

* a visible chosen-kernel generator is exactly a
  `RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness`;
* absence of that kernel obstruction is enough to recover chosen-projection
  descent.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- The checkable chosen-kernel obstruction is exactly the existing log-window
projection-escape witness for the canonical head-span tail. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailKernelObstruction_iff_logWindowProjectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelObstruction
        M n hn2 htb hns ↔
      RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
        M n hn2 htb hns := by
  constructor
  · intro hker
    have hnotDescent :
        ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
            M n hn2 htb hns :=
      (routeBRicherSPDPStableCandidate_not_logWindowHeadTailChosenProjectionDescent_iff_kernelObstruction
        M n hn2 htb hns).mpr hker
    exact
      (routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_iff_not_chosenProjectionDescent
        M n hn2 htb hns).mpr hnotDescent
  · intro hbad
    have hnotDescent :
        ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
            M n hn2 htb hns :=
      (routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_iff_not_chosenProjectionDescent
        M n hn2 htb hns).mp hbad
    exact
      (routeBRicherSPDPStableCandidate_not_logWindowHeadTailChosenProjectionDescent_iff_kernelObstruction
        M n hn2 htb hns).mp hnotDescent

/-- A visible chosen-kernel generator instantiates the log-window
projection-escape witness. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_kernelObstruction
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hker :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelObstruction
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
      M n hn2 htb hns :=
  (routeBRicherSPDPStableCandidate_headSpanTailKernelObstruction_iff_logWindowProjectionEscapeWitness
    M n hn2 htb hns).mp hker

/-- Conversely, every log-window projection escape contains a visible
chosen-kernel generator obstruction. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailKernelObstruction_of_logWindowProjectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelObstruction
      M n hn2 htb hns :=
  (routeBRicherSPDPStableCandidate_headSpanTailKernelObstruction_iff_logWindowProjectionEscapeWitness
    M n hn2 htb hns).mpr hbad

/-- The checkable kernel criterion is equivalent to absence of the existing
projection-escape witness. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailKernelCriterion_iff_no_logWindowProjectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelCriterion
        M n hn2 htb hns ↔
      ¬ RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
        M n hn2 htb hns := by
  constructor
  · intro hcriterion hbad
    have hdescent :
        RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
          M n hn2 htb hns :=
      (routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_iff_kernelCriterion
        M n hn2 htb hns).mpr hcriterion
    exact
      ((routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_iff_not_chosenProjectionDescent
        M n hn2 htb hns).mp hbad) hdescent
  · intro hno
    have hdescent :
        RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
          M n hn2 htb hns := by
      by_contra hnotDescent
      exact hno
        ((routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_iff_not_chosenProjectionDescent
          M n hn2 htb hns).mpr hnotDescent)
    exact
      (routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_iff_kernelCriterion
        M n hn2 htb hns).mp hdescent

/-- No visible chosen-kernel obstruction implies the chosen-projection descent
condition for the canonical head-span tail. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailChosenProjectionDescent_of_no_kernelObstruction
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hno :
      ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelObstruction
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
      M n hn2 htb hns :=
  (routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_iff_no_kernelObstruction
    M n hn2 htb hns).mpr hno

/-- No visible chosen-kernel obstruction is equivalent to no log-window
projection-escape witness. -/
theorem routeBRicherSPDPStableCandidate_no_headSpanTailKernelObstruction_iff_no_logWindowProjectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    (¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelObstruction
        M n hn2 htb hns) ↔
      ¬ RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
        M n hn2 htb hns := by
  constructor
  · intro hno hbad
    exact hno
      (routeBRicherSPDPStableCandidate_headSpanTailKernelObstruction_of_logWindowProjectionEscapeWitness
        M n hn2 htb hns hbad)
  · intro hno hker
    exact hno
      (routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_kernelObstruction
        M n hn2 htb hns hker)

/-! ## Axiom audit anchors -/

#print axioms routeBRicherSPDPStableCandidate_headSpanTailKernelObstruction_iff_logWindowProjectionEscapeWitness
#print axioms routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_kernelObstruction
#print axioms routeBRicherSPDPStableCandidate_headSpanTailKernelObstruction_of_logWindowProjectionEscapeWitness
#print axioms routeBRicherSPDPStableCandidate_headSpanTailKernelCriterion_iff_no_logWindowProjectionEscapeWitness
#print axioms routeBRicherSPDPStableCandidate_headSpanTailChosenProjectionDescent_of_no_kernelObstruction
#print axioms routeBRicherSPDPStableCandidate_no_headSpanTailKernelObstruction_iff_no_logWindowProjectionEscapeWitness

end PallLean.Paper93.Paper283
