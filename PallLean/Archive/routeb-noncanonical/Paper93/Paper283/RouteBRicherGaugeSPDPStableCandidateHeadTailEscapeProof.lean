import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailEscape
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailComplementProof

/-!
# Head-tail log-window escape proof bridge

This module records the exact fallback status for the canonical Route B
head-span tail.  The remaining log-window projection-escape witness is not an
independent new obligation: it is precisely failure of the chosen complement's
log-window invariance, equivalently failure of chosen-projection descent.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Any concrete log-window projection escape for the canonical head-span tail
is exactly a counterexample to log-window invariance of the chosen complement.
-/
theorem routeBRicherSPDPStableCandidate_not_logWindowChosenComplementInvariant_of_headSpanTailLogWindowProjectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns) := by
  intro hinvariant
  obtain ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm,
    hpComplement, hprojNe⟩ := hbad
  have hrowComplement :
      routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∈
        routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
          M n hn2 htb hns := by
    have hrow :=
      hinvariant spdpKappa ell p S shift
        hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm
        (by
          simpa [routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement]
            using hpComplement)
    simpa [routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement]
      using hrow
  exact hprojNe
    ((routeBRicherSPDPStableCandidateProjectionWithComplement_apply_eq_zero_iff
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
        M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement_isCompl
        M n hn2 htb hns)
      (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)).mpr
        hrowComplement)

/-- For the canonical head-span tail, the log-window projection-escape witness
is equivalent to failure of log-window chosen-complement invariance. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_iff_not_logWindowChosenComplementInvariant
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
        M n hn2 htb hns ↔
      ¬ RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
          M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail
            M n hn2 htb hns) := by
  constructor
  · exact
      routeBRicherSPDPStableCandidate_not_logWindowChosenComplementInvariant_of_headSpanTailLogWindowProjectionEscapeWitness
        M n hn2 htb hns
  · exact
      routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_not_logWindowChosenComplementInvariant
        M n hn2 htb hns

/-- Absence of the log-window projection escape is exactly the positive
log-window chosen-complement invariant. -/
theorem routeBRicherSPDPStableCandidate_no_headSpanTailLogWindowProjectionEscapeWitness_iff_logWindowChosenComplementInvariant
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    (¬ RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
        M n hn2 htb hns) ↔
      RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns) := by
  constructor
  · intro hno
    by_contra hnot
    exact hno
      (routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_not_logWindowChosenComplementInvariant
        M n hn2 htb hns hnot)
  · intro hinvariant hbad
    exact
      (routeBRicherSPDPStableCandidate_not_logWindowChosenComplementInvariant_of_headSpanTailLogWindowProjectionEscapeWitness
        M n hn2 htb hns hbad)
        hinvariant

/-- Equivalently, the missing witness is exactly failure of chosen-projection
descent for the canonical head-span tail. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_iff_not_chosenProjectionDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
        M n hn2 htb hns ↔
      ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
          M n hn2 htb hns := by
  rw [
    routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_iff_not_logWindowChosenComplementInvariant]
  exact
    not_congr
      (routeBRicherSPDPStableCandidate_logWindowChosenComplementInvariant_for_headSpanTail_iff_descent
        M n hn2 htb hns)

/-- A failure of the chosen-projection descent equation produces the requested
log-window projection-escape witness. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_not_chosenProjectionDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hnot :
      ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
          M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
      M n hn2 htb hns :=
  (routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_iff_not_chosenProjectionDescent
    M n hn2 htb hns).mpr hnot

/-- If chosen-projection descent holds, there is no log-window
projection-escape witness for the canonical head-span tail. -/
theorem routeBRicherSPDPStableCandidate_no_headSpanTailLogWindowProjectionEscapeWitness_of_chosenProjectionDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdescent :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
        M n hn2 htb hns := by
  intro hbad
  exact
    ((routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_iff_not_chosenProjectionDescent
      M n hn2 htb hns).mp hbad)
      hdescent

/-- Absence of the log-window projection escape is exactly chosen-projection
descent for the canonical head-span tail. -/
theorem routeBRicherSPDPStableCandidate_no_headSpanTailLogWindowProjectionEscapeWitness_iff_chosenProjectionDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    (¬ RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
        M n hn2 htb hns) ↔
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
        M n hn2 htb hns := by
  constructor
  · intro hno
    by_contra hnot
    exact hno
      ((routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_iff_not_chosenProjectionDescent
        M n hn2 htb hns).mpr hnot)
  · exact
      routeBRicherSPDPStableCandidate_no_headSpanTailLogWindowProjectionEscapeWitness_of_chosenProjectionDescent
        M n hn2 htb hns

/-- The existing empty-generator `mlProj` escape is a sufficient concrete
way to fail chosen-projection descent. -/
theorem routeBRicherSPDPStableCandidate_not_chosenProjectionDescent_of_headSpanTailMlProjProjectionEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateHeadSpanTailMlProjProjectionEscapeWitness
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
        M n hn2 htb hns :=
  (routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_iff_not_chosenProjectionDescent
    M n hn2 htb hns).mp
    (routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_mlProjProjectionEscape
      M n hn2 htb hns hbad)

/-- If chosen-projection descent holds, the empty-generator `mlProj` escape
cannot occur. -/
theorem routeBRicherSPDPStableCandidate_no_headSpanTailMlProjProjectionEscapeWitness_of_chosenProjectionDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdescent :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateHeadSpanTailMlProjProjectionEscapeWitness
        M n hn2 htb hns := by
  intro hbad
  exact
    (routeBRicherSPDPStableCandidate_not_chosenProjectionDescent_of_headSpanTailMlProjProjectionEscape
      M n hn2 htb hns hbad) hdescent

/-- The empty-generator kernel closure condition: every vector killed by the
chosen head-span-tail projection remains killed after applying `mlProj`. -/
def RouteBRicherSPDPStableCandidateHeadSpanTailMlProjKernelClosed
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  forall p : SATDeciderGaugeSpace M n hn2 htb hns,
    routeBRicherSPDPStableCandidateProjectionWithComplement
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
        M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement_isCompl
        M n hn2 htb hns)
      p = 0 ->
    routeBRicherSPDPStableCandidateProjectionWithComplement
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
        M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement_isCompl
        M n hn2 htb hns)
      (mlProj p) = 0

/-- Failure of empty-generator kernel closure is exactly the kernel-form
`mlProj` projection escape witness. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailKernelMlProjProjectionEscapeWitness_iff_not_mlProjKernelClosed
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateHeadSpanTailKernelMlProjProjectionEscapeWitness
        M n hn2 htb hns ↔
      ¬ RouteBRicherSPDPStableCandidateHeadSpanTailMlProjKernelClosed
          M n hn2 htb hns := by
  constructor
  · rintro ⟨p, hpZero, hmlNe⟩ hclosed
    exact hmlNe (hclosed p hpZero)
  · intro hnotClosed
    classical
    by_contra hnoWitness
    apply hnotClosed
    intro p hpZero
    by_contra hmlNe
    exact hnoWitness ⟨p, hpZero, hmlNe⟩

/-- Absence of the kernel-form empty-generator escape is equivalent to
closure of the projection kernel under `mlProj`. -/
theorem routeBRicherSPDPStableCandidate_no_headSpanTailKernelMlProjProjectionEscapeWitness_iff_mlProjKernelClosed
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    (¬ RouteBRicherSPDPStableCandidateHeadSpanTailKernelMlProjProjectionEscapeWitness
        M n hn2 htb hns) ↔
      RouteBRicherSPDPStableCandidateHeadSpanTailMlProjKernelClosed
        M n hn2 htb hns := by
  constructor
  · intro hnoEscape
    by_contra hnotClosed
    exact hnoEscape
      ((routeBRicherSPDPStableCandidate_headSpanTailKernelMlProjProjectionEscapeWitness_iff_not_mlProjKernelClosed
        M n hn2 htb hns).mpr hnotClosed)
  · intro hclosed hbad
    exact
      ((routeBRicherSPDPStableCandidate_headSpanTailKernelMlProjProjectionEscapeWitness_iff_not_mlProjKernelClosed
        M n hn2 htb hns).mp hbad) hclosed

/-- The kernel-form empty-generator `mlProj` escape is also a sufficient
concrete way to fail chosen-projection descent. -/
theorem routeBRicherSPDPStableCandidate_not_chosenProjectionDescent_of_headSpanTailKernelMlProjProjectionEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateHeadSpanTailKernelMlProjProjectionEscapeWitness
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
        M n hn2 htb hns :=
  (routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_iff_not_chosenProjectionDescent
    M n hn2 htb hns).mp
    (routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_kernelMlProjProjectionEscape
      M n hn2 htb hns hbad)

/-- If chosen-projection descent holds, the kernel-form empty-generator
`mlProj` escape cannot occur. -/
theorem routeBRicherSPDPStableCandidate_no_headSpanTailKernelMlProjProjectionEscapeWitness_of_chosenProjectionDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdescent :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateHeadSpanTailKernelMlProjProjectionEscapeWitness
        M n hn2 htb hns := by
  intro hbad
  exact
    (routeBRicherSPDPStableCandidate_not_chosenProjectionDescent_of_headSpanTailKernelMlProjProjectionEscape
      M n hn2 htb hns hbad) hdescent

/-! ## Axiom audit anchors -/

#print axioms routeBRicherSPDPStableCandidate_not_logWindowChosenComplementInvariant_of_headSpanTailLogWindowProjectionEscapeWitness
#print axioms routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_iff_not_logWindowChosenComplementInvariant
#print axioms routeBRicherSPDPStableCandidate_no_headSpanTailLogWindowProjectionEscapeWitness_iff_logWindowChosenComplementInvariant
#print axioms routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_iff_not_chosenProjectionDescent
#print axioms routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_not_chosenProjectionDescent
#print axioms routeBRicherSPDPStableCandidate_no_headSpanTailLogWindowProjectionEscapeWitness_of_chosenProjectionDescent
#print axioms routeBRicherSPDPStableCandidate_no_headSpanTailLogWindowProjectionEscapeWitness_iff_chosenProjectionDescent
#print axioms routeBRicherSPDPStableCandidate_not_chosenProjectionDescent_of_headSpanTailMlProjProjectionEscape
#print axioms routeBRicherSPDPStableCandidate_no_headSpanTailMlProjProjectionEscapeWitness_of_chosenProjectionDescent
#print axioms RouteBRicherSPDPStableCandidateHeadSpanTailMlProjKernelClosed
#print axioms routeBRicherSPDPStableCandidate_headSpanTailKernelMlProjProjectionEscapeWitness_iff_not_mlProjKernelClosed
#print axioms routeBRicherSPDPStableCandidate_no_headSpanTailKernelMlProjProjectionEscapeWitness_iff_mlProjKernelClosed
#print axioms routeBRicherSPDPStableCandidate_not_chosenProjectionDescent_of_headSpanTailKernelMlProjProjectionEscape
#print axioms routeBRicherSPDPStableCandidate_no_headSpanTailKernelMlProjProjectionEscapeWitness_of_chosenProjectionDescent

end PallLean.Paper93.Paper283
