import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadCover
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateComplement

/-!
# Complement-escape route for the head-span Route B tail

This file specializes the explicit-complement projection-escape no-go API to
the narrow log-window head-span tail.  It does not prove a concrete escaping
polynomial.  Instead it records the exact witness predicate left to exhibit:
a complement vector whose admissible generator row has nonzero projection
along the chosen finite-row complement.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- The finite projection's chosen complement for the narrow log-window
head-span tail. -/
noncomputable abbrev routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidateProjectionComplement M n hn2 htb hns
    (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)

/-- The chosen complement is complementary to the selected head-span row
submodule. -/
theorem routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement_isCompl
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    IsCompl
      (finiteRowsSubmodule
        (routeBRicherSPDPStableCandidateRows M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail
            M n hn2 htb hns)))
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
        M n hn2 htb hns) := by
  simpa [routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement,
    routeBRicherSPDPStableCandidateProjectionComplement] using
    (finiteSubmoduleProjection_isCompl
      (finiteRowsSubmodule
        (routeBRicherSPDPStableCandidateRows M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail
            M n hn2 htb hns))))

/-- The canonical head-span tail's chosen complement, repackaged as the
generic explicit-complement interface. -/
noncomputable def routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplementInterface
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateProjectionComplementInterface
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns) where
  complement :=
    routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
      M n hn2 htb hns
  isCompl :=
    routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement_isCompl
      M n hn2 htb hns

/-- Projection-escape witness specialized to the head-span tail and the finite
projection's chosen complement.  This is the exact remaining exhibit needed by
the explicit-complement no-go wrappers. -/
def RouteBRicherSPDPStableCandidateHeadSpanTailProjectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  exists (spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ∧
    shift.totalDegree <= ell ∧
    shift.vars <= S.toFinset ∧
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ∧
    p ∈ routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
      M n hn2 htb hns ∧
    routeBRicherSPDPStableCandidateProjectionWithComplement
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
        M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement_isCompl
        M n hn2 htb hns)
      (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) ≠ 0

/-- Log-window variant of the same projection-escape witness. -/
def RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  exists (spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ∧
    shift.totalDegree <= ell ∧
    S.length <= Nat.log 2 n ∧
    shift.totalDegree <= Nat.log 2 n ∧
    shift.vars <= S.toFinset ∧
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ∧
    p ∈ routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
      M n hn2 htb hns ∧
    routeBRicherSPDPStableCandidateProjectionWithComplement
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
        M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement_isCompl
        M n hn2 htb hns)
      (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) ≠ 0

/-- A log-window escape is an unrestricted projection escape after forgetting
the window bounds. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailProjectionEscapeWitness_of_logWindow
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHeadSpanTailProjectionEscapeWitness
      M n hn2 htb hns := by
  obtain ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, _hSlog, _hshiftLog, hshiftVars, hadm,
    hpComplement, hprojNe⟩ := hbad
  exact ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hshiftVars, hadm, hpComplement, hprojNe⟩

/-- Failure of full chosen-complement invariance for the head-span tail
produces the exact projection-escape witness consumed by the explicit
with-complement no-go wrappers. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailProjectionEscapeWitness_of_not_chosenComplementInvariant
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hnot :
      ¬ RouteBRicherSPDPStableCandidateChosenComplementInvariant
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)) :
    RouteBRicherSPDPStableCandidateHeadSpanTailProjectionEscapeWitness
      M n hn2 htb hns := by
  classical
  by_contra hno
  apply hnot
  intro spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm hpComplement
  by_contra hrowNotComplement
  apply hno
  refine ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hshiftVars, hadm, ?_, ?_⟩
  · simpa [routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement] using
      hpComplement
  · intro hprojZero
    have hrowComplement :
        routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∈
          routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
            M n hn2 htb hns :=
      (routeBRicherSPDPStableCandidateProjectionWithComplement_apply_eq_zero_iff
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)
        (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
          M n hn2 htb hns)
        (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement_isCompl
          M n hn2 htb hns)
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)).mp hprojZero
    exact hrowNotComplement
      (by
        simpa [routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement]
          using hrowComplement)

/-- Failure of log-window chosen-complement invariance for the head-span tail
produces a log-window projection-escape witness. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_not_logWindowChosenComplementInvariant
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hnot :
      ¬ RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)) :
    RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
      M n hn2 htb hns := by
  classical
  by_contra hno
  apply hnot
  intro spdpKappa ell p S shift
    hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm hpComplement
  by_contra hrowNotComplement
  apply hno
  refine ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm, ?_, ?_⟩
  · simpa [routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement] using
      hpComplement
  · intro hprojZero
    have hrowComplement :
        routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∈
          routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
            M n hn2 htb hns :=
      (routeBRicherSPDPStableCandidateProjectionWithComplement_apply_eq_zero_iff
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)
        (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
          M n hn2 htb hns)
        (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement_isCompl
          M n hn2 htb hns)
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)).mp hprojZero
    exact hrowNotComplement
      (by
        simpa [routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement]
          using hrowComplement)

/-- Head-span-tail specialization of the explicit-complement no-go wrapper. -/
theorem routeBRicherSPDPStableCandidate_headSpanTail_explicitComplementInvariant_noGo_of_projectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateHeadSpanTailProjectionEscapeWitness
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateExplicitComplementInvariant
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)
        (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
          M n hn2 htb hns) := by
  exact
    routeBRicherSPDPStableCandidate_explicitComplementInvariant_noGo_of_projectionWithComplement_escape
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
        M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement_isCompl
        M n hn2 htb hns)
      hbad

/-- Head-span-tail specialization of the explicit-complement kernel no-go
wrapper. -/
theorem routeBRicherSPDPStableCandidate_headSpanTail_kernelGeneratorInvisibleWithComplement_noGo_of_projectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateHeadSpanTailProjectionEscapeWitness
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateKernelGeneratorInvisibleWithComplement
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)
        (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
          M n hn2 htb hns)
        (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement_isCompl
          M n hn2 htb hns) := by
  exact
    routeBRicherSPDPStableCandidate_kernelGeneratorInvisibleWithComplement_noGo_of_projectionWithComplement_escape
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
        M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement_isCompl
        M n hn2 htb hns)
      hbad

/-- If the head-span tail's chosen complement is not invariant, the
specialized explicit-complement invariant is refuted through a projection
escape witness. -/
theorem routeBRicherSPDPStableCandidate_headSpanTail_explicitComplementInvariant_noGo_of_not_chosenComplementInvariant
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hnot :
      ¬ RouteBRicherSPDPStableCandidateChosenComplementInvariant
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)) :
    ¬ RouteBRicherSPDPStableCandidateExplicitComplementInvariant
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)
        (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
          M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_headSpanTail_explicitComplementInvariant_noGo_of_projectionEscapeWitness
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headSpanTailProjectionEscapeWitness_of_not_chosenComplementInvariant
      M n hn2 htb hns hnot)

/-- Log-window complement-invariance failure also refutes the specialized
explicit-complement invariant, by first producing the log-window escape
witness and then forgetting the window bounds. -/
theorem routeBRicherSPDPStableCandidate_headSpanTail_explicitComplementInvariant_noGo_of_not_logWindowChosenComplementInvariant
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hnot :
      ¬ RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)) :
    ¬ RouteBRicherSPDPStableCandidateExplicitComplementInvariant
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)
        (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
          M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_headSpanTail_explicitComplementInvariant_noGo_of_projectionEscapeWitness
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headSpanTailProjectionEscapeWitness_of_logWindow
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_not_logWindowChosenComplementInvariant
        M n hn2 htb hns hnot))

/-! ## Axiom audit anchors -/

#print axioms routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement_isCompl
#print axioms routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplementInterface
#print axioms RouteBRicherSPDPStableCandidateHeadSpanTailProjectionEscapeWitness
#print axioms RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
#print axioms routeBRicherSPDPStableCandidate_headSpanTailProjectionEscapeWitness_of_not_chosenComplementInvariant
#print axioms routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_not_logWindowChosenComplementInvariant
#print axioms routeBRicherSPDPStableCandidate_headSpanTail_explicitComplementInvariant_noGo_of_projectionEscapeWitness
#print axioms routeBRicherSPDPStableCandidate_headSpanTail_kernelGeneratorInvisibleWithComplement_noGo_of_projectionEscapeWitness
#print axioms routeBRicherSPDPStableCandidate_headSpanTail_explicitComplementInvariant_noGo_of_not_chosenComplementInvariant
#print axioms routeBRicherSPDPStableCandidate_headSpanTail_explicitComplementInvariant_noGo_of_not_logWindowChosenComplementInvariant

end PallLean.Paper93.Paper283
