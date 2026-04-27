import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailDescentObstruction

/-!
# Coordinate escape witnesses for the head-span tail

The selected complement for the head-span tail is still the arbitrary
`Classical.choose` complement behind `finiteSubmoduleProjectionComplement`.
This file therefore does not claim a closed-form basis vector.  Instead it
pushes the negative branch down to a concrete coordinate check: a single
monomial coefficient of the projected generator row is nonzero.

The first predicate is equivalent to the existing log-window projection escape.
The second is the empty-generator `mlProj` specialization, matching the
smallest obstruction exposed in `HeadTailEscape.lean`.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- A polynomial is nonzero iff one of its monomial coefficients is nonzero. -/
theorem mvPolynomial_ne_zero_iff_exists_coeff_ne_zero
    {N : Nat} (p : MvPolynomial (Fin N) Rat) :
    p ≠ 0 ↔
      ∃ μ : Fin N →₀ Nat, MvPolynomial.coeff μ p ≠ 0 := by
  constructor
  · intro hp
    classical
    by_contra hno
    apply hp
    apply MvPolynomial.ext
    intro μ
    have hcoeff : MvPolynomial.coeff μ p = 0 := by
      by_contra hne
      exact hno ⟨μ, hne⟩
    simpa using hcoeff
  · rintro ⟨μ, hμ⟩ hp
    exact hμ (by simp [hp])

/-- Coordinate form of the head-span-tail kernel obstruction.

Instead of only asking that the projected generator row be nonzero, this records
an explicit monomial coordinate `μ` where it is visible. -/
def RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  exists (spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns)
    (μ : Fin (RouteBCookLevinDim M n hn2 htb hns) →₀ Nat),
    S.length = spdpKappa ∧
    shift.totalDegree <= ell ∧
    S.length <= Nat.log 2 n ∧
    shift.totalDegree <= Nat.log 2 n ∧
    shift.vars <= S.toFinset ∧
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ∧
    routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
        p = 0 ∧
    MvPolynomial.coeff μ
      (routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)) ≠ 0

/-- Constructor form for the general visible coefficient obstruction.  This is
the exact named interface for turning an explicit kernel vector, admissible
generator row, and nonzero projected monomial coefficient into the Route B
escape branch. -/
theorem routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_of_explicitCoeff
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns)
    (μ : Fin (RouteBCookLevinDim M n hn2 htb hns) →₀ Nat)
    (hSlen : S.length = spdpKappa)
    (hshiftDegree : shift.totalDegree <= ell)
    (hSlog : S.length <= Nat.log 2 n)
    (hshiftLog : shift.totalDegree <= Nat.log 2 n)
    (hshiftVars : shift.vars <= S.toFinset)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition S)
    (hpZero :
      routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
          p = 0)
    (hcoeff :
      MvPolynomial.coeff μ
        (routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
          (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)) ≠ 0) :
    RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
      M n hn2 htb hns :=
  ⟨spdpKappa, ell, p, S, shift, μ, hSlen, hshiftDegree, hSlog,
    hshiftLog, hshiftVars, hadm, hpZero, hcoeff⟩

/-- A visible monomial coefficient gives the existing kernel obstruction. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailKernelObstruction_of_visibleCoefficientEscapeObstruction
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hcoord :
      RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelObstruction
      M n hn2 htb hns := by
  rcases hcoord with ⟨spdpKappa, ell, p, S, shift, μ,
    hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm,
    hpZero, hcoeff⟩
  refine ⟨spdpKappa, ell, p, S, shift, hSlen, hshiftDegree,
    hSlog, hshiftLog, hshiftVars, hadm, hpZero, ?_⟩
  intro hrowZero
  exact hcoeff (by simp [hrowZero])

/-- Every kernel obstruction has a visible monomial coefficient. -/
theorem routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_of_headSpanTailKernelObstruction
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hker :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelObstruction
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
      M n hn2 htb hns := by
  rcases hker with ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm,
    hpZero, hvisible⟩
  obtain ⟨μ, hcoeff⟩ :=
    (mvPolynomial_ne_zero_iff_exists_coeff_ne_zero
      (routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift))).mp hvisible
  exact ⟨spdpKappa, ell, p, S, shift, μ, hSlen, hshiftDegree,
    hSlog, hshiftLog, hshiftVars, hadm, hpZero, hcoeff⟩

/-- Coordinate obstruction and chosen-kernel obstruction are the same target. -/
theorem routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_iff_kernelObstruction
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
        M n hn2 htb hns ↔
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelObstruction
        M n hn2 htb hns :=
  ⟨routeBRicherSPDPStableCandidate_headSpanTailKernelObstruction_of_visibleCoefficientEscapeObstruction
      M n hn2 htb hns,
    routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_of_headSpanTailKernelObstruction
      M n hn2 htb hns⟩

/-- A coordinate obstruction instantiates the requested log-window projection
escape witness. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_visibleCoefficientEscapeObstruction
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hcoord :
      RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
      M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_kernelObstruction
    M n hn2 htb hns
    ((routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_iff_kernelObstruction
      M n hn2 htb hns).mp hcoord)

/-- Conversely, any log-window projection escape contains a visible monomial
coordinate after applying the selected projection. -/
theorem routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_of_headSpanTailLogWindowProjectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
      M n hn2 htb hns :=
  (routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_iff_kernelObstruction
    M n hn2 htb hns).mpr
    (routeBRicherSPDPStableCandidate_headSpanTailKernelObstruction_of_logWindowProjectionEscapeWitness
      M n hn2 htb hns hbad)

/-- The coefficient obstruction is equivalent to the existing log-window
projection escape. -/
theorem routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_iff_logWindowProjectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
        M n hn2 htb hns ↔
      RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
        M n hn2 htb hns :=
  ⟨routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_visibleCoefficientEscapeObstruction
      M n hn2 htb hns,
    routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_of_headSpanTailLogWindowProjectionEscapeWitness
      M n hn2 htb hns⟩

/-- Failure of the chosen-projection descent equation already contains a
visible monomial coefficient of the escaped projected generator row. -/
theorem routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_of_not_chosenProjectionDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hnot :
      ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
          M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
      M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_of_headSpanTailLogWindowProjectionEscapeWitness
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_not_chosenProjectionDescent
      M n hn2 htb hns hnot)

/-- The coefficient escape branch is exactly failure of chosen-projection
descent for the canonical head-span tail. -/
theorem routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_iff_not_chosenProjectionDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
        M n hn2 htb hns ↔
      ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
          M n hn2 htb hns := by
  rw [
    routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_iff_logWindowProjectionEscapeWitness,
    routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_iff_not_chosenProjectionDescent]

/-- Failure of the chosen log-window complement invariant contains a visible
monomial coefficient of the escaped projected generator row. -/
theorem routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_of_not_logWindowChosenComplementInvariant
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hnot :
      ¬ RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
          M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail
            M n hn2 htb hns)) :
    RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
      M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_of_headSpanTailLogWindowProjectionEscapeWitness
    M n hn2 htb hns
    ((routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_iff_not_logWindowChosenComplementInvariant
      M n hn2 htb hns).mpr hnot)

/-- The coefficient escape branch is exactly failure of the chosen log-window
complement invariant for the canonical head-span tail. -/
theorem routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_iff_not_logWindowChosenComplementInvariant
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
        M n hn2 htb hns ↔
      ¬ RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
          M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail
            M n hn2 htb hns) := by
  rw [
    routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_iff_logWindowProjectionEscapeWitness,
    routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_iff_not_logWindowChosenComplementInvariant]

/-- Empty-generator coordinate form: a vector in the chosen projection kernel
whose `mlProj` has a visible projected monomial coefficient. -/
def RouteBRicherSPDPStableCandidateHeadSpanTailMlProjVisibleCoefficientEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  exists (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (μ : Fin (RouteBCookLevinDim M n hn2 htb hns) →₀ Nat),
    routeBRicherSPDPStableCandidateProjectionWithComplement
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
        M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement_isCompl
        M n hn2 htb hns)
      p = 0 ∧
    MvPolynomial.coeff μ
      (routeBRicherSPDPStableCandidateProjectionWithComplement
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
        (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
          M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement_isCompl
        M n hn2 htb hns)
      (mlProj p)) ≠ 0

/-- Constructor form for the empty-generator coordinate obstruction.  This is
the exact place where an explicit kernel vector and monomial coefficient would
instantiate the `mlProj` escape branch for the chosen head-span-tail
projection. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailMlProjVisibleCoefficientEscapeWitness_of_explicitCoeff
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (μ : Fin (RouteBCookLevinDim M n hn2 htb hns) →₀ Nat)
    (hpZero :
      routeBRicherSPDPStableCandidateProjectionWithComplement
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
        (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
          M n hn2 htb hns)
        (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement_isCompl
          M n hn2 htb hns)
        p = 0)
    (hcoeff :
      MvPolynomial.coeff μ
        (routeBRicherSPDPStableCandidateProjectionWithComplement
          M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
          (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
            M n hn2 htb hns)
          (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement_isCompl
            M n hn2 htb hns)
          (mlProj p)) ≠ 0) :
    RouteBRicherSPDPStableCandidateHeadSpanTailMlProjVisibleCoefficientEscapeWitness
      M n hn2 htb hns :=
  ⟨p, μ, hpZero, hcoeff⟩

/-- A visible `mlProj` coefficient is the existing kernel-form empty-generator
escape. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailKernelMlProjProjectionEscape_of_mlProjVisibleCoefficientEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hcoord :
      RouteBRicherSPDPStableCandidateHeadSpanTailMlProjVisibleCoefficientEscapeWitness
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHeadSpanTailKernelMlProjProjectionEscapeWitness
      M n hn2 htb hns := by
  rcases hcoord with ⟨p, μ, hpZero, hcoeff⟩
  exact ⟨p, hpZero, fun hmlZero => hcoeff (by simp [hmlZero])⟩

/-- Every kernel-form empty-generator escape has a visible monomial
coordinate. -/
theorem routeBRicherSPDPStableCandidate_mlProjVisibleCoefficientEscape_of_headSpanTailKernelMlProjProjectionEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateHeadSpanTailKernelMlProjProjectionEscapeWitness
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHeadSpanTailMlProjVisibleCoefficientEscapeWitness
      M n hn2 htb hns := by
  rcases hbad with ⟨p, hpZero, hmlVisible⟩
  obtain ⟨μ, hcoeff⟩ :=
    (mvPolynomial_ne_zero_iff_exists_coeff_ne_zero
      (routeBRicherSPDPStableCandidateProjectionWithComplement
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
        (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
          M n hn2 htb hns)
        (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement_isCompl
          M n hn2 htb hns)
        (mlProj p))).mp hmlVisible
  exact ⟨p, μ, hpZero, hcoeff⟩

/-- The empty-generator coordinate obstruction is equivalent to the existing
kernel-form `mlProj` escape predicate. -/
theorem routeBRicherSPDPStableCandidate_mlProjVisibleCoefficientEscape_iff_kernelMlProjProjectionEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateHeadSpanTailMlProjVisibleCoefficientEscapeWitness
        M n hn2 htb hns ↔
      RouteBRicherSPDPStableCandidateHeadSpanTailKernelMlProjProjectionEscapeWitness
        M n hn2 htb hns :=
  ⟨routeBRicherSPDPStableCandidate_headSpanTailKernelMlProjProjectionEscape_of_mlProjVisibleCoefficientEscape
      M n hn2 htb hns,
    routeBRicherSPDPStableCandidate_mlProjVisibleCoefficientEscape_of_headSpanTailKernelMlProjProjectionEscape
      M n hn2 htb hns⟩

/-- Failure of empty-generator `mlProj` kernel closure already contains a
visible monomial coefficient after the selected projection. -/
theorem routeBRicherSPDPStableCandidate_mlProjVisibleCoefficientEscape_of_not_mlProjKernelClosed
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hnot :
      ¬ RouteBRicherSPDPStableCandidateHeadSpanTailMlProjKernelClosed
          M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHeadSpanTailMlProjVisibleCoefficientEscapeWitness
      M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_mlProjVisibleCoefficientEscape_of_headSpanTailKernelMlProjProjectionEscape
    M n hn2 htb hns
    ((routeBRicherSPDPStableCandidate_headSpanTailKernelMlProjProjectionEscapeWitness_iff_not_mlProjKernelClosed
      M n hn2 htb hns).mpr hnot)

/-- The empty-generator coefficient escape is exactly failure of kernel closure
under `mlProj` for the chosen head-span-tail projection. -/
theorem routeBRicherSPDPStableCandidate_mlProjVisibleCoefficientEscape_iff_not_mlProjKernelClosed
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateHeadSpanTailMlProjVisibleCoefficientEscapeWitness
        M n hn2 htb hns ↔
      ¬ RouteBRicherSPDPStableCandidateHeadSpanTailMlProjKernelClosed
          M n hn2 htb hns := by
  rw [
    routeBRicherSPDPStableCandidate_mlProjVisibleCoefficientEscape_iff_kernelMlProjProjectionEscape,
    routeBRicherSPDPStableCandidate_headSpanTailKernelMlProjProjectionEscapeWitness_iff_not_mlProjKernelClosed]

/-- A visible `mlProj` coordinate instantiates the requested log-window
projection-escape witness. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_mlProjVisibleCoefficientEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hcoord :
      RouteBRicherSPDPStableCandidateHeadSpanTailMlProjVisibleCoefficientEscapeWitness
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
      M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_kernelMlProjProjectionEscape
    M n hn2 htb hns
    ((routeBRicherSPDPStableCandidate_mlProjVisibleCoefficientEscape_iff_kernelMlProjProjectionEscape
      M n hn2 htb hns).mp hcoord)

/-! ## Caller-supplied complement coefficient witnesses -/

/-- Coordinate escape witness for the canonical head-span tail, but with a
caller-supplied projection complement rather than the legacy chosen complement.

The witness is deliberately stated against the bundled explicit-complement
interface: an inspectable complement `I.complement`, a kernel vector `p`, an
admissible generator row, and a visible monomial coefficient after `I.projection`.
-/
def RouteBRicherSPDPStableCandidateHeadSpanTailExplicitComplementVisibleCoefficientEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)) : Prop :=
  exists (spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns)
    (μ : Fin (RouteBCookLevinDim M n hn2 htb hns) →₀ Nat),
    S.length = spdpKappa ∧
    shift.totalDegree <= ell ∧
    S.length <= Nat.log 2 n ∧
    shift.totalDegree <= Nat.log 2 n ∧
    shift.vars <= S.toFinset ∧
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ∧
    I.projection p = 0 ∧
    MvPolynomial.coeff μ
      (I.projection
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)) ≠ 0

/-- Constructor for the caller-supplied-complement coordinate escape surface. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailExplicitComplementVisibleCoefficientEscapeWitness_of_explicitCoeff
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns))
    (spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns)
    (μ : Fin (RouteBCookLevinDim M n hn2 htb hns) →₀ Nat)
    (hSlen : S.length = spdpKappa)
    (hshiftDegree : shift.totalDegree <= ell)
    (hSlog : S.length <= Nat.log 2 n)
    (hshiftLog : shift.totalDegree <= Nat.log 2 n)
    (hshiftVars : shift.vars <= S.toFinset)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition S)
    (hpZero : I.projection p = 0)
    (hcoeff :
      MvPolynomial.coeff μ
        (I.projection
          (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)) ≠ 0) :
    RouteBRicherSPDPStableCandidateHeadSpanTailExplicitComplementVisibleCoefficientEscapeWitness
      M n hn2 htb hns I :=
  ⟨spdpKappa, ell, p, S, shift, μ, hSlen, hshiftDegree, hSlog,
    hshiftLog, hshiftVars, hadm, hpZero, hcoeff⟩

/-- A visible coefficient for a caller-supplied complement gives the existing
projection-with-complement escape shape, with log-window bounds forgotten. -/
theorem routeBRicherSPDPStableCandidate_projectionWithComplement_escape_of_headSpanTailExplicitComplementVisibleCoefficientEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns))
    (hcoord :
      RouteBRicherSPDPStableCandidateHeadSpanTailExplicitComplementVisibleCoefficientEscapeWitness
        M n hn2 htb hns I) :
    exists (spdpKappa ell : Nat)
      (p : SATDeciderGaugeSpace M n hn2 htb hns)
      (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
      (shift : SATDeciderGaugeSpace M n hn2 htb hns),
      S.length = spdpKappa ∧
      shift.totalDegree <= ell ∧
      shift.vars <= S.toFinset ∧
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition S ∧
      p ∈ I.complement ∧
      routeBRicherSPDPStableCandidateProjectionWithComplement
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
        I.complement I.isCompl
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) ≠ 0 := by
  rcases hcoord with ⟨spdpKappa, ell, p, S, shift, μ,
    hSlen, hshiftDegree, _hSlog, _hshiftLog, hshiftVars, hadm,
    hpZero, hcoeff⟩
  refine ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hshiftVars, hadm, ?_, ?_⟩
  · exact (I.projection_apply_eq_zero_iff p).mp hpZero
  · intro hprojZero
    exact hcoeff (by simp [RouteBRicherSPDPStableCandidateProjectionComplementInterface.projection,
      hprojZero])

/-- A caller-supplied-complement visible coefficient refutes invariance of that
same inspectable complement. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailExplicitComplementInvariant_noGo_of_visibleCoefficientEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns))
    (hcoord :
      RouteBRicherSPDPStableCandidateHeadSpanTailExplicitComplementVisibleCoefficientEscapeWitness
        M n hn2 htb hns I) :
    ¬ RouteBRicherSPDPStableCandidateExplicitComplementInvariant
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)
        I.complement :=
  routeBRicherSPDPStableCandidate_explicitComplementInvariant_noGo_of_projectionWithComplement_escape
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidateLogWindowHeadTail
      M n hn2 htb hns)
    I.complement I.isCompl
    (routeBRicherSPDPStableCandidate_projectionWithComplement_escape_of_headSpanTailExplicitComplementVisibleCoefficientEscape
      M n hn2 htb hns I hcoord)

/-- Empty-generator `mlProj` coefficient witness for a caller-supplied
head-span-tail complement. -/
def RouteBRicherSPDPStableCandidateHeadSpanTailExplicitComplementMlProjVisibleCoefficientEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)) : Prop :=
  exists (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (μ : Fin (RouteBCookLevinDim M n hn2 htb hns) →₀ Nat),
    I.projection p = 0 ∧
    MvPolynomial.coeff μ (I.projection (mlProj p)) ≠ 0

/-- Constructor for the empty-generator caller-supplied-complement coefficient
witness. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailExplicitComplementMlProjVisibleCoefficientEscapeWitness_of_explicitCoeff
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns))
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (μ : Fin (RouteBCookLevinDim M n hn2 htb hns) →₀ Nat)
    (hpZero : I.projection p = 0)
    (hcoeff : MvPolynomial.coeff μ (I.projection (mlProj p)) ≠ 0) :
    RouteBRicherSPDPStableCandidateHeadSpanTailExplicitComplementMlProjVisibleCoefficientEscapeWitness
      M n hn2 htb hns I :=
  ⟨p, μ, hpZero, hcoeff⟩

/-- The empty-generator caller-supplied coefficient witness instantiates the
general caller-supplied coefficient witness. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailExplicitComplementVisibleCoefficientEscape_of_mlProjVisibleCoefficientEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns))
    (hcoord :
      RouteBRicherSPDPStableCandidateHeadSpanTailExplicitComplementMlProjVisibleCoefficientEscapeWitness
        M n hn2 htb hns I) :
    RouteBRicherSPDPStableCandidateHeadSpanTailExplicitComplementVisibleCoefficientEscapeWitness
      M n hn2 htb hns I := by
  rcases hcoord with ⟨p, μ, hpZero, hcoeff⟩
  refine ⟨0, 0, p,
    ([] : List (Fin (RouteBCookLevinDim M n hn2 htb hns))),
    (1 : SATDeciderGaugeSpace M n hn2 htb hns), μ,
    by simp,
    by simp [MvPolynomial.totalDegree_one],
    by simp,
    by simp [MvPolynomial.totalDegree_one],
    by simp [MvPolynomial.vars_one],
    ?_,
    hpZero,
    ?_⟩
  · constructor
    · simp
    · intro b
      simp
  · simpa [routeBSPDPGeneratorRow, SPDP.iterDerivList, mlProj_one] using hcoeff

/-- Empty-generator caller-supplied coefficient escape refutes invariance of
the same inspectable complement. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailExplicitComplementInvariant_noGo_of_mlProjVisibleCoefficientEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns))
    (hcoord :
      RouteBRicherSPDPStableCandidateHeadSpanTailExplicitComplementMlProjVisibleCoefficientEscapeWitness
        M n hn2 htb hns I) :
    ¬ RouteBRicherSPDPStableCandidateExplicitComplementInvariant
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)
        I.complement :=
  routeBRicherSPDPStableCandidate_headSpanTailExplicitComplementInvariant_noGo_of_visibleCoefficientEscape
    M n hn2 htb hns I
    (routeBRicherSPDPStableCandidate_headSpanTailExplicitComplementVisibleCoefficientEscape_of_mlProjVisibleCoefficientEscape
      M n hn2 htb hns I hcoord)

/-! ## Axiom audit anchors -/

#print axioms mvPolynomial_ne_zero_iff_exists_coeff_ne_zero
#print axioms RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
#print axioms routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_of_explicitCoeff
#print axioms routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_iff_logWindowProjectionEscapeWitness
#print axioms routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_iff_not_chosenProjectionDescent
#print axioms routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_iff_not_logWindowChosenComplementInvariant
#print axioms RouteBRicherSPDPStableCandidateHeadSpanTailMlProjVisibleCoefficientEscapeWitness
#print axioms routeBRicherSPDPStableCandidate_headSpanTailMlProjVisibleCoefficientEscapeWitness_of_explicitCoeff
#print axioms routeBRicherSPDPStableCandidate_mlProjVisibleCoefficientEscape_iff_kernelMlProjProjectionEscape
#print axioms routeBRicherSPDPStableCandidate_mlProjVisibleCoefficientEscape_iff_not_mlProjKernelClosed
#print axioms routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_mlProjVisibleCoefficientEscape
#print axioms RouteBRicherSPDPStableCandidateHeadSpanTailExplicitComplementVisibleCoefficientEscapeWitness
#print axioms routeBRicherSPDPStableCandidate_headSpanTailExplicitComplementVisibleCoefficientEscapeWitness_of_explicitCoeff
#print axioms routeBRicherSPDPStableCandidate_projectionWithComplement_escape_of_headSpanTailExplicitComplementVisibleCoefficientEscape
#print axioms routeBRicherSPDPStableCandidate_headSpanTailExplicitComplementInvariant_noGo_of_visibleCoefficientEscape
#print axioms RouteBRicherSPDPStableCandidateHeadSpanTailExplicitComplementMlProjVisibleCoefficientEscapeWitness
#print axioms routeBRicherSPDPStableCandidate_headSpanTailExplicitComplementMlProjVisibleCoefficientEscapeWitness_of_explicitCoeff
#print axioms routeBRicherSPDPStableCandidate_headSpanTailExplicitComplementVisibleCoefficientEscape_of_mlProjVisibleCoefficientEscape
#print axioms routeBRicherSPDPStableCandidate_headSpanTailExplicitComplementInvariant_noGo_of_mlProjVisibleCoefficientEscape

end PallLean.Paper93.Paper283
