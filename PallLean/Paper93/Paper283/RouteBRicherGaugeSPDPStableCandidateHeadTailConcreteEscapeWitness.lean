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

/-! ## Axiom audit anchors -/

#print axioms mvPolynomial_ne_zero_iff_exists_coeff_ne_zero
#print axioms RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
#print axioms routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_iff_logWindowProjectionEscapeWitness
#print axioms RouteBRicherSPDPStableCandidateHeadSpanTailMlProjVisibleCoefficientEscapeWitness
#print axioms routeBRicherSPDPStableCandidate_mlProjVisibleCoefficientEscape_iff_kernelMlProjProjectionEscape
#print axioms routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_mlProjVisibleCoefficientEscape

end PallLean.Paper93.Paper283
