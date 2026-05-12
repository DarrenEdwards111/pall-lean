import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailDescentObstruction

/-!
# Head-tail chosen-projection kernel criterion proof surfaces

The selected head-tail complement is still arbitrary, so there is no canonical
unconditional invariance theorem for it.  This module packages the positive
side in two useful forms:

* exact stability of the chosen projection kernel under every log-window
  generator map;
* a stricter residual-row annihilation condition, matching the informal
  "residual generators vanish" obligation, which is sufficient for the kernel
  criterion and hence for descent.
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

/-- Operator form of the exact chosen-projection kernel criterion: every
log-window generator map preserves the kernel of the selected head-tail
projection. -/
def RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  forall (spdpKappa ell : Nat)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    S.length <= Nat.log 2 n ->
    shift.totalDegree <= Nat.log 2 n ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    let tail :=
      routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns
    let Pi := routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail
    let L := routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift
    Submodule.map L (LinearMap.ker Pi) <= LinearMap.ker Pi

/-- The kernel-submodule stability form is exactly the pointwise kernel
criterion already exposed by the descent file. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_iff_kernelCriterion
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
        M n hn2 htb hns ↔
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelCriterion
        M n hn2 htb hns := by
  constructor
  · intro hstable spdpKappa ell p S shift hSlen hshiftDegree hSlog
      hshiftLog hshiftVars hadm hp
    let tail :=
      routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns
    let Pi := routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail
    let L := routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift
    have hpKer : p ∈ LinearMap.ker Pi := by
      simpa [Pi] using hp
    have hmap : L p ∈ Submodule.map L (LinearMap.ker Pi) := by
      exact ⟨p, hpKer, rfl⟩
    have hker : L p ∈ LinearMap.ker Pi := by
      exact
        hstable spdpKappa ell S shift hSlen hshiftDegree hSlog
          hshiftLog hshiftVars hadm hmap
    simpa [Pi, L, tail, routeBSPDPGeneratorRowLinearMap_apply] using hker
  · intro hkernel spdpKappa ell S shift hSlen hshiftDegree hSlog
      hshiftLog hshiftVars hadm
    let tail :=
      routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns
    let Pi := routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail
    let L := routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift
    change Submodule.map L (LinearMap.ker Pi) <= LinearMap.ker Pi
    intro q hq
    rcases hq with ⟨p, hpKer, rfl⟩
    have hp : Pi p = 0 := by
      simpa [Pi] using hpKer
    have hzero :
        Pi (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) = 0 :=
      hkernel spdpKappa ell p S shift hSlen hshiftDegree hSlog
        hshiftLog hshiftVars hadm hp
    simpa [Pi, L, tail, routeBSPDPGeneratorRowLinearMap_apply] using hzero

/-- For the canonical head-span tail, stability of the selected projection
kernel is the same condition as stability of the selected complement under the
log-window generator maps. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_iff_chosenComplementStableGeneratorMaps
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
        M n hn2 htb hns ↔
      RouteBRicherSPDPStableCandidateLogWindowChosenComplementStableGeneratorMaps
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns) := by
  rw [routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_iff_kernelCriterion]
  rw [← routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_iff_kernelCriterion]
  exact
    routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_iff_stableGeneratorMaps
      M n hn2 htb hns

/-- Log-window chosen-complement invariance is exactly the stable-generator-map
criterion for the selected head-tail projection kernel. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_iff_logWindowChosenComplementInvariant
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
        M n hn2 htb hns ↔
      RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns) := by
  rw [routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_iff_chosenComplementStableGeneratorMaps]
  exact
    (routeBRicherSPDPStableCandidate_logWindowChosenComplementInvariant_iff_stableGeneratorMaps
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns)).symm

/-- The all-admissible kernel-invisibility obligation for the head-tail
candidate is stronger than the log-window stable-generator-map criterion. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_of_kernelGeneratorInvisible
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hkernel :
      RouteBRicherSPDPStableCandidateKernelGeneratorInvisible
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
      M n hn2 htb hns := by
  refine
    (routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_iff_kernelCriterion
      M n hn2 htb hns).mpr ?_
  intro spdpKappa ell p S shift hSlen hshiftDegree _hSlog
    _hshiftLog hshiftVars hadm hp
  exact
    hkernel spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm hp

/-- Residual invisibility for the head-tail candidate, with no log-window
restriction, implies the log-window stable-generator-map criterion. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_of_residualInvisible
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hinvisible :
      RouteBRicherSPDPStableCandidateResidualInvisible
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
      M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_of_kernelGeneratorInvisible
    M n hn2 htb hns
    ((routeBRicherSPDPStableCandidate_residualInvisible_iff_kernelGeneratorInvisible
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns)).mp hinvisible)

/-- The all-admissible chosen-complement invariance obligation for the
head-tail candidate implies the log-window stable-generator-map criterion. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_of_chosenComplementInvariant
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hinvariant :
      RouteBRicherSPDPStableCandidateChosenComplementInvariant
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
      M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_of_kernelGeneratorInvisible
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_kernelGeneratorInvisible_of_chosenComplementInvariant
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns)
      hinvariant)

/-- Kernel-submodule stability gives chosen-projection descent. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_of_projectionKernelStableGeneratorMaps
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hstable :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
      M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_of_kernelCriterion
    M n hn2 htb hns
    ((routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_iff_kernelCriterion
      M n hn2 htb hns).mp hstable)

/-- Strict residual-row annihilation for the canonical head-tail projection:
every log-window generator row of the projection residual actually vanishes.

This is stronger than the kernel criterion, but it is the concrete
"residual generators vanish" obligation that would make the arbitrary
chosen complement invisible. -/
def RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  forall (spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    S.length <= Nat.log 2 n ->
    shift.totalDegree <= Nat.log 2 n ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    let tail :=
      routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns
    let Pi := routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail
    routeBSPDPGeneratorRow M n hn2 htb hns (p - Pi p) S shift = 0

/-- Equivalent kernel-vector annihilation form of strict residual-row
annihilation. -/
def RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorAnnihilates
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  forall (spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    S.length <= Nat.log 2 n ->
    shift.totalDegree <= Nat.log 2 n ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
        p = 0 ->
    routeBSPDPGeneratorRow M n hn2 htb hns p S shift = 0

/-- Explicit obstruction to strict residual-row annihilation: a log-window
admissible generator row is nonzero on a vector in the chosen projection
kernel. -/
def RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorNonzeroWitness
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
    routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
        p = 0 ∧
    routeBSPDPGeneratorRow M n hn2 htb hns p S shift ≠ 0

/-- Residual-zero gap witness under the chosen-projection kernel criterion:
a log-window generator row starts in the chosen projection kernel, remains
invisible after the chosen projection, but is not the zero row. -/
def RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness
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
    routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
        p = 0 ∧
    routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) = 0 ∧
    routeBSPDPGeneratorRow M n hn2 htb hns p S shift ≠ 0

/-- Coordinate form of the strict kernel-generator nonzero witness: the
unprojected generator row has a nonzero monomial coefficient. -/
def RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorCoefficientNonzeroWitness
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
      (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) ≠ 0

/-- Empty-generator obstruction to strict residual-row annihilation: the
chosen projection kernel contains a vector with nonzero multilinear part. -/
def RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelMlProjNonzeroWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  exists p : SATDeciderGaugeSpace M n hn2 htb hns,
    routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
        p = 0 ∧
    mlProj p ≠ 0

/-- Residual-row annihilation and kernel-vector annihilation are the same
strict condition, rewritten across `p - Π p`. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_iff_kernelGeneratorAnnihilates
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
        M n hn2 htb hns ↔
      RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorAnnihilates
        M n hn2 htb hns := by
  constructor
  · intro hzero spdpKappa ell p S shift hSlen hshiftDegree hSlog
      hshiftLog hshiftVars hadm hp
    let tail :=
      routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns
    let Pi := routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail
    have h :=
      hzero spdpKappa ell p S shift hSlen hshiftDegree hSlog
        hshiftLog hshiftVars hadm
    simpa [RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero,
      tail, Pi, hp, sub_zero] using h
  · intro hann spdpKappa ell p S shift hSlen hshiftDegree hSlog
      hshiftLog hshiftVars hadm
    let tail :=
      routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns
    let Pi := routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail
    have hPiPi : Pi (Pi p) = Pi p := by
      simpa [Pi, tail] using
        routeBRicherSPDPStableCandidate_projection_idempotent
          M n hn2 htb hns tail p
    have hresZero : Pi (p - Pi p) = 0 := by
      simp [Pi, map_sub, hPiPi]
    exact
      hann spdpKappa ell (p - Pi p) S shift hSlen hshiftDegree hSlog
        hshiftLog hshiftVars hadm
        (by simpa [Pi, tail] using hresZero)

/-- A strict kernel-generator nonzero witness is exactly the obstruction to
strict residual-row annihilation. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_iff_no_kernelGeneratorNonzeroWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
        M n hn2 htb hns ↔
      ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorNonzeroWitness
        M n hn2 htb hns := by
  constructor
  · intro hzero hbad
    obtain ⟨spdpKappa, ell, p, S, shift,
      hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm,
      hpZero, hrowNe⟩ := hbad
    have hann :
        RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorAnnihilates
          M n hn2 htb hns :=
      (routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_iff_kernelGeneratorAnnihilates
        M n hn2 htb hns).mp hzero
    exact hrowNe
      (hann spdpKappa ell p S shift hSlen hshiftDegree hSlog hshiftLog
        hshiftVars hadm hpZero)
  · intro hno
    refine
      (routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_iff_kernelGeneratorAnnihilates
        M n hn2 htb hns).mpr ?_
    intro spdpKappa ell p S shift hSlen hshiftDegree hSlog hshiftLog
      hshiftVars hadm hpZero
    by_contra hrowNe
    exact hno
      ⟨spdpKappa, ell, p, S, shift,
        hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm,
        hpZero, hrowNe⟩

/-- Constructor form for the unprojected coordinate strict obstruction. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorCoefficientNonzeroWitness_of_explicitCoeff
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
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) ≠ 0) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorCoefficientNonzeroWitness
      M n hn2 htb hns :=
  ⟨spdpKappa, ell, p, S, shift, μ, hSlen, hshiftDegree, hSlog,
    hshiftLog, hshiftVars, hadm, hpZero, hcoeff⟩

/-- An unprojected nonzero monomial coefficient gives the strict nonzero row
witness. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorNonzeroWitness_of_coefficientNonzeroWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hcoeff :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorCoefficientNonzeroWitness
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorNonzeroWitness
      M n hn2 htb hns := by
  rcases hcoeff with ⟨spdpKappa, ell, p, S, shift, μ,
    hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm,
    hpZero, hμ⟩
  refine ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm, hpZero, ?_⟩
  intro hrowZero
  exact hμ (by simp [hrowZero])

/-- Every strict nonzero generator-row witness has an unprojected visible
monomial coefficient. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorCoefficientNonzeroWitness_of_nonzeroWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorNonzeroWitness
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorCoefficientNonzeroWitness
      M n hn2 htb hns := by
  rcases hbad with ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm,
    hpZero, hrowNe⟩
  obtain ⟨μ, hcoeff⟩ :=
    (mvPolynomial_ne_zero_iff_exists_coeff_ne_zero
      (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)).mp hrowNe
  exact ⟨spdpKappa, ell, p, S, shift, μ, hSlen, hshiftDegree,
    hSlog, hshiftLog, hshiftVars, hadm, hpZero, hcoeff⟩

/-- The coordinate strict obstruction is exactly the unprojected nonzero row
witness. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorCoefficientNonzeroWitness_iff_nonzeroWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorCoefficientNonzeroWitness
        M n hn2 htb hns ↔
      RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorNonzeroWitness
        M n hn2 htb hns :=
  ⟨routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorNonzeroWitness_of_coefficientNonzeroWitness
      M n hn2 htb hns,
    routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorCoefficientNonzeroWitness_of_nonzeroWitness
      M n hn2 htb hns⟩

/-- Strict residual-row annihilation is exactly absence of an unprojected
coordinate nonzero generator-row witness. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_iff_no_kernelGeneratorCoefficientNonzeroWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
        M n hn2 htb hns ↔
      ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorCoefficientNonzeroWitness
        M n hn2 htb hns := by
  rw [
    routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_iff_no_kernelGeneratorNonzeroWitness,
    routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorCoefficientNonzeroWitness_iff_nonzeroWitness]

/-- Failure of strict residual-row annihilation produces a concrete nonzero
kernel-generator witness. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorNonzeroWitness_of_not_residualGeneratorZero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hnot :
      ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorNonzeroWitness
      M n hn2 htb hns := by
  by_contra hnoWitness
  exact hnot
    ((routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_iff_no_kernelGeneratorNonzeroWitness
      M n hn2 htb hns).mpr hnoWitness)

/-- Failure of strict residual-row annihilation produces an unprojected
coordinate nonzero kernel-generator witness. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorCoefficientNonzeroWitness_of_not_residualGeneratorZero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hnot :
      ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorCoefficientNonzeroWitness
      M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorCoefficientNonzeroWitness_of_nonzeroWitness
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorNonzeroWitness_of_not_residualGeneratorZero
      M n hn2 htb hns hnot)

/-- Any concrete nonzero kernel-generator witness refutes strict
residual-row annihilation. -/
theorem routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_of_kernelGeneratorNonzeroWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorNonzeroWitness
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
        M n hn2 htb hns := by
  intro hzero
  exact
    ((routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_iff_no_kernelGeneratorNonzeroWitness
      M n hn2 htb hns).mp hzero) hbad

/-- Any unprojected coordinate nonzero generator-row witness refutes strict
residual-row annihilation. -/
theorem routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_of_kernelGeneratorCoefficientNonzeroWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorCoefficientNonzeroWitness
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
        M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_of_kernelGeneratorNonzeroWitness
    M n hn2 htb hns
    ((routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorCoefficientNonzeroWitness_iff_nonzeroWitness
      M n hn2 htb hns).mp hbad)

/-- A nonzero `mlProj` vector in the chosen projection kernel is the smallest
log-window kernel-generator nonzero witness: take the empty derivative list
and constant shift `1`. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorNonzeroWitness_of_kernelMlProjNonzeroWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelMlProjNonzeroWitness
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorNonzeroWitness
      M n hn2 htb hns := by
  obtain ⟨p, hpZero, hmlNe⟩ := hbad
  refine ⟨0, 0, p,
    ([] : List (Fin (RouteBCookLevinDim M n hn2 htb hns))),
    (1 : SATDeciderGaugeSpace M n hn2 htb hns),
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
  · simpa [routeBSPDPGeneratorRow, SPDP.iterDerivList, mlProj_one] using hmlNe

/-- The empty-generator `mlProj` obstruction refutes strict residual-row
annihilation. -/
theorem routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_of_kernelMlProjNonzeroWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelMlProjNonzeroWitness
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
        M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_of_kernelGeneratorNonzeroWitness
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorNonzeroWitness_of_kernelMlProjNonzeroWitness
      M n hn2 htb hns hbad)

/-- If every log-window generator annihilates vectors in the selected
head-span-tail complement, then the residual of the selected projection has
strict zero generator rows. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_of_chosenComplement_generator_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hann :
      forall (spdpKappa ell : Nat)
        (p : SATDeciderGaugeSpace M n hn2 htb hns)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ->
        shift.totalDegree <= ell ->
        S.length <= Nat.log 2 n ->
        shift.totalDegree <= Nat.log 2 n ->
        shift.vars <= S.toFinset ->
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ->
        p ∈ routeBRicherSPDPStableCandidateLogWindowHeadTailChosenComplement
          M n hn2 htb hns ->
        routeBSPDPGeneratorRow M n hn2 htb hns p S shift = 0) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
      M n hn2 htb hns := by
  refine
    (routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_iff_kernelGeneratorAnnihilates
      M n hn2 htb hns).mpr ?_
  intro spdpKappa ell p S shift hSlen hshiftDegree hSlog hshiftLog
    hshiftVars hadm hp
  let tail := routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns
  have hpComplement :
      p ∈ routeBRicherSPDPStableCandidateLogWindowHeadTailChosenComplement
        M n hn2 htb hns := by
    simpa [routeBRicherSPDPStableCandidateLogWindowHeadTailChosenComplement,
      tail] using
      (routeBRicherSPDPStableCandidateProjection_apply_eq_zero_iff_projectionComplement
        M n hn2 htb hns tail p).mp hp
  exact
    hann spdpKappa ell p S shift hSlen hshiftDegree hSlog
      hshiftLog hshiftVars hadm hpComplement

/-- The all-admissible zero-before-projection kernel obligation for the
head-tail candidate is stronger than strict log-window residual-generator
zero. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_of_kernelGeneratorZero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hzero :
      RouteBRicherSPDPStableCandidateKernelGeneratorZero
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
      M n hn2 htb hns := by
  refine
    (routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_iff_kernelGeneratorAnnihilates
      M n hn2 htb hns).mpr ?_
  intro spdpKappa ell p S shift hSlen hshiftDegree _hSlog
    _hshiftLog hshiftVars hadm hp
  exact
    hzero spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm hp

/-- A log-window nonzero kernel-generator witness also refutes the stronger
all-admissible zero-before-projection kernel obligation for the head-tail
candidate. -/
theorem routeBRicherSPDPStableCandidate_not_kernelGeneratorZero_of_logWindowHeadTailKernelGeneratorNonzeroWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorNonzeroWitness
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateKernelGeneratorZero
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns) := by
  intro hzero
  obtain ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, _hSlog, _hshiftLog, hshiftVars, hadm,
    hpZero, hrowNe⟩ := hbad
  exact hrowNe
    (hzero spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm hpZero)

/-- A visible chosen-kernel obstruction already gives an unprojected nonzero
generator-row witness, since a nonzero projection cannot come from the zero
row. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorNonzeroWitness_of_kernelObstruction
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelObstruction
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorNonzeroWitness
      M n hn2 htb hns := by
  rcases hbad with ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm,
    hpZero, hvisible⟩
  refine ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm, hpZero, ?_⟩
  intro hrowZero
  exact hvisible (by simp [hrowZero])

/-- A visible chosen-kernel obstruction has an unprojected monomial
coefficient witness. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorCoefficientNonzeroWitness_of_kernelObstruction
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelObstruction
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorCoefficientNonzeroWitness
      M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorCoefficientNonzeroWitness_of_nonzeroWitness
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorNonzeroWitness_of_kernelObstruction
      M n hn2 htb hns hbad)

/-- The stronger all-admissible kernel-generator-zero obligation excludes
the explicit strict log-window obstruction. -/
theorem routeBRicherSPDPStableCandidate_no_logWindowHeadTailKernelGeneratorNonzeroWitness_of_kernelGeneratorZero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hzero :
      RouteBRicherSPDPStableCandidateKernelGeneratorZero
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)) :
    ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorNonzeroWitness
        M n hn2 htb hns := by
  intro hbad
  exact
    (routeBRicherSPDPStableCandidate_not_kernelGeneratorZero_of_logWindowHeadTailKernelGeneratorNonzeroWitness
      M n hn2 htb hns hbad) hzero

/-- Strict kernel-generator annihilation proves the exact chosen-projection
kernel criterion. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionKernelCriterion_of_kernelGeneratorAnnihilates
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hann :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorAnnihilates
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelCriterion
      M n hn2 htb hns := by
  intro spdpKappa ell p S shift hSlen hshiftDegree hSlog hshiftLog
    hshiftVars hadm hp
  have hrowZero :
      routeBSPDPGeneratorRow M n hn2 htb hns p S shift = 0 :=
    hann spdpKappa ell p S shift hSlen hshiftDegree hSlog hshiftLog
      hshiftVars hadm hp
  rw [hrowZero]
  simp

/-- Strict residual-row annihilation proves the exact chosen-projection kernel
criterion. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionKernelCriterion_of_residualGeneratorZero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hzero :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelCriterion
      M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionKernelCriterion_of_kernelGeneratorAnnihilates
    M n hn2 htb hns
    ((routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_iff_kernelGeneratorAnnihilates
      M n hn2 htb hns).mp hzero)

/-- A projection-invisible nonzero kernel-generator witness is, after
forgetting the projection-invisibility clause, a strict nonzero generator-row
witness. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorNonzeroWitness_of_projectionInvisibleNonzeroWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorNonzeroWitness
      M n hn2 htb hns := by
  rcases hbad with ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm,
    hpZero, _hprojZero, hrowNe⟩
  exact ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm,
    hpZero, hrowNe⟩

/-- A projection-invisible nonzero kernel-generator row directly refutes
strict residual-row zero. -/
theorem routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_of_projectionInvisibleNonzeroWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
        M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_of_kernelGeneratorNonzeroWitness
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorNonzeroWitness_of_projectionInvisibleNonzeroWitness
      M n hn2 htb hns hbad)

/-- Under the chosen-projection kernel criterion, every strict nonzero
kernel-generator witness is exactly projection-invisible. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness_of_kernelCriterion_of_nonzeroWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hkernel :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelCriterion
        M n hn2 htb hns)
    (hbad :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorNonzeroWitness
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness
      M n hn2 htb hns := by
  rcases hbad with ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm,
    hpZero, hrowNe⟩
  exact ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm,
    hpZero,
    hkernel spdpKappa ell p S shift hSlen hshiftDegree hSlog
      hshiftLog hshiftVars hadm hpZero,
    hrowNe⟩

/-- A strict nonzero kernel-generator witness splits exactly into either the
projection-invisible residual gap or the visible chosen-kernel obstruction. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorNonzeroWitness_iff_projectionInvisibleNonzeroWitness_or_kernelObstruction
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorNonzeroWitness
        M n hn2 htb hns ↔
      RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness
          M n hn2 htb hns ∨
        RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelObstruction
          M n hn2 htb hns := by
  constructor
  · intro hbad
    rcases hbad with ⟨spdpKappa, ell, p, S, shift,
      hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm,
      hpZero, hrowNe⟩
    by_cases hprojZero :
        routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
          (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) = 0
    · exact Or.inl
        ⟨spdpKappa, ell, p, S, shift,
          hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm,
          hpZero, hprojZero, hrowNe⟩
    · exact Or.inr
        ⟨spdpKappa, ell, p, S, shift,
          hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm,
          hpZero, hprojZero⟩
  · intro hsplit
    rcases hsplit with hbad | hbad
    · exact
        routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorNonzeroWitness_of_projectionInvisibleNonzeroWitness
          M n hn2 htb hns hbad
    · exact
        routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorNonzeroWitness_of_kernelObstruction
          M n hn2 htb hns hbad

/-- Failure of strict residual-row annihilation is exactly the disjunction
between a projection-invisible residual gap and a visible chosen-kernel
obstruction. -/
theorem routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_iff_projectionInvisibleNonzeroWitness_or_kernelObstruction
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    (¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
        M n hn2 htb hns) ↔
      RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness
          M n hn2 htb hns ∨
        RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelObstruction
          M n hn2 htb hns := by
  constructor
  · intro hnot
    exact
      (routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorNonzeroWitness_iff_projectionInvisibleNonzeroWitness_or_kernelObstruction
        M n hn2 htb hns).mp
        (routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorNonzeroWitness_of_not_residualGeneratorZero
          M n hn2 htb hns hnot)
  · intro hsplit hzero
    rcases hsplit with hbad | hbad
    · exact
        (routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_of_projectionInvisibleNonzeroWitness
          M n hn2 htb hns hbad) hzero
    · exact
        (routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_of_kernelGeneratorNonzeroWitness
          M n hn2 htb hns
          (routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorNonzeroWitness_of_kernelObstruction
            M n hn2 htb hns hbad)) hzero

/-- Projection-escape version of the strict residual-failure split: a failed
strict residual proof is either projection-invisible, or it is exactly the
existing visible log-window projection escape. -/
theorem routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_iff_projectionInvisibleNonzeroWitness_or_logWindowProjectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    (¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
        M n hn2 htb hns) ↔
      RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness
          M n hn2 htb hns ∨
        RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
          M n hn2 htb hns := by
  constructor
  · intro hnot
    rcases
      (routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_iff_projectionInvisibleNonzeroWitness_or_kernelObstruction
        M n hn2 htb hns).mp hnot with hbad | hbad
    · exact Or.inl hbad
    · exact Or.inr
        (routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_kernelObstruction
          M n hn2 htb hns hbad)
  · intro hsplit hzero
    rcases hsplit with hbad | hbad
    · exact
        (routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_of_projectionInvisibleNonzeroWitness
          M n hn2 htb hns hbad) hzero
    · exact
        (routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_of_kernelGeneratorNonzeroWitness
          M n hn2 htb hns
          (routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorNonzeroWitness_of_kernelObstruction
            M n hn2 htb hns
            (routeBRicherSPDPStableCandidate_headSpanTailKernelObstruction_of_logWindowProjectionEscapeWitness
              M n hn2 htb hns hbad))) hzero

/-- Under the chosen-projection kernel criterion, failure of strict
residual-row zero instantiates the projection-invisible nonzero witness. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness_of_kernelCriterion_of_not_residualGeneratorZero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hkernel :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelCriterion
        M n hn2 htb hns)
    (hnot :
      ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness
      M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness_of_kernelCriterion_of_nonzeroWitness
    M n hn2 htb hns hkernel
    (routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorNonzeroWitness_of_not_residualGeneratorZero
      M n hn2 htb hns hnot)

/-- Criterion-relative exact alternative: once the chosen-projection kernel
criterion holds, the projection-invisible nonzero witness is equivalent to
failure of strict residual-row zero. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness_iff_not_residualGeneratorZero_of_kernelCriterion
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hkernel :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelCriterion
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness
        M n hn2 htb hns ↔
      ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
        M n hn2 htb hns :=
  ⟨routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_of_projectionInvisibleNonzeroWitness
      M n hn2 htb hns,
    routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness_of_kernelCriterion_of_not_residualGeneratorZero
      M n hn2 htb hns hkernel⟩

/-- Stable-generator-map form of the criterion-relative exact alternative. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness_iff_not_residualGeneratorZero_of_projectionKernelStableGeneratorMaps
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hstable :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness
        M n hn2 htb hns ↔
      ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
        M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness_iff_not_residualGeneratorZero_of_kernelCriterion
    M n hn2 htb hns
    ((routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_iff_kernelCriterion
      M n hn2 htb hns).mp hstable)

/-- Exact conjunction surface: the projection-invisible residual gap carries
the same information as strict residual failure once the kernel criterion is
kept explicit. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailKernelCriterion_and_projectionInvisibleNonzeroWitness_iff_kernelCriterion_and_not_residualGeneratorZero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    (RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelCriterion
        M n hn2 htb hns ∧
      RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness
        M n hn2 htb hns) ↔
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelCriterion
          M n hn2 htb hns ∧
        ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
          M n hn2 htb hns := by
  constructor
  · rintro ⟨hkernel, hbad⟩
    exact ⟨hkernel,
      routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_of_projectionInvisibleNonzeroWitness
        M n hn2 htb hns hbad⟩
  · rintro ⟨hkernel, hnot⟩
    exact ⟨hkernel,
      routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness_of_kernelCriterion_of_not_residualGeneratorZero
        M n hn2 htb hns hkernel hnot⟩

/-- Exact strict-residual interface: once the chosen-projection kernel
criterion is available, the only extra obstruction to strict residual-row zero
is a projection-invisible nonzero generator row on a chosen-kernel vector. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_iff_kernelCriterion_and_no_projectionInvisibleNonzeroWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
        M n hn2 htb hns ↔
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelCriterion
          M n hn2 htb hns ∧
        ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness
          M n hn2 htb hns := by
  constructor
  · intro hzero
    refine ⟨
      routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionKernelCriterion_of_residualGeneratorZero
        M n hn2 htb hns hzero,
      ?_⟩
    intro hbad
    exact
      ((routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_iff_no_kernelGeneratorNonzeroWitness
        M n hn2 htb hns).mp hzero)
        (routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorNonzeroWitness_of_projectionInvisibleNonzeroWitness
          M n hn2 htb hns hbad)
  · rintro ⟨hkernel, hnoInvisible⟩
    refine
      (routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_iff_kernelGeneratorAnnihilates
        M n hn2 htb hns).mpr ?_
    intro spdpKappa ell p S shift hSlen hshiftDegree hSlog hshiftLog
      hshiftVars hadm hpZero
    by_contra hrowNe
    exact hnoInvisible
      ⟨spdpKappa, ell, p, S, shift,
        hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm,
        hpZero,
        hkernel spdpKappa ell p S shift hSlen hshiftDegree hSlog
          hshiftLog hshiftVars hadm hpZero,
        hrowNe⟩

/-- Stable-generator-map version of the exact strict-residual interface. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_iff_projectionKernelStableGeneratorMaps_and_no_projectionInvisibleNonzeroWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
        M n hn2 htb hns ↔
      RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
          M n hn2 htb hns ∧
        ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness
          M n hn2 htb hns := by
  rw [
    routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_iff_kernelCriterion_and_no_projectionInvisibleNonzeroWitness,
    routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_iff_kernelCriterion]

/-- Constructor form for strict residual-row zero from the exact isolated
kernel-criterion plus projection-invisible-row exclusion. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_of_kernelCriterion_no_projectionInvisibleNonzeroWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hkernel :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelCriterion
        M n hn2 htb hns)
    (hnoInvisible :
      ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
      M n hn2 htb hns :=
  (routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_iff_kernelCriterion_and_no_projectionInvisibleNonzeroWitness
    M n hn2 htb hns).mpr ⟨hkernel, hnoInvisible⟩

/-- Constructor form using the stable-generator-map surface plus the exact
projection-invisible-row exclusion. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_of_projectionKernelStableGeneratorMaps_no_projectionInvisibleNonzeroWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hstable :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
        M n hn2 htb hns)
    (hnoInvisible :
      ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
      M n hn2 htb hns :=
  (routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_iff_projectionKernelStableGeneratorMaps_and_no_projectionInvisibleNonzeroWitness
    M n hn2 htb hns).mpr ⟨hstable, hnoInvisible⟩

/-- Strict residual-row annihilation is a sufficient positive proof of
chosen-projection descent. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_of_residualGeneratorZero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hzero :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
      M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_of_kernelCriterion
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionKernelCriterion_of_residualGeneratorZero
      M n hn2 htb hns hzero)

/-- A visible chosen-kernel obstruction refutes the stricter residual-row
annihilation condition. -/
theorem routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_of_kernelObstruction
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelObstruction
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
        M n hn2 htb hns := by
  intro hzero
  have hcriterion :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelCriterion
        M n hn2 htb hns :=
    routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionKernelCriterion_of_residualGeneratorZero
      M n hn2 htb hns hzero
  rcases hbad with ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm,
    hpZero, hvisible⟩
  exact hvisible
    (hcriterion spdpKappa ell p S shift hSlen hshiftDegree hSlog
      hshiftLog hshiftVars hadm hpZero)

/-- Consequently, a log-window projection-escape witness also refutes strict
residual-row annihilation. -/
theorem routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_of_logWindowProjectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
        M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_of_kernelObstruction
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headSpanTailKernelObstruction_of_logWindowProjectionEscapeWitness
      M n hn2 htb hns hbad)

/-! ## Axiom audit anchors -/

#print axioms RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
#print axioms mvPolynomial_ne_zero_iff_exists_coeff_ne_zero
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_iff_kernelCriterion
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_iff_chosenComplementStableGeneratorMaps
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_iff_logWindowChosenComplementInvariant
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_of_kernelGeneratorInvisible
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_of_residualInvisible
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_of_chosenComplementInvariant
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_of_projectionKernelStableGeneratorMaps
#print axioms RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
#print axioms RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorAnnihilates
#print axioms RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorNonzeroWitness
#print axioms RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness
#print axioms RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorCoefficientNonzeroWitness
#print axioms RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelMlProjNonzeroWitness
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_iff_kernelGeneratorAnnihilates
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_iff_no_kernelGeneratorNonzeroWitness
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorCoefficientNonzeroWitness_iff_nonzeroWitness
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_iff_no_kernelGeneratorCoefficientNonzeroWitness
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorNonzeroWitness_of_not_residualGeneratorZero
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorCoefficientNonzeroWitness_of_not_residualGeneratorZero
#print axioms routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_of_kernelGeneratorNonzeroWitness
#print axioms routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_of_kernelGeneratorCoefficientNonzeroWitness
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorNonzeroWitness_of_kernelMlProjNonzeroWitness
#print axioms routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_of_kernelMlProjNonzeroWitness
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_of_chosenComplement_generator_zero
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_of_kernelGeneratorZero
#print axioms routeBRicherSPDPStableCandidate_not_kernelGeneratorZero_of_logWindowHeadTailKernelGeneratorNonzeroWitness
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorCoefficientNonzeroWitness_of_kernelObstruction
#print axioms routeBRicherSPDPStableCandidate_no_logWindowHeadTailKernelGeneratorNonzeroWitness_of_kernelGeneratorZero
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorNonzeroWitness_of_projectionInvisibleNonzeroWitness
#print axioms routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_of_projectionInvisibleNonzeroWitness
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness_of_kernelCriterion_of_nonzeroWitness
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorNonzeroWitness_iff_projectionInvisibleNonzeroWitness_or_kernelObstruction
#print axioms routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_iff_projectionInvisibleNonzeroWitness_or_kernelObstruction
#print axioms routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_iff_projectionInvisibleNonzeroWitness_or_logWindowProjectionEscapeWitness
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness_of_kernelCriterion_of_not_residualGeneratorZero
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness_iff_not_residualGeneratorZero_of_kernelCriterion
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailKernelGeneratorProjectionInvisibleNonzeroWitness_iff_not_residualGeneratorZero_of_projectionKernelStableGeneratorMaps
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailKernelCriterion_and_projectionInvisibleNonzeroWitness_iff_kernelCriterion_and_not_residualGeneratorZero
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_iff_kernelCriterion_and_no_projectionInvisibleNonzeroWitness
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_iff_projectionKernelStableGeneratorMaps_and_no_projectionInvisibleNonzeroWitness
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_of_kernelCriterion_no_projectionInvisibleNonzeroWitness
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_of_projectionKernelStableGeneratorMaps_no_projectionInvisibleNonzeroWitness
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionKernelCriterion_of_residualGeneratorZero
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_of_residualGeneratorZero
#print axioms routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_of_kernelObstruction
#print axioms routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_of_logWindowProjectionEscapeWitness

end PallLean.Paper93.Paper283
