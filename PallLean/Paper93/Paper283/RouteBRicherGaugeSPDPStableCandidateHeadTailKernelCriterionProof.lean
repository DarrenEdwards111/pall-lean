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
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_iff_kernelCriterion
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_iff_chosenComplementStableGeneratorMaps
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_iff_logWindowChosenComplementInvariant
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_of_kernelGeneratorInvisible
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_of_residualInvisible
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_of_chosenComplementInvariant
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_of_projectionKernelStableGeneratorMaps
#print axioms RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
#print axioms RouteBRicherSPDPStableCandidateLogWindowHeadTailKernelGeneratorAnnihilates
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_iff_kernelGeneratorAnnihilates
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_of_chosenComplement_generator_zero
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_of_kernelGeneratorZero
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionKernelCriterion_of_residualGeneratorZero
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_of_residualGeneratorZero
#print axioms routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_of_kernelObstruction
#print axioms routeBRicherSPDPStableCandidate_not_logWindowHeadTailResidualGeneratorZero_of_logWindowProjectionEscapeWitness

end PallLean.Paper93.Paper283
