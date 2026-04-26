import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidate
import PallLean.Paper93.Paper283.BridgeAMlProjLinear
import PallLean.IterDerivHelpers

/-!
# Kernel-form characterization and no-go criteria for the smaller
  SPDP-stable candidate

This file ports the existence-of-witness no-go criteria from
`RouteBRicherGaugeConcreteMultilinearResidual` to the smaller concrete-NP
prepended SPDP-stable candidate (`RouteBRicherGaugeSPDPStableCandidate`).
The kernel-form predicate and equivalence live in
`RouteBRicherGaugeSPDPStableCandidate`.

Unlike the broad multilinear-tail case, the smaller candidate's residual
obligation is `ResidualInvisible`: only the *projection* of the residual
generator must vanish, not the generator itself.  Consequently the
refutation criteria here are weaker — strictly more candidate tails survive
them — and a concrete refutation requires a kernel vector whose generator's
projection (not the generator) is nonzero.

The companion file `RouteBRicherGaugeSPDPStableCandidateProfileTail` records
the structural narrowing complementary to these no-gos: any tail that
covers every `mlProj` output already inherits the strict broad-tail no-go
(see
`routeBRicherSPDPStableCandidate_residualInvisible_iff_residualGeneratorZero_of_mlCovering`).
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Idempotency of the smaller-candidate projection.  Lifts the
`is_idempotent` field on `CandidateGauge` through `routeBNFrameCandidateAsSATGauge`,
exactly mirroring the manipulation used in `Residual.lean`. -/
theorem routeBRicherSPDPStableCandidate_projection_idempotent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail
        (routeBRicherSPDPStableCandidateProjection
          M n hn2 htb hns tail p) =
      routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail p := by
  have hidem :=
    (routeBRicherSPDPStableCandidateGauge M n hn2 htb hns tail).is_idempotent
  have happ := congrArg (fun L => L p) hidem
  simpa [routeBRicherSPDPStableCandidateProjection,
    routeBRicherSPDPStableCandidateGauge,
    LinearMap.comp_apply] using happ

/-- Smaller SPDP-stable candidate gauge with a caller-supplied complement to
the prepended finite-row span. -/
noncomputable abbrev routeBRicherSPDPStableCandidateGaugeWithComplement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (T : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hT :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail))
        T) :
    PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns) :=
  routeBRicherFiniteRowsCandidateGaugeWithComplement M n hn2 htb hns
    (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail) T hT

/-- SAT-side projection for the explicit-complement smaller SPDP-stable
candidate. -/
noncomputable abbrev routeBRicherSPDPStableCandidateProjectionWithComplement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (T : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hT :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail))
        T) :
    SATDeciderGaugeSpace M n hn2 htb hns →ₗ[Rat]
      SATDeciderGaugeSpace M n hn2 htb hns :=
  routeBNFrameCandidateAsSATGauge M n hn2 htb hns
    (routeBRicherSPDPStableCandidateGaugeWithComplement
      M n hn2 htb hns tail T hT)

/-- Kernel criterion for the explicit-complement smaller SPDP-stable
projection. -/
theorem routeBRicherSPDPStableCandidateProjectionWithComplement_apply_eq_zero_iff
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (T : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hT :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail))
        T)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    routeBRicherSPDPStableCandidateProjectionWithComplement
        M n hn2 htb hns tail T hT p = 0 ↔
      p ∈ T := by
  let rows := routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail
  have hzero :=
    routeBRicherFiniteRowsCandidateGaugeWithComplement_projection_apply_eq_zero_iff
      M n hn2 htb hns rows T hT p
  simpa [routeBRicherSPDPStableCandidateProjectionWithComplement,
    routeBRicherSPDPStableCandidateGaugeWithComplement, rows] using hzero

/-- Explicit-complement invariance for the smaller SPDP-stable candidate:
admissible SPDP generator rows preserve the supplied complement `T`. -/
def RouteBRicherSPDPStableCandidateExplicitComplementInvariant
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (_tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (T : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns)) : Prop :=
  forall (spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    p ∈ T ->
    routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∈ T

/-- Kernel-generator invisibility for the explicit-complement projection. -/
def RouteBRicherSPDPStableCandidateKernelGeneratorInvisibleWithComplement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (T : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hT :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail))
        T) : Prop :=
  forall (spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    routeBRicherSPDPStableCandidateProjectionWithComplement
      M n hn2 htb hns tail T hT p = 0 ->
    routeBRicherSPDPStableCandidateProjectionWithComplement
      M n hn2 htb hns tail T hT
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) = 0

/-- For any explicitly supplied complement, kernel-generator invisibility for
the corresponding projection is exactly generator invariance of that
complement. -/
theorem routeBRicherSPDPStableCandidate_kernelGeneratorInvisibleWithComplement_iff_explicitComplementInvariant
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (T : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hT :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail))
        T) :
    RouteBRicherSPDPStableCandidateKernelGeneratorInvisibleWithComplement
        M n hn2 htb hns tail T hT ↔
      RouteBRicherSPDPStableCandidateExplicitComplementInvariant
        M n hn2 htb hns tail T := by
  constructor
  · intro hkernel spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm hpT
    have hker :
        routeBRicherSPDPStableCandidateProjectionWithComplement
          M n hn2 htb hns tail T hT p = 0 :=
      (routeBRicherSPDPStableCandidateProjectionWithComplement_apply_eq_zero_iff
        M n hn2 htb hns tail T hT p).mpr hpT
    have hrowZero :=
      hkernel spdpKappa ell p S shift
        hSlen hshiftDegree hshiftVars hadm hker
    exact
      (routeBRicherSPDPStableCandidateProjectionWithComplement_apply_eq_zero_iff
        M n hn2 htb hns tail T hT
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)).mp hrowZero
  · intro hinvariant spdpKappa ell p S shift
      hSlen hshiftDegree hshiftVars hadm hker
    have hpT :
        p ∈ T :=
      (routeBRicherSPDPStableCandidateProjectionWithComplement_apply_eq_zero_iff
        M n hn2 htb hns tail T hT p).mp hker
    have hrowT :=
      hinvariant spdpKappa ell p S shift
        hSlen hshiftDegree hshiftVars hadm hpT
    exact
      (routeBRicherSPDPStableCandidateProjectionWithComplement_apply_eq_zero_iff
        M n hn2 htb hns tail T hT
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)).mpr hrowT

/-- Explicit-complement escape directly refutes explicit complement
invariance. -/
theorem routeBRicherSPDPStableCandidate_explicitComplementInvariant_noGo_of_generator_escape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (T : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hbad :
      exists (spdpKappa ell : Nat)
        (p : SATDeciderGaugeSpace M n hn2 htb hns)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ∧
        shift.totalDegree <= ell ∧
        shift.vars <= S.toFinset ∧
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ∧
        p ∈ T ∧
        routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∉ T) :
    ¬ RouteBRicherSPDPStableCandidateExplicitComplementInvariant
        M n hn2 htb hns tail T := by
  intro hinvariant
  obtain ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hshiftVars, hadm, hpT, hrowNotT⟩ := hbad
  exact hrowNotT
    (hinvariant spdpKappa ell p S shift
      hSlen hshiftDegree hshiftVars hadm hpT)

/-- Explicit-complement escape directly refutes kernel-generator invisibility
for the projection built from that complement. -/
theorem routeBRicherSPDPStableCandidate_kernelGeneratorInvisibleWithComplement_noGo_of_generator_escape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (T : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hT :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail))
        T)
    (hbad :
      exists (spdpKappa ell : Nat)
        (p : SATDeciderGaugeSpace M n hn2 htb hns)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ∧
        shift.totalDegree <= ell ∧
        shift.vars <= S.toFinset ∧
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ∧
        p ∈ T ∧
        routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∉ T) :
    ¬ RouteBRicherSPDPStableCandidateKernelGeneratorInvisibleWithComplement
        M n hn2 htb hns tail T hT := by
  intro hkernel
  exact
    routeBRicherSPDPStableCandidate_explicitComplementInvariant_noGo_of_generator_escape
      M n hn2 htb hns tail T hbad
      ((routeBRicherSPDPStableCandidate_kernelGeneratorInvisibleWithComplement_iff_explicitComplementInvariant
        M n hn2 htb hns tail T hT).mp hkernel)

/-- No-go criterion (general): existence of an admissible `(p, S, shift)`
with `Π p = 0` but `Π(gen(p, S, shift)) ≠ 0` refutes
`ResidualInvisible`. -/
theorem routeBRicherSPDPStableCandidate_residualInvisible_noGo_of_kernelGenerator_ne_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hbad :
      exists (spdpKappa ell : Nat)
        (p : SATDeciderGaugeSpace M n hn2 htb hns)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ∧
        shift.totalDegree <= ell ∧
        shift.vars <= S.toFinset ∧
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ∧
        routeBRicherSPDPStableCandidateProjection
          M n hn2 htb hns tail p = 0 ∧
        routeBRicherSPDPStableCandidateProjection
          M n hn2 htb hns tail
          (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) ≠ 0) :
    ¬ RouteBRicherSPDPStableCandidateResidualInvisible
        M n hn2 htb hns tail := by
  intro hinv
  obtain ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hshiftVars, hadm, hker, hne⟩ := hbad
  have hkernel :=
    (routeBRicherSPDPStableCandidate_residualInvisible_iff_kernelGeneratorInvisible
      M n hn2 htb hns tail).mp hinv
  exact hne
    (hkernel spdpKappa ell p S shift
      hSlen hshiftDegree hshiftVars hadm hker)

/-- No-go criterion in the exposed-complement form: if an admissible generator
map sends some vector from the finite projection's chosen complement out of
that complement, then residual invisibility fails. -/
theorem routeBRicherSPDPStableCandidate_residualInvisible_noGo_of_chosenComplementGenerator_escape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hbad :
      exists (spdpKappa ell : Nat)
        (p : SATDeciderGaugeSpace M n hn2 htb hns)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ∧
        shift.totalDegree <= ell ∧
        shift.vars <= S.toFinset ∧
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ∧
        p ∈ routeBRicherSPDPStableCandidateProjectionComplement
          M n hn2 htb hns tail ∧
        routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∉
          routeBRicherSPDPStableCandidateProjectionComplement
            M n hn2 htb hns tail) :
    ¬ RouteBRicherSPDPStableCandidateResidualInvisible
        M n hn2 htb hns tail := by
  apply
    routeBRicherSPDPStableCandidate_residualInvisible_noGo_of_kernelGenerator_ne_zero
      M n hn2 htb hns tail
  obtain ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hshiftVars, hadm, hpComplement,
    hrowNotComplement⟩ := hbad
  let rows := routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail
  have hpRows :
      p ∈ finiteSubmoduleProjectionComplement (finiteRowsSubmodule rows) := by
    simpa [routeBRicherSPDPStableCandidateProjectionComplement, rows] using
      hpComplement
  have hkerRows :
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows).projection p =
        0 :=
    (routeBRicherFiniteRowsCandidateGauge_projection_apply_eq_zero_iff
      M n hn2 htb hns rows p).mpr hpRows
  have hker :
      routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail p = 0 := by
    simpa [routeBRicherSPDPStableCandidateProjection,
      routeBRicherSPDPStableCandidateGauge, rows]
      using hkerRows
  have hne :
      routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail
          (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) ≠ 0 := by
    intro hzero
    have hrowRowsZero :
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows).projection
            (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) = 0 := by
      simpa [routeBRicherSPDPStableCandidateProjection,
        routeBRicherSPDPStableCandidateGauge, rows]
        using hzero
    have hrowRowsComplement :
        routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∈
          finiteSubmoduleProjectionComplement (finiteRowsSubmodule rows) :=
      (routeBRicherFiniteRowsCandidateGauge_projection_apply_eq_zero_iff
        M n hn2 htb hns rows
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)).mp hrowRowsZero
    exact hrowNotComplement
      (by
        simpa [routeBRicherSPDPStableCandidateProjectionComplement, rows] using
          hrowRowsComplement)
  exact
    ⟨spdpKappa, ell, p, S, shift,
      hSlen, hshiftDegree, hshiftVars, hadm, hker, hne⟩

/-- Chosen-complement escape directly refutes chosen-complement invariance. -/
theorem routeBRicherSPDPStableCandidate_chosenComplementInvariant_noGo_of_chosenComplementGenerator_escape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hbad :
      exists (spdpKappa ell : Nat)
        (p : SATDeciderGaugeSpace M n hn2 htb hns)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ∧
        shift.totalDegree <= ell ∧
        shift.vars <= S.toFinset ∧
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ∧
        p ∈ routeBRicherSPDPStableCandidateProjectionComplement
          M n hn2 htb hns tail ∧
        routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∉
          routeBRicherSPDPStableCandidateProjectionComplement
            M n hn2 htb hns tail) :
    ¬ RouteBRicherSPDPStableCandidateChosenComplementInvariant
        M n hn2 htb hns tail := by
  intro hinvariant
  obtain ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hshiftVars, hadm, hpComplement,
    hrowNotComplement⟩ := hbad
  exact hrowNotComplement
    (hinvariant spdpKappa ell p S shift
      hSlen hshiftDegree hshiftVars hadm hpComplement)

/-- Chosen-complement escape directly refutes the kernel-generator invisible
form, without first passing through `ResidualInvisible`. -/
theorem routeBRicherSPDPStableCandidate_kernelGeneratorInvisible_noGo_of_chosenComplementGenerator_escape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hbad :
      exists (spdpKappa ell : Nat)
        (p : SATDeciderGaugeSpace M n hn2 htb hns)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ∧
        shift.totalDegree <= ell ∧
        shift.vars <= S.toFinset ∧
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ∧
        p ∈ routeBRicherSPDPStableCandidateProjectionComplement
          M n hn2 htb hns tail ∧
        routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∉
          routeBRicherSPDPStableCandidateProjectionComplement
            M n hn2 htb hns tail) :
    ¬ RouteBRicherSPDPStableCandidateKernelGeneratorInvisible
        M n hn2 htb hns tail := by
  intro hkernel
  exact
    routeBRicherSPDPStableCandidate_chosenComplementInvariant_noGo_of_chosenComplementGenerator_escape
      M n hn2 htb hns tail hbad
      ((routeBRicherSPDPStableCandidate_kernelGeneratorInvisible_iff_chosenComplementInvariant
        M n hn2 htb hns tail).mp hkernel)

/-- Empty-generator specialization of complement escape: if `mlProj` sends a
chosen-complement vector out of the chosen complement, residual invisibility
fails. -/
theorem routeBRicherSPDPStableCandidate_residualInvisible_noGo_of_chosenComplement_mlProj_escape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hbad :
      exists p : SATDeciderGaugeSpace M n hn2 htb hns,
        p ∈ routeBRicherSPDPStableCandidateProjectionComplement
          M n hn2 htb hns tail ∧
        mlProj p ∉ routeBRicherSPDPStableCandidateProjectionComplement
          M n hn2 htb hns tail) :
    ¬ RouteBRicherSPDPStableCandidateResidualInvisible
        M n hn2 htb hns tail := by
  apply
    routeBRicherSPDPStableCandidate_residualInvisible_noGo_of_chosenComplementGenerator_escape
      M n hn2 htb hns tail
  obtain ⟨p, hpComplement, hmlNotComplement⟩ := hbad
  refine ⟨0, 0, p,
    ([] : List (Fin (RouteBCookLevinDim M n hn2 htb hns))),
    (1 : SATDeciderGaugeSpace M n hn2 htb hns),
    by simp, by simp [MvPolynomial.totalDegree_one],
    by simp [MvPolynomial.vars_one], ?_, hpComplement, ?_⟩
  · constructor
    · simp
    · intro b; simp
  · intro hrowComplement
    exact hmlNotComplement
      (by
        simpa [routeBSPDPGeneratorRow, SPDP.iterDerivList, mlProj_one] using
          hrowComplement)

/-- No-go criterion (specialization to empty derivative list and constant
shift `1`): existence of `p` with `Π p = 0` but `Π(mlProj p) ≠ 0` refutes
`ResidualInvisible`.  This is the smaller-candidate analog of the
multilinear-tail diagonal no-go, weakened to the projection of the
multilinear part. -/
theorem routeBRicherSPDPStableCandidate_residualInvisible_noGo_of_kernel_mlProj_projection_ne_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hbad :
      exists p : SATDeciderGaugeSpace M n hn2 htb hns,
        routeBRicherSPDPStableCandidateProjection
          M n hn2 htb hns tail p = 0 ∧
        routeBRicherSPDPStableCandidateProjection
          M n hn2 htb hns tail (mlProj p) ≠ 0) :
    ¬ RouteBRicherSPDPStableCandidateResidualInvisible
        M n hn2 htb hns tail := by
  rcases hbad with ⟨p, hker, hne⟩
  apply
    routeBRicherSPDPStableCandidate_residualInvisible_noGo_of_kernelGenerator_ne_zero
      M n hn2 htb hns tail
  refine ⟨0, 0, p,
    ([] : List (Fin (RouteBCookLevinDim M n hn2 htb hns))),
    (1 : SATDeciderGaugeSpace M n hn2 htb hns),
    by simp, by simp [MvPolynomial.totalDegree_one],
    by simp [MvPolynomial.vars_one],
    ?_,
    hker, ?_⟩
  · -- admissibility for the empty derivative list
    constructor
    · simp
    · intro b; simp
  · -- gen p [] 1 = mlProj (1 * iterDerivList [] p) = mlProj p
    simpa [routeBSPDPGeneratorRow, SPDP.iterDerivList, mlProj_one] using hne

/-- Consequence: residual invisibility forces `mlProj p` into `Π`'s kernel
whenever `p` itself is in `Π`'s kernel.  This is the smaller-candidate
analog of `routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_implies_kernel_mlProj_zero`,
weakened from `mlProj p = 0` to `Π(mlProj p) = 0`. -/
theorem routeBRicherSPDPStableCandidate_residualInvisible_implies_kernel_mlProj_projection_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hinv :
      RouteBRicherSPDPStableCandidateResidualInvisible
        M n hn2 htb hns tail)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (hker :
      routeBRicherSPDPStableCandidateProjection
        M n hn2 htb hns tail p = 0) :
    routeBRicherSPDPStableCandidateProjection
        M n hn2 htb hns tail (mlProj p) = 0 := by
  have hker' :=
    (routeBRicherSPDPStableCandidate_residualInvisible_iff_kernelGeneratorInvisible
      M n hn2 htb hns tail).mp hinv
  have hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        ([] : List (Fin (RouteBCookLevinDim M n hn2 htb hns))) := by
    constructor
    · simp
    · intro b; simp
  have h :=
    hker' 0 0 p
      ([] : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
      (1 : SATDeciderGaugeSpace M n hn2 htb hns)
      (by simp) (by simp [MvPolynomial.totalDegree_one])
      (by simp [MvPolynomial.vars_one]) hadm hker
  simpa [routeBSPDPGeneratorRow, SPDP.iterDerivList, mlProj_one] using h

/-! ## Axiom audit anchors -/

#print axioms RouteBRicherSPDPStableCandidateKernelGeneratorInvisible
#print axioms routeBRicherSPDPStableCandidateGaugeWithComplement
#print axioms routeBRicherSPDPStableCandidateProjectionWithComplement
#print axioms routeBRicherSPDPStableCandidateProjectionWithComplement_apply_eq_zero_iff
#print axioms RouteBRicherSPDPStableCandidateExplicitComplementInvariant
#print axioms RouteBRicherSPDPStableCandidateKernelGeneratorInvisibleWithComplement
#print axioms routeBRicherSPDPStableCandidate_kernelGeneratorInvisibleWithComplement_iff_explicitComplementInvariant
#print axioms routeBRicherSPDPStableCandidate_explicitComplementInvariant_noGo_of_generator_escape
#print axioms routeBRicherSPDPStableCandidate_kernelGeneratorInvisibleWithComplement_noGo_of_generator_escape
#print axioms routeBRicherSPDPStableCandidate_projection_idempotent
#print axioms routeBRicherSPDPStableCandidate_residualInvisible_iff_kernelGeneratorInvisible
#print axioms routeBRicherSPDPStableCandidate_residualInvisible_noGo_of_kernelGenerator_ne_zero
#print axioms routeBRicherSPDPStableCandidate_residualInvisible_noGo_of_chosenComplementGenerator_escape
#print axioms routeBRicherSPDPStableCandidate_chosenComplementInvariant_noGo_of_chosenComplementGenerator_escape
#print axioms routeBRicherSPDPStableCandidate_kernelGeneratorInvisible_noGo_of_chosenComplementGenerator_escape
#print axioms routeBRicherSPDPStableCandidate_residualInvisible_noGo_of_chosenComplement_mlProj_escape
#print axioms routeBRicherSPDPStableCandidate_residualInvisible_noGo_of_kernel_mlProj_projection_ne_zero
#print axioms routeBRicherSPDPStableCandidate_residualInvisible_implies_kernel_mlProj_projection_zero

end PallLean.Paper93.Paper283
