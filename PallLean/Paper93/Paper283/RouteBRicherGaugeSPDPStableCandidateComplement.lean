import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateNoGo
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPConcreteCoefficients

/-!
# Explicit-complement interfaces for the smaller SPDP-stable candidate

This file keeps the complement side separate from the no-go API.  It records
operator-level sufficient conditions for explicit complement invariance and
projection-level escape witnesses that can be consumed by the existing no-go
theorems without requiring callers to manually rewrite through the kernel
criterion.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Structural complement stability: every admissible generator-row linear map
sends the supplied complement `T` into itself. -/
def RouteBRicherSPDPStableCandidateExplicitComplementStableGeneratorMaps
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (_tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (T : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns)) : Prop :=
  forall (spdpKappa ell : Nat)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    Submodule.map
      (routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift) T <= T

/-- Direct linear-map stability of the complement proves the explicit
complement-invariance predicate used by the with-complement no-go API. -/
theorem routeBRicherSPDPStableCandidate_explicitComplementInvariant_of_generatorRowLinearMap_maps_complement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (T : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hstable :
      RouteBRicherSPDPStableCandidateExplicitComplementStableGeneratorMaps
        M n hn2 htb hns tail T) :
    RouteBRicherSPDPStableCandidateExplicitComplementInvariant
        M n hn2 htb hns tail T := by
  intro spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm hpT
  have hpMap :
      routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift p ∈
        Submodule.map
          (routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift) T := by
    exact ⟨p, hpT, rfl⟩
  have hsubset :=
    hstable spdpKappa ell S shift hSlen hshiftDegree hshiftVars hadm
  have hrowT := hsubset hpMap
  simpa [routeBSPDPGeneratorRowLinearMap_apply] using hrowT

/-- Projection-intertwining surface for an explicit complement: every
admissible generator-row operator descends through the explicit projection.
Since the complement is the kernel of this projection, such an intertwiner
forces complement invariance. -/
def RouteBRicherSPDPStableCandidateExplicitComplementProjectionIntertwines
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
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    exists A :
      SATDeciderGaugeSpace M n hn2 htb hns →ₗ[Rat]
        SATDeciderGaugeSpace M n hn2 htb hns,
      (routeBRicherSPDPStableCandidateProjectionWithComplement
          M n hn2 htb hns tail T hT).comp
        (routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift) =
      A.comp
        (routeBRicherSPDPStableCandidateProjectionWithComplement
          M n hn2 htb hns tail T hT)

/-- If the explicit projection intertwines every admissible generator-row
operator, then its kernel complement is invariant under those generators. -/
theorem routeBRicherSPDPStableCandidate_explicitComplementInvariant_of_projection_intertwines
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
    (hintertwines :
      RouteBRicherSPDPStableCandidateExplicitComplementProjectionIntertwines
        M n hn2 htb hns tail T hT) :
    RouteBRicherSPDPStableCandidateExplicitComplementInvariant
        M n hn2 htb hns tail T := by
  intro spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm hpT
  obtain ⟨A, hA⟩ :=
    hintertwines spdpKappa ell S shift
      hSlen hshiftDegree hshiftVars hadm
  have hpZero :
      routeBRicherSPDPStableCandidateProjectionWithComplement
          M n hn2 htb hns tail T hT p = 0 :=
    (routeBRicherSPDPStableCandidateProjectionWithComplement_apply_eq_zero_iff
      M n hn2 htb hns tail T hT p).mpr hpT
  have hrowZero :
      routeBRicherSPDPStableCandidateProjectionWithComplement
          M n hn2 htb hns tail T hT
          (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) = 0 := by
    have happ := congrArg (fun L =>
      L p) hA
    simpa [LinearMap.comp_apply, routeBSPDPGeneratorRowLinearMap_apply,
      hpZero] using happ
  exact
    (routeBRicherSPDPStableCandidateProjectionWithComplement_apply_eq_zero_iff
      M n hn2 htb hns tail T hT
      (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)).mp hrowZero

/-- Projection-escape witnesses are raw generator-escape witnesses for the
explicit complement, via the explicit projection's kernel criterion. -/
theorem routeBRicherSPDPStableCandidate_generator_escape_of_projectionWithComplement_escape
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
        routeBRicherSPDPStableCandidateProjectionWithComplement
          M n hn2 htb hns tail T hT
          (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) ≠ 0) :
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
        routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∉ T := by
  obtain ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hshiftVars, hadm, hpT, hprojNe⟩ := hbad
  refine ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hshiftVars, hadm, hpT, ?_⟩
  intro hrowT
  exact hprojNe
    ((routeBRicherSPDPStableCandidateProjectionWithComplement_apply_eq_zero_iff
      M n hn2 htb hns tail T hT
      (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)).mpr hrowT)

/-- Projection-escape form of the explicit-complement no-go theorem. -/
theorem routeBRicherSPDPStableCandidate_explicitComplementInvariant_noGo_of_projectionWithComplement_escape
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
        routeBRicherSPDPStableCandidateProjectionWithComplement
          M n hn2 htb hns tail T hT
          (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) ≠ 0) :
    ¬ RouteBRicherSPDPStableCandidateExplicitComplementInvariant
        M n hn2 htb hns tail T := by
  exact
    routeBRicherSPDPStableCandidate_explicitComplementInvariant_noGo_of_generator_escape
      M n hn2 htb hns tail T
      (routeBRicherSPDPStableCandidate_generator_escape_of_projectionWithComplement_escape
        M n hn2 htb hns tail T hT hbad)

/-- Projection-escape form of the explicit-complement kernel-invisibility
no-go theorem. -/
theorem routeBRicherSPDPStableCandidate_kernelGeneratorInvisibleWithComplement_noGo_of_projectionWithComplement_escape
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
        routeBRicherSPDPStableCandidateProjectionWithComplement
          M n hn2 htb hns tail T hT
          (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) ≠ 0) :
    ¬ RouteBRicherSPDPStableCandidateKernelGeneratorInvisibleWithComplement
        M n hn2 htb hns tail T hT := by
  exact
    routeBRicherSPDPStableCandidate_kernelGeneratorInvisibleWithComplement_noGo_of_generator_escape
      M n hn2 htb hns tail T hT
      (routeBRicherSPDPStableCandidate_generator_escape_of_projectionWithComplement_escape
        M n hn2 htb hns tail T hT hbad)

/-! ## Bundled explicit-complement interface -/

/-- The finite row span for the smaller SPDP-stable candidate.  Naming this
submodule keeps the explicit projection data below inspectable: the range
target is exactly this span, and the supplied complement is its kernel. -/
noncomputable abbrev RouteBRicherSPDPStableCandidateRowSpan
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns) :=
  finiteRowsSubmodule
    (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail)

/-- A caller-supplied complement for the smaller SPDP-stable candidate, bundled
with the proof that it complements the finite span of the prepended candidate
rows.  This is the inspectable alternative to the legacy
`Classical.choose` complement. -/
structure RouteBRicherSPDPStableCandidateProjectionComplementInterface
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    Type where
  complement : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns)
  isCompl :
    IsCompl
      (finiteRowsSubmodule
        (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail))
      complement

namespace RouteBRicherSPDPStableCandidateProjectionComplementInterface

/-- Candidate gauge built from a bundled explicit complement. -/
noncomputable def gauge
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns tail) :
    PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidateGaugeWithComplement
    M n hn2 htb hns tail I.complement I.isCompl

/-- SAT-side projection built from a bundled explicit complement. -/
noncomputable def projection
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns tail) :
    SATDeciderGaugeSpace M n hn2 htb hns →ₗ[Rat]
      SATDeciderGaugeSpace M n hn2 htb hns :=
  routeBRicherSPDPStableCandidateProjectionWithComplement
    M n hn2 htb hns tail I.complement I.isCompl

/-- Zero criterion for the projection attached to a bundled explicit
complement. -/
theorem projection_apply_eq_zero_iff
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns tail)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    I.projection p = 0 ↔ p ∈ I.complement := by
  simpa [projection] using
    routeBRicherSPDPStableCandidateProjectionWithComplement_apply_eq_zero_iff
      M n hn2 htb hns tail I.complement I.isCompl p

/-- Idempotency of the projection attached to a bundled explicit complement. -/
theorem projection_idempotent
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns tail)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    I.projection (I.projection p) = I.projection p := by
  have hidem := I.gauge.is_idempotent
  have happ := congrArg (fun L => L p) hidem
  simpa [projection, gauge, LinearMap.comp_apply] using happ

/-- Idempotency of the bundled projection, as a linear-map equation. -/
theorem projection_comp_idempotent
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns tail) :
    I.projection.comp I.projection = I.projection := by
  apply LinearMap.ext
  intro p
  simpa [LinearMap.comp_apply] using I.projection_idempotent p

/-- The bundled projection has range equal to the finite row span. -/
theorem projection_range
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns tail) :
    LinearMap.range I.projection =
      RouteBRicherSPDPStableCandidateRowSpan M n hn2 htb hns tail := by
  simpa [projection, RouteBRicherSPDPStableCandidateRowSpan,
    routeBRicherSPDPStableCandidateProjectionWithComplement,
    routeBRicherSPDPStableCandidateGaugeWithComplement] using
    routeBRicherFiniteRowsCandidateGaugeWithComplement_range
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail)
      I.complement I.isCompl

/-- The bundled projection has kernel equal to the bundled complement. -/
theorem projection_ker
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns tail) :
    LinearMap.ker I.projection = I.complement := by
  ext p
  change I.projection p = 0 ↔ p ∈ I.complement
  exact I.projection_apply_eq_zero_iff p

/-- The bundled projection fixes every vector in the finite row span. -/
theorem projection_fixes_of_mem_rowSpan
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns tail)
    {p : SATDeciderGaugeSpace M n hn2 htb hns}
    (hp :
      p ∈ RouteBRicherSPDPStableCandidateRowSpan
        M n hn2 htb hns tail) :
    I.projection p = p := by
  have hpRange : p ∈ LinearMap.range I.projection := by
    rw [I.projection_range]
    exact hp
  rcases hpRange with ⟨q, rfl⟩
  exact I.projection_idempotent q

/-- The bundled projection fixes each prepended finite row. -/
theorem projection_fixes_row
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns tail)
    (i : Fin (m + 1)) :
    I.projection
        (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail i) =
      routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail i :=
  I.projection_fixes_of_mem_rowSpan
    (Submodule.subset_span ⟨i, rfl⟩)

/-- Kernel invisibility for the bundled projection is exactly invariance of
the bundled complement under admissible generator rows. -/
theorem kernelGeneratorInvisible_iff_explicitComplementInvariant
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateKernelGeneratorInvisibleWithComplement
        M n hn2 htb hns tail I.complement I.isCompl ↔
      RouteBRicherSPDPStableCandidateExplicitComplementInvariant
        M n hn2 htb hns tail I.complement :=
  routeBRicherSPDPStableCandidate_kernelGeneratorInvisibleWithComplement_iff_explicitComplementInvariant
    M n hn2 htb hns tail I.complement I.isCompl

/-- Operator stability of the bundled complement proves the pointwise
explicit-complement invariant. -/
theorem explicitComplementInvariant_of_stableGeneratorMaps
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns tail)
    (hstable :
      RouteBRicherSPDPStableCandidateExplicitComplementStableGeneratorMaps
        M n hn2 htb hns tail I.complement) :
    RouteBRicherSPDPStableCandidateExplicitComplementInvariant
      M n hn2 htb hns tail I.complement :=
  routeBRicherSPDPStableCandidate_explicitComplementInvariant_of_generatorRowLinearMap_maps_complement
    M n hn2 htb hns tail I.complement hstable

/-- Projection intertwining for the bundled explicit projection proves the
pointwise explicit-complement invariant. -/
theorem explicitComplementInvariant_of_projectionIntertwines
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns tail)
    (hintertwines :
      RouteBRicherSPDPStableCandidateExplicitComplementProjectionIntertwines
        M n hn2 htb hns tail I.complement I.isCompl) :
    RouteBRicherSPDPStableCandidateExplicitComplementInvariant
      M n hn2 htb hns tail I.complement :=
  routeBRicherSPDPStableCandidate_explicitComplementInvariant_of_projection_intertwines
    M n hn2 htb hns tail I.complement I.isCompl hintertwines

/-- Descent of every admissible generator-row map through the bundled
projection: `Pi ∘ L = Pi ∘ L ∘ Pi`. -/
def ProjectionDescent
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns tail) : Prop :=
  forall (spdpKappa ell : Nat)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    let Pi := I.projection
    let L := routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift
    Pi.comp L = (Pi.comp L).comp Pi

/-- Escape witness stated directly against the bundled projection. -/
def ProjectionEscapeWitness
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns tail) : Prop :=
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
    I.projection
      (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) ≠ 0

/-- Descent through the bundled projection is equivalent to the older
projection-intertwining surface. -/
theorem projectionDescent_iff_projectionIntertwines
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns tail) :
    I.ProjectionDescent ↔
      RouteBRicherSPDPStableCandidateExplicitComplementProjectionIntertwines
        M n hn2 htb hns tail I.complement I.isCompl := by
  constructor
  · intro hdescent spdpKappa ell S shift hSlen hshiftDegree hshiftVars hadm
    refine ⟨I.projection.comp
      (routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift), ?_⟩
    simpa [ProjectionDescent, projection] using
      hdescent spdpKappa ell S shift
        hSlen hshiftDegree hshiftVars hadm
  · intro hintertwines spdpKappa ell S shift
      hSlen hshiftDegree hshiftVars hadm
    let Pi := I.projection
    let L := routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift
    obtain ⟨A, hA⟩ :=
      hintertwines spdpKappa ell S shift
        hSlen hshiftDegree hshiftVars hadm
    have hA' : Pi.comp L = A.comp Pi := by
      simpa [Pi, L, projection] using hA
    have hidem : Pi.comp Pi = Pi := by
      simpa [Pi] using I.projection_comp_idempotent
    calc
      Pi.comp L = A.comp Pi := hA'
      _ = (A.comp Pi).comp Pi := by
        apply LinearMap.ext
        intro p
        have hPiPi : Pi (Pi p) = Pi p := by
          have happ := congrArg (fun F => F p) hidem
          simpa [LinearMap.comp_apply] using happ
        simp [LinearMap.comp_apply, hPiPi]
      _ = (Pi.comp L).comp Pi := by rw [hA']

/-- Descent through the bundled projection is exactly invariance of the
bundled complement. -/
theorem projectionDescent_iff_explicitComplementInvariant
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns tail) :
    I.ProjectionDescent ↔
      RouteBRicherSPDPStableCandidateExplicitComplementInvariant
        M n hn2 htb hns tail I.complement := by
  constructor
  · intro hdescent spdpKappa ell p S shift
      hSlen hshiftDegree hshiftVars hadm hpComplement
    let Pi := I.projection
    let L := routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift
    have hpZero : Pi p = 0 := by
      simpa [Pi] using (I.projection_apply_eq_zero_iff p).mpr hpComplement
    have hdesc : Pi.comp L = (Pi.comp L).comp Pi := by
      simpa [ProjectionDescent, Pi, L] using
        hdescent spdpKappa ell S shift
          hSlen hshiftDegree hshiftVars hadm
    have hrowZero :
        Pi (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) = 0 := by
      have happ := congrArg (fun F => F p) hdesc
      have hrowZeroL : Pi (L p) = 0 := by
        simpa [LinearMap.comp_apply, hpZero] using happ
      simpa [Pi, L, routeBSPDPGeneratorRowLinearMap_apply] using hrowZeroL
    exact
      (I.projection_apply_eq_zero_iff
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)).mp
        (by simpa [Pi] using hrowZero)
  · intro hinvariant spdpKappa ell S shift
      hSlen hshiftDegree hshiftVars hadm
    let Pi := I.projection
    let L := routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift
    apply LinearMap.ext
    intro p
    have hPiPi : Pi (Pi p) = Pi p := by
      simpa [Pi] using I.projection_idempotent p
    have hresZero : Pi (p - Pi p) = 0 := by
      simp [Pi, map_sub, hPiPi]
    have hresComplement : p - Pi p ∈ I.complement :=
      (I.projection_apply_eq_zero_iff (p - Pi p)).mp
        (by simpa [Pi] using hresZero)
    have hrowComplement :
        routeBSPDPGeneratorRow M n hn2 htb hns (p - Pi p) S shift ∈
          I.complement :=
      hinvariant spdpKappa ell (p - Pi p) S shift
        hSlen hshiftDegree hshiftVars hadm hresComplement
    have hrowZero : Pi (L (p - Pi p)) = 0 := by
      have hzero :=
        (I.projection_apply_eq_zero_iff
          (routeBSPDPGeneratorRow M n hn2 htb hns
            (p - Pi p) S shift)).mpr hrowComplement
      simpa [Pi, L, routeBSPDPGeneratorRowLinearMap_apply] using hzero
    have hmapSub : Pi (L p - L (Pi p)) = 0 := by
      simpa [map_sub] using hrowZero
    have hsubZero : Pi (L p) - Pi (L (Pi p)) = 0 := by
      simpa [map_sub] using hmapSub
    have hpoint : Pi (L p) = Pi (L (Pi p)) := sub_eq_zero.mp hsubZero
    simpa [ProjectionDescent, Pi, L, LinearMap.comp_apply] using hpoint

/-- Projection escape is exactly failure of descent through the bundled
projection. -/
theorem projectionEscapeWitness_iff_not_projectionDescent
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns tail) :
    I.ProjectionEscapeWitness ↔ ¬ I.ProjectionDescent := by
  constructor
  · intro hbad hdescent
    obtain ⟨spdpKappa, ell, p, S, shift,
      hSlen, hshiftDegree, hshiftVars, hadm, hpComplement,
      hprojNe⟩ := hbad
    have hinvariant :=
      (I.projectionDescent_iff_explicitComplementInvariant).mp hdescent
    have hrowComplement :=
      hinvariant spdpKappa ell p S shift
        hSlen hshiftDegree hshiftVars hadm hpComplement
    exact hprojNe
      ((I.projection_apply_eq_zero_iff
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)).mpr
        hrowComplement)
  · intro hnot
    classical
    by_contra hno
    apply hnot
    apply (I.projectionDescent_iff_explicitComplementInvariant).mpr
    intro spdpKappa ell p S shift
      hSlen hshiftDegree hshiftVars hadm hpComplement
    by_contra hrowNotComplement
    have hprojNe :
        I.projection
          (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) ≠ 0 := by
      intro hzero
      exact hrowNotComplement
        ((I.projection_apply_eq_zero_iff
          (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)).mp hzero)
    exact hno ⟨spdpKappa, ell, p, S, shift,
      hSlen, hshiftDegree, hshiftVars, hadm, hpComplement, hprojNe⟩

/-- Bundled projection escape is the projection-with-complement escape shape
consumed by the existing no-go theorem. -/
theorem projectionWithComplement_escape_of_projectionEscapeWitness
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns tail)
    (hbad : I.ProjectionEscapeWitness) :
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
        M n hn2 htb hns tail I.complement I.isCompl
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) ≠ 0 := by
  simpa [ProjectionEscapeWitness, projection] using hbad

/-- Bundled projection escape refutes invariance of the same inspectable
complement. -/
theorem explicitComplementInvariant_noGo_of_projectionEscapeWitness
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns tail)
    (hbad : I.ProjectionEscapeWitness) :
    ¬ RouteBRicherSPDPStableCandidateExplicitComplementInvariant
        M n hn2 htb hns tail I.complement := by
  exact
    routeBRicherSPDPStableCandidate_explicitComplementInvariant_noGo_of_projectionWithComplement_escape
      M n hn2 htb hns tail I.complement I.isCompl
      (I.projectionWithComplement_escape_of_projectionEscapeWitness hbad)

/-- Bundled projection escape refutes kernel-generator invisibility for the
same inspectable projection. -/
theorem kernelGeneratorInvisibleWithComplement_noGo_of_projectionEscapeWitness
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns tail)
    (hbad : I.ProjectionEscapeWitness) :
    ¬ RouteBRicherSPDPStableCandidateKernelGeneratorInvisibleWithComplement
        M n hn2 htb hns tail I.complement I.isCompl := by
  exact
    routeBRicherSPDPStableCandidate_kernelGeneratorInvisibleWithComplement_noGo_of_projectionWithComplement_escape
      M n hn2 htb hns tail I.complement I.isCompl
      (I.projectionWithComplement_escape_of_projectionEscapeWitness hbad)

end RouteBRicherSPDPStableCandidateProjectionComplementInterface

/-! ## Inspectable projection data -/

/-- Fully inspectable projection data for the smaller SPDP-stable candidate.

This package is stronger than merely providing a complement: callers supply
the actual projection map, prove it is idempotent, prove its range is exactly
the finite row span, and prove its kernel is exactly the displayed complement.
The `isCompl` proof needed by the legacy with-complement API is then derived
from these fields rather than chosen by `Classical.choose`. -/
structure RouteBRicherSPDPStableCandidateExplicitProjectionData
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    Type where
  complement : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns)
  projection :
    SATDeciderGaugeSpace M n hn2 htb hns →ₗ[Rat]
      SATDeciderGaugeSpace M n hn2 htb hns
  projection_idempotent : projection.comp projection = projection
  projection_range :
    LinearMap.range projection =
      RouteBRicherSPDPStableCandidateRowSpan M n hn2 htb hns tail
  projection_ker :
    LinearMap.ker projection = complement

namespace RouteBRicherSPDPStableCandidateExplicitProjectionData

/-- The supplied projection is an idempotent element of the endomorphism ring. -/
theorem projection_isIdempotentElem
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (D :
      RouteBRicherSPDPStableCandidateExplicitProjectionData
        M n hn2 htb hns tail) :
    IsIdempotentElem D.projection := by
  change D.projection * D.projection = D.projection
  simpa using D.projection_idempotent

/-- The range/kernel fields produce the complement proof required by the
with-complement API. -/
theorem isCompl
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (D :
      RouteBRicherSPDPStableCandidateExplicitProjectionData
        M n hn2 htb hns tail) :
    IsCompl
      (RouteBRicherSPDPStableCandidateRowSpan M n hn2 htb hns tail)
      D.complement := by
  rw [← D.projection_range, ← D.projection_ker]
  exact LinearMap.IsIdempotentElem.isCompl D.projection_isIdempotentElem

/-- Convert fully inspectable projection data to the existing complement
interface. -/
def toComplementInterface
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (D :
      RouteBRicherSPDPStableCandidateExplicitProjectionData
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateProjectionComplementInterface
      M n hn2 htb hns tail where
  complement := D.complement
  isCompl := by
    simpa [RouteBRicherSPDPStableCandidateRowSpan] using D.isCompl

/-- Kernel criterion for the supplied projection map. -/
theorem projection_apply_eq_zero_iff
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (D :
      RouteBRicherSPDPStableCandidateExplicitProjectionData
        M n hn2 htb hns tail)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    D.projection p = 0 ↔ p ∈ D.complement := by
  change p ∈ LinearMap.ker D.projection ↔ p ∈ D.complement
  rw [D.projection_ker]

/-- Pointwise idempotency of the supplied projection map. -/
theorem projection_idempotent_apply
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (D :
      RouteBRicherSPDPStableCandidateExplicitProjectionData
        M n hn2 htb hns tail)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    D.projection (D.projection p) = D.projection p := by
  have happ := congrArg (fun L => L p) D.projection_idempotent
  simpa [LinearMap.comp_apply] using happ

/-- The supplied projection fixes every vector in the finite row span. -/
theorem projection_fixes_of_mem_rowSpan
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (D :
      RouteBRicherSPDPStableCandidateExplicitProjectionData
        M n hn2 htb hns tail)
    {p : SATDeciderGaugeSpace M n hn2 htb hns}
    (hp :
      p ∈ RouteBRicherSPDPStableCandidateRowSpan
        M n hn2 htb hns tail) :
    D.projection p = p := by
  have hpRange : p ∈ LinearMap.range D.projection := by
    rw [D.projection_range]
    exact hp
  rcases hpRange with ⟨q, rfl⟩
  exact D.projection_idempotent_apply q

/-- The supplied projection fixes each prepended finite row. -/
theorem projection_fixes_row
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (D :
      RouteBRicherSPDPStableCandidateExplicitProjectionData
        M n hn2 htb hns tail)
    (i : Fin (m + 1)) :
    D.projection
        (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail i) =
      routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail i :=
  D.projection_fixes_of_mem_rowSpan
    (Submodule.subset_span ⟨i, rfl⟩)

/-- Repackage an existing complement interface as explicit projection data by
using its attached projection map. -/
noncomputable def ofComplementInterface
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (I :
      RouteBRicherSPDPStableCandidateProjectionComplementInterface
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateExplicitProjectionData
      M n hn2 htb hns tail where
  complement := I.complement
  projection := I.projection
  projection_idempotent := I.projection_comp_idempotent
  projection_range := I.projection_range
  projection_ker := I.projection_ker

/-- Descent through a caller-supplied projection map. -/
def ProjectionDescent
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (D :
      RouteBRicherSPDPStableCandidateExplicitProjectionData
        M n hn2 htb hns tail) : Prop :=
  forall (spdpKappa ell : Nat)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    let Pi := D.projection
    let L := routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift
    Pi.comp L = (Pi.comp L).comp Pi

/-- Escape witness stated directly against a caller-supplied projection map. -/
def ProjectionEscapeWitness
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (D :
      RouteBRicherSPDPStableCandidateExplicitProjectionData
        M n hn2 htb hns tail) : Prop :=
  exists (spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ∧
    shift.totalDegree <= ell ∧
    shift.vars <= S.toFinset ∧
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ∧
    p ∈ D.complement ∧
    D.projection
      (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) ≠ 0

/-- Descent through the supplied projection is exactly invariance of its
displayed kernel complement. -/
theorem projectionDescent_iff_explicitComplementInvariant
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (D :
      RouteBRicherSPDPStableCandidateExplicitProjectionData
        M n hn2 htb hns tail) :
    D.ProjectionDescent ↔
      RouteBRicherSPDPStableCandidateExplicitComplementInvariant
        M n hn2 htb hns tail D.complement := by
  constructor
  · intro hdescent spdpKappa ell p S shift
      hSlen hshiftDegree hshiftVars hadm hpComplement
    let Pi := D.projection
    let L := routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift
    have hpZero : Pi p = 0 := by
      simpa [Pi] using (D.projection_apply_eq_zero_iff p).mpr hpComplement
    have hdesc : Pi.comp L = (Pi.comp L).comp Pi := by
      simpa [ProjectionDescent, Pi, L] using
        hdescent spdpKappa ell S shift
          hSlen hshiftDegree hshiftVars hadm
    have hrowZero :
        Pi (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) = 0 := by
      have happ := congrArg (fun F => F p) hdesc
      have hrowZeroL : Pi (L p) = 0 := by
        simpa [LinearMap.comp_apply, hpZero] using happ
      simpa [Pi, L, routeBSPDPGeneratorRowLinearMap_apply] using hrowZeroL
    exact
      (D.projection_apply_eq_zero_iff
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)).mp
        (by simpa [Pi] using hrowZero)
  · intro hinvariant spdpKappa ell S shift
      hSlen hshiftDegree hshiftVars hadm
    let Pi := D.projection
    let L := routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift
    apply LinearMap.ext
    intro p
    have hPiPi : Pi (Pi p) = Pi p := by
      simpa [Pi] using D.projection_idempotent_apply p
    have hresZero : Pi (p - Pi p) = 0 := by
      simp [Pi, map_sub, hPiPi]
    have hresComplement : p - Pi p ∈ D.complement :=
      (D.projection_apply_eq_zero_iff (p - Pi p)).mp
        (by simpa [Pi] using hresZero)
    have hrowComplement :
        routeBSPDPGeneratorRow M n hn2 htb hns (p - Pi p) S shift ∈
          D.complement :=
      hinvariant spdpKappa ell (p - Pi p) S shift
        hSlen hshiftDegree hshiftVars hadm hresComplement
    have hrowZero : Pi (L (p - Pi p)) = 0 := by
      have hzero :=
        (D.projection_apply_eq_zero_iff
          (routeBSPDPGeneratorRow M n hn2 htb hns
            (p - Pi p) S shift)).mpr hrowComplement
      simpa [Pi, L, routeBSPDPGeneratorRowLinearMap_apply] using hzero
    have hmapSub : Pi (L p - L (Pi p)) = 0 := by
      simpa [map_sub] using hrowZero
    have hsubZero : Pi (L p) - Pi (L (Pi p)) = 0 := by
      simpa [map_sub] using hmapSub
    have hpoint : Pi (L p) = Pi (L (Pi p)) := sub_eq_zero.mp hsubZero
    simpa [ProjectionDescent, Pi, L, LinearMap.comp_apply] using hpoint

/-- Projection escape is exactly failure of descent through the supplied
projection map. -/
theorem projectionEscapeWitness_iff_not_projectionDescent
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (D :
      RouteBRicherSPDPStableCandidateExplicitProjectionData
        M n hn2 htb hns tail) :
    D.ProjectionEscapeWitness ↔ ¬ D.ProjectionDescent := by
  constructor
  · intro hbad hdescent
    obtain ⟨spdpKappa, ell, p, S, shift,
      hSlen, hshiftDegree, hshiftVars, hadm, hpComplement,
      hprojNe⟩ := hbad
    have hinvariant :=
      (D.projectionDescent_iff_explicitComplementInvariant).mp hdescent
    have hrowComplement :=
      hinvariant spdpKappa ell p S shift
        hSlen hshiftDegree hshiftVars hadm hpComplement
    exact hprojNe
      ((D.projection_apply_eq_zero_iff
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)).mpr
        hrowComplement)
  · intro hnot
    classical
    by_contra hno
    apply hnot
    apply (D.projectionDescent_iff_explicitComplementInvariant).mpr
    intro spdpKappa ell p S shift
      hSlen hshiftDegree hshiftVars hadm hpComplement
    by_contra hrowNotComplement
    have hprojNe :
        D.projection
          (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) ≠ 0 := by
      intro hzero
      exact hrowNotComplement
        ((D.projection_apply_eq_zero_iff
          (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)).mp hzero)
    exact hno ⟨spdpKappa, ell, p, S, shift,
      hSlen, hshiftDegree, hshiftVars, hadm, hpComplement, hprojNe⟩

/-- Descent for the canonical with-complement projection is equivalent to
descent for the supplied projection data. -/
theorem toComplementInterface_projectionDescent_iff
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (D :
      RouteBRicherSPDPStableCandidateExplicitProjectionData
        M n hn2 htb hns tail) :
    D.toComplementInterface.ProjectionDescent ↔ D.ProjectionDescent := by
  rw [
    RouteBRicherSPDPStableCandidateProjectionComplementInterface.projectionDescent_iff_explicitComplementInvariant,
    D.projectionDescent_iff_explicitComplementInvariant]
  simp [toComplementInterface]

/-- Escape for supplied projection data gives escape for the canonical
projection attached to the derived complement interface. -/
theorem toComplementInterface_projectionEscapeWitness_of_projectionEscapeWitness
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (D :
      RouteBRicherSPDPStableCandidateExplicitProjectionData
        M n hn2 htb hns tail)
    (hbad : D.ProjectionEscapeWitness) :
    D.toComplementInterface.ProjectionEscapeWitness := by
  obtain ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hshiftVars, hadm, hpComplement,
    hprojNe⟩ := hbad
  refine ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hshiftVars, hadm, hpComplement, ?_⟩
  intro hcanonicalZero
  have hrowComplement :
      routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∈ D.complement := by
    simpa [toComplementInterface] using
      (D.toComplementInterface.projection_apply_eq_zero_iff
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)).mp
        hcanonicalZero
  exact hprojNe
    ((D.projection_apply_eq_zero_iff
      (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)).mpr
      hrowComplement)

/-- Supplied projection escape refutes invariance of its displayed
complement. -/
theorem explicitComplementInvariant_noGo_of_projectionEscapeWitness
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (D :
      RouteBRicherSPDPStableCandidateExplicitProjectionData
        M n hn2 htb hns tail)
    (hbad : D.ProjectionEscapeWitness) :
    ¬ RouteBRicherSPDPStableCandidateExplicitComplementInvariant
        M n hn2 htb hns tail D.complement := by
  simpa [toComplementInterface] using
    D.toComplementInterface.explicitComplementInvariant_noGo_of_projectionEscapeWitness
      (D.toComplementInterface_projectionEscapeWitness_of_projectionEscapeWitness hbad)

/-- Supplied projection escape refutes kernel-generator invisibility for the
derived with-complement projection. -/
theorem kernelGeneratorInvisibleWithComplement_noGo_of_projectionEscapeWitness
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {m : Nat} {tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns}
    (D :
      RouteBRicherSPDPStableCandidateExplicitProjectionData
        M n hn2 htb hns tail)
    (hbad : D.ProjectionEscapeWitness) :
    ¬ RouteBRicherSPDPStableCandidateKernelGeneratorInvisibleWithComplement
        M n hn2 htb hns tail D.complement D.toComplementInterface.isCompl := by
  exact
    D.toComplementInterface.kernelGeneratorInvisibleWithComplement_noGo_of_projectionEscapeWitness
      (D.toComplementInterface_projectionEscapeWitness_of_projectionEscapeWitness hbad)

end RouteBRicherSPDPStableCandidateExplicitProjectionData

/-- If the caller has proved that the prepended rows already span the whole
ambient SAT gauge space, the inspectable complement is `⊥`. -/
def routeBRicherSPDPStableCandidateBottomProjectionComplementInterface_of_rows_top
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hrowsTop :
      finiteRowsSubmodule
        (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail) = ⊤) :
    RouteBRicherSPDPStableCandidateProjectionComplementInterface
      M n hn2 htb hns tail where
  complement := ⊥
  isCompl := by
    simpa [hrowsTop] using
      (isCompl_top_bot :
        IsCompl
          (⊤ : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
          (⊥ : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns)))

/-- If the prepended rows span the whole ambient SAT gauge space, the fully
inspectable projection data is the identity projection with complement `⊥`. -/
def routeBRicherSPDPStableCandidateBottomExplicitProjectionData_of_rows_top
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hrowsTop :
      RouteBRicherSPDPStableCandidateRowSpan
        M n hn2 htb hns tail = ⊤) :
    RouteBRicherSPDPStableCandidateExplicitProjectionData
      M n hn2 htb hns tail where
  complement := ⊥
  projection := LinearMap.id
  projection_idempotent := by simp
  projection_range := by
    simp [hrowsTop]
  projection_ker := by simp

/-- The legacy chosen complement, repackaged as an explicit-complement
interface.  This keeps old projection statements compatible while allowing new
proofs to abstract over a caller-supplied complement. -/
noncomputable def routeBRicherSPDPStableCandidateChosenProjectionComplementInterface
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateProjectionComplementInterface
      M n hn2 htb hns tail where
  complement :=
    routeBRicherSPDPStableCandidateProjectionComplement
      M n hn2 htb hns tail
  isCompl := by
    simpa [routeBRicherSPDPStableCandidateProjectionComplement] using
      finiteSubmoduleProjection_isCompl
        (finiteRowsSubmodule
          (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail))

/-- The legacy chosen complement, repackaged as fully explicit projection data.
This is still noncomputable because the complement itself is chosen by the
finite-submodule projection API; the range, kernel, and idempotence fields are
now exposed for audit. -/
noncomputable def routeBRicherSPDPStableCandidateChosenExplicitProjectionData
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateExplicitProjectionData
      M n hn2 htb hns tail :=
  RouteBRicherSPDPStableCandidateExplicitProjectionData.ofComplementInterface
    (routeBRicherSPDPStableCandidateChosenProjectionComplementInterface
      M n hn2 htb hns tail)

/-! ## Axiom audit anchors -/

#print axioms RouteBRicherSPDPStableCandidateRowSpan
#print axioms RouteBRicherSPDPStableCandidateProjectionComplementInterface
#print axioms RouteBRicherSPDPStableCandidateProjectionComplementInterface.gauge
#print axioms RouteBRicherSPDPStableCandidateProjectionComplementInterface.projection
#print axioms RouteBRicherSPDPStableCandidateProjectionComplementInterface.projection_apply_eq_zero_iff
#print axioms RouteBRicherSPDPStableCandidateProjectionComplementInterface.projection_idempotent
#print axioms RouteBRicherSPDPStableCandidateProjectionComplementInterface.projection_range
#print axioms RouteBRicherSPDPStableCandidateProjectionComplementInterface.projection_ker
#print axioms RouteBRicherSPDPStableCandidateProjectionComplementInterface.projection_fixes_row
#print axioms RouteBRicherSPDPStableCandidateProjectionComplementInterface.kernelGeneratorInvisible_iff_explicitComplementInvariant
#print axioms RouteBRicherSPDPStableCandidateProjectionComplementInterface.explicitComplementInvariant_of_stableGeneratorMaps
#print axioms RouteBRicherSPDPStableCandidateProjectionComplementInterface.explicitComplementInvariant_of_projectionIntertwines
#print axioms RouteBRicherSPDPStableCandidateProjectionComplementInterface.ProjectionDescent
#print axioms RouteBRicherSPDPStableCandidateProjectionComplementInterface.ProjectionEscapeWitness
#print axioms RouteBRicherSPDPStableCandidateProjectionComplementInterface.projectionDescent_iff_projectionIntertwines
#print axioms RouteBRicherSPDPStableCandidateProjectionComplementInterface.projectionDescent_iff_explicitComplementInvariant
#print axioms RouteBRicherSPDPStableCandidateProjectionComplementInterface.projectionEscapeWitness_iff_not_projectionDescent
#print axioms RouteBRicherSPDPStableCandidateExplicitProjectionData
#print axioms RouteBRicherSPDPStableCandidateExplicitProjectionData.isCompl
#print axioms RouteBRicherSPDPStableCandidateExplicitProjectionData.toComplementInterface
#print axioms RouteBRicherSPDPStableCandidateExplicitProjectionData.projection_apply_eq_zero_iff
#print axioms RouteBRicherSPDPStableCandidateExplicitProjectionData.projection_fixes_row
#print axioms RouteBRicherSPDPStableCandidateExplicitProjectionData.ofComplementInterface
#print axioms RouteBRicherSPDPStableCandidateExplicitProjectionData.ProjectionDescent
#print axioms RouteBRicherSPDPStableCandidateExplicitProjectionData.ProjectionEscapeWitness
#print axioms RouteBRicherSPDPStableCandidateExplicitProjectionData.projectionDescent_iff_explicitComplementInvariant
#print axioms RouteBRicherSPDPStableCandidateExplicitProjectionData.projectionEscapeWitness_iff_not_projectionDescent
#print axioms RouteBRicherSPDPStableCandidateExplicitProjectionData.toComplementInterface_projectionDescent_iff
#print axioms RouteBRicherSPDPStableCandidateExplicitProjectionData.toComplementInterface_projectionEscapeWitness_of_projectionEscapeWitness
#print axioms routeBRicherSPDPStableCandidateBottomProjectionComplementInterface_of_rows_top
#print axioms routeBRicherSPDPStableCandidateBottomExplicitProjectionData_of_rows_top
#print axioms routeBRicherSPDPStableCandidateChosenProjectionComplementInterface
#print axioms routeBRicherSPDPStableCandidateChosenExplicitProjectionData
#print axioms RouteBRicherSPDPStableCandidateExplicitComplementStableGeneratorMaps
#print axioms routeBRicherSPDPStableCandidate_explicitComplementInvariant_of_generatorRowLinearMap_maps_complement
#print axioms RouteBRicherSPDPStableCandidateExplicitComplementProjectionIntertwines
#print axioms routeBRicherSPDPStableCandidate_explicitComplementInvariant_of_projection_intertwines
#print axioms routeBRicherSPDPStableCandidate_generator_escape_of_projectionWithComplement_escape
#print axioms routeBRicherSPDPStableCandidate_explicitComplementInvariant_noGo_of_projectionWithComplement_escape
#print axioms routeBRicherSPDPStableCandidate_kernelGeneratorInvisibleWithComplement_noGo_of_projectionWithComplement_escape

end PallLean.Paper93.Paper283
