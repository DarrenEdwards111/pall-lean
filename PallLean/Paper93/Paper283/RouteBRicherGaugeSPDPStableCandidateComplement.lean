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

end RouteBRicherSPDPStableCandidateProjectionComplementInterface

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

/-! ## Axiom audit anchors -/

#print axioms RouteBRicherSPDPStableCandidateProjectionComplementInterface
#print axioms RouteBRicherSPDPStableCandidateProjectionComplementInterface.gauge
#print axioms RouteBRicherSPDPStableCandidateProjectionComplementInterface.projection
#print axioms RouteBRicherSPDPStableCandidateProjectionComplementInterface.projection_apply_eq_zero_iff
#print axioms RouteBRicherSPDPStableCandidateProjectionComplementInterface.projection_idempotent
#print axioms RouteBRicherSPDPStableCandidateProjectionComplementInterface.kernelGeneratorInvisible_iff_explicitComplementInvariant
#print axioms RouteBRicherSPDPStableCandidateProjectionComplementInterface.explicitComplementInvariant_of_stableGeneratorMaps
#print axioms RouteBRicherSPDPStableCandidateProjectionComplementInterface.explicitComplementInvariant_of_projectionIntertwines
#print axioms routeBRicherSPDPStableCandidateBottomProjectionComplementInterface_of_rows_top
#print axioms routeBRicherSPDPStableCandidateChosenProjectionComplementInterface
#print axioms RouteBRicherSPDPStableCandidateExplicitComplementStableGeneratorMaps
#print axioms routeBRicherSPDPStableCandidate_explicitComplementInvariant_of_generatorRowLinearMap_maps_complement
#print axioms RouteBRicherSPDPStableCandidateExplicitComplementProjectionIntertwines
#print axioms routeBRicherSPDPStableCandidate_explicitComplementInvariant_of_projection_intertwines
#print axioms routeBRicherSPDPStableCandidate_generator_escape_of_projectionWithComplement_escape
#print axioms routeBRicherSPDPStableCandidate_explicitComplementInvariant_noGo_of_projectionWithComplement_escape
#print axioms routeBRicherSPDPStableCandidate_kernelGeneratorInvisibleWithComplement_noGo_of_projectionWithComplement_escape

end PallLean.Paper93.Paper283
