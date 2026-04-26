import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateComplement
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadCover

/-!
# Complement interfaces for the log-window head-span tail

This file keeps the head-span/profile-tail complement question additive.  The
finite projection chooses its complement noncomputably, so the useful concrete
surface is the exact operator condition that every log-window admissible
generator linear map preserves that chosen complement.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Log-window linear-map stability of the finite projection's chosen
complement.  This is the operator form of
`RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant`. -/
def RouteBRicherSPDPStableCandidateLogWindowChosenComplementStableGeneratorMaps
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) : Prop :=
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
    Submodule.map
      (routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift)
      (routeBRicherSPDPStableCandidateProjectionComplement
        M n hn2 htb hns tail) <=
    routeBRicherSPDPStableCandidateProjectionComplement
      M n hn2 htb hns tail

/-- The log-window pointwise complement-invariance predicate is equivalent to
the corresponding log-window operator stability of the chosen complement. -/
theorem routeBRicherSPDPStableCandidate_logWindowChosenComplementInvariant_iff_stableGeneratorMaps
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
        M n hn2 htb hns tail ↔
      RouteBRicherSPDPStableCandidateLogWindowChosenComplementStableGeneratorMaps
        M n hn2 htb hns tail := by
  constructor
  · intro hinvariant spdpKappa ell S shift hSlen hshiftDegree hSlog
      hshiftLog hshiftVars hadm row hrow
    rcases hrow with ⟨p, hpComplement, rfl⟩
    simpa [routeBSPDPGeneratorRowLinearMap_apply] using
      hinvariant spdpKappa ell p S shift
        hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm hpComplement
  · intro hstable spdpKappa ell p S shift hSlen hshiftDegree hSlog
      hshiftLog hshiftVars hadm hpComplement
    have hpMap :
        routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift p ∈
          Submodule.map
            (routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift)
            (routeBRicherSPDPStableCandidateProjectionComplement
              M n hn2 htb hns tail) := by
      exact ⟨p, hpComplement, rfl⟩
    have hsubset :=
      hstable spdpKappa ell S shift
        hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm
    simpa [routeBSPDPGeneratorRowLinearMap_apply] using hsubset hpMap

/-- The head-span tail's chosen complement as a named explicit complement. -/
noncomputable abbrev routeBRicherSPDPStableCandidateLogWindowHeadTailChosenComplement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidateProjectionComplement
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)

/-- The named head-span-tail chosen complement is complementary to the
prepended finite-row span. -/
theorem routeBRicherSPDPStableCandidateLogWindowHeadTailChosenComplement_isCompl
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    IsCompl
      (finiteRowsSubmodule
        (routeBRicherSPDPStableCandidateRows M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail
            M n hn2 htb hns)))
      (routeBRicherSPDPStableCandidateLogWindowHeadTailChosenComplement
        M n hn2 htb hns) := by
  simpa [routeBRicherSPDPStableCandidateLogWindowHeadTailChosenComplement,
    routeBRicherSPDPStableCandidateProjectionComplement] using
    finiteSubmoduleProjection_isCompl
      (finiteRowsSubmodule
        (routeBRicherSPDPStableCandidateRows M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail
            M n hn2 htb hns)))

/-- Concrete reduction for the head-span/profile tail: it is enough, and by
the previous equivalence necessary, to prove log-window stability of the
chosen complement under the generator linear maps. -/
theorem routeBRicherSPDPStableCandidate_logWindowChosenComplementInvariant_for_headSpanTail_of_stableGeneratorMaps
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hstable :
      RouteBRicherSPDPStableCandidateLogWindowChosenComplementStableGeneratorMaps
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)) :
    RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns) :=
  (routeBRicherSPDPStableCandidate_logWindowChosenComplementInvariant_iff_stableGeneratorMaps
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidateLogWindowHeadTail
      M n hn2 htb hns)).mpr hstable

/-- Projection-intertwining sufficient condition for the chosen projection on
the log-window head-span tail. -/
def RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionIntertwines
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
    exists A :
      SATDeciderGaugeSpace M n hn2 htb hns →ₗ[Rat]
        SATDeciderGaugeSpace M n hn2 htb hns,
      (routeBRicherSPDPStableCandidateProjection
          M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail
            M n hn2 htb hns)).comp
        (routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift) =
      A.comp
        (routeBRicherSPDPStableCandidateProjection
          M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail
            M n hn2 htb hns))

/-- Projection intertwining forces log-window invariance of the chosen
head-span-tail complement. -/
theorem routeBRicherSPDPStableCandidate_logWindowChosenComplementInvariant_for_headSpanTail_of_projectionIntertwines
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hintertwines :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionIntertwines
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns) := by
  intro spdpKappa ell p S shift hSlen hshiftDegree hSlog hshiftLog
    hshiftVars hadm hpComplement
  let tail :=
    routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns
  let rows := routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail
  let Pi := routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail
  obtain ⟨A, hA⟩ :=
    hintertwines spdpKappa ell S shift
      hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm
  have hpRows :
      p ∈ finiteSubmoduleProjectionComplement (finiteRowsSubmodule rows) := by
    simpa [tail, rows, routeBRicherSPDPStableCandidateProjectionComplement]
      using hpComplement
  have hpRowsZero :
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows).projection p =
        0 :=
    (routeBRicherFiniteRowsCandidateGauge_projection_apply_eq_zero_iff
      M n hn2 htb hns rows p).mpr hpRows
  have hpZero : Pi p = 0 := by
    simpa [Pi, routeBRicherSPDPStableCandidateProjection,
      routeBRicherSPDPStableCandidateGauge, rows] using hpRowsZero
  have hrowZero :
      Pi (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) = 0 := by
    have happ := congrArg (fun L => L p) hA
    simpa [Pi, tail, LinearMap.comp_apply,
      routeBSPDPGeneratorRowLinearMap_apply, hpZero] using happ
  have hrowRowsZero :
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows).projection
          (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) = 0 := by
    simpa [Pi, routeBRicherSPDPStableCandidateProjection,
      routeBRicherSPDPStableCandidateGauge, rows] using hrowZero
  have hrowRowsComplement :
      routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∈
        finiteSubmoduleProjectionComplement (finiteRowsSubmodule rows) :=
    (routeBRicherFiniteRowsCandidateGauge_projection_apply_eq_zero_iff
      M n hn2 htb hns rows
      (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)).mp hrowRowsZero
  simpa [tail, rows, routeBRicherSPDPStableCandidateProjectionComplement]
    using hrowRowsComplement

/-! ## Axiom audit anchors -/

#print axioms RouteBRicherSPDPStableCandidateLogWindowChosenComplementStableGeneratorMaps
#print axioms routeBRicherSPDPStableCandidate_logWindowChosenComplementInvariant_iff_stableGeneratorMaps
#print axioms routeBRicherSPDPStableCandidateLogWindowHeadTailChosenComplement_isCompl
#print axioms routeBRicherSPDPStableCandidate_logWindowChosenComplementInvariant_for_headSpanTail_of_stableGeneratorMaps
#print axioms RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionIntertwines
#print axioms routeBRicherSPDPStableCandidate_logWindowChosenComplementInvariant_for_headSpanTail_of_projectionIntertwines

end PallLean.Paper93.Paper283
