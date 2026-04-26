import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailComplement

/-!
# Head-tail chosen-complement descent criterion

The complement selected by `finiteSubmoduleProjectionComplement` is arbitrary:
it is obtained from `Submodule.exists_isCompl` by `Classical.choose`.  This file
therefore does not assert a canonical invariance property of that complement.
Instead it proves the sharp positive route: for the head-span tail, stability
of the chosen complement is exactly the statement that every log-window
generator row map descends through the chosen finite-row projection.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Kernel criterion for the selected projection of the smaller SPDP-stable
candidate, stated against its exposed chosen complement. -/
theorem routeBRicherSPDPStableCandidateProjection_apply_eq_zero_iff_projectionComplement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail p = 0 ↔
      p ∈ routeBRicherSPDPStableCandidateProjectionComplement
        M n hn2 htb hns tail := by
  let rows := routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail
  simpa [routeBRicherSPDPStableCandidateProjection,
    routeBRicherSPDPStableCandidateGauge,
    routeBRicherSPDPStableCandidateProjectionComplement, rows] using
    (routeBRicherFiniteRowsCandidateGauge_projection_apply_eq_zero_iff
      M n hn2 htb hns rows p)

/-- Log-window descent of every head-tail generator through the chosen
finite-row projection.  For a generator map `L` and chosen projection `Pi`,
this is the concrete equation `Pi ∘ L = Pi ∘ L ∘ Pi`. -/
def RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
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
    Pi.comp L = (Pi.comp L).comp Pi

/-- The descent equation is equivalent to stability of the arbitrary chosen
complement. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_iff_stableGeneratorMaps
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
        M n hn2 htb hns ↔
      RouteBRicherSPDPStableCandidateLogWindowChosenComplementStableGeneratorMaps
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns) := by
  constructor
  · intro hdescent spdpKappa ell S shift hSlen hshiftDegree hSlog
      hshiftLog hshiftVars hadm row hrow
    let tail :=
      routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns
    let Pi := routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail
    let L := routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift
    rcases hrow with ⟨p, hpComplement, rfl⟩
    have hpZero : Pi p = 0 := by
      simpa [Pi, tail] using
        (routeBRicherSPDPStableCandidateProjection_apply_eq_zero_iff_projectionComplement
          M n hn2 htb hns tail p).mpr hpComplement
    have hdesc :
        Pi.comp L = (Pi.comp L).comp Pi := by
      simpa [RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent,
        tail, Pi, L] using
        hdescent spdpKappa ell S shift hSlen hshiftDegree hSlog
          hshiftLog hshiftVars hadm
    have hrowZero : Pi (L p) = 0 := by
      have happ := congrArg (fun F => F p) hdesc
      simpa [LinearMap.comp_apply, hpZero] using happ
    simpa [Pi, L, tail] using
      (routeBRicherSPDPStableCandidateProjection_apply_eq_zero_iff_projectionComplement
        M n hn2 htb hns tail (L p)).mp hrowZero
  · intro hstable spdpKappa ell S shift hSlen hshiftDegree hSlog
      hshiftLog hshiftVars hadm
    let tail :=
      routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns
    let Pi := routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail
    let L := routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift
    apply LinearMap.ext
    intro p
    have hPiPi : Pi (Pi p) = Pi p := by
      simpa [Pi, tail] using
        routeBRicherSPDPStableCandidate_projection_idempotent
          M n hn2 htb hns tail p
    have hresZero : Pi (p - Pi p) = 0 := by
      simp [Pi, map_sub, hPiPi]
    have hresComplement :
        p - Pi p ∈
          routeBRicherSPDPStableCandidateProjectionComplement
            M n hn2 htb hns tail := by
      exact
        (routeBRicherSPDPStableCandidateProjection_apply_eq_zero_iff_projectionComplement
          M n hn2 htb hns tail (p - Pi p)).mp hresZero
    have hresMap :
        L (p - Pi p) ∈
          Submodule.map L
            (routeBRicherSPDPStableCandidateProjectionComplement
              M n hn2 htb hns tail) := by
      exact ⟨p - Pi p, hresComplement, rfl⟩
    have hrowComplement :
        L (p - Pi p) ∈
          routeBRicherSPDPStableCandidateProjectionComplement
            M n hn2 htb hns tail := by
      exact
        hstable spdpKappa ell S shift hSlen hshiftDegree hSlog
          hshiftLog hshiftVars hadm hresMap
    have hrowZero : Pi (L (p - Pi p)) = 0 := by
      exact
        (routeBRicherSPDPStableCandidateProjection_apply_eq_zero_iff_projectionComplement
          M n hn2 htb hns tail (L (p - Pi p))).mpr hrowComplement
    have hsubZero : Pi (L p) - Pi (L (Pi p)) = 0 := by
      have hmapSub : Pi (L p - L (Pi p)) = 0 := by
        simpa [map_sub] using hrowZero
      simpa [map_sub] using hmapSub
    have hpoint : Pi (L p) = Pi (L (Pi p)) := sub_eq_zero.mp hsubZero
    simpa [RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent,
      tail, Pi, L, LinearMap.comp_apply] using hpoint

/-- Projection intertwining is exactly the same descent equation. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionIntertwines_iff_descent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionIntertwines
        M n hn2 htb hns ↔
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
        M n hn2 htb hns := by
  constructor
  · intro hintertwines spdpKappa ell S shift hSlen hshiftDegree hSlog
      hshiftLog hshiftVars hadm
    let tail :=
      routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns
    let Pi := routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail
    let L := routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift
    obtain ⟨A, hA⟩ :=
      hintertwines spdpKappa ell S shift hSlen hshiftDegree hSlog
        hshiftLog hshiftVars hadm
    apply LinearMap.ext
    intro p
    have hPiPi : Pi (Pi p) = Pi p := by
      simpa [Pi, tail] using
        routeBRicherSPDPStableCandidate_projection_idempotent
          M n hn2 htb hns tail p
    have hleft := congrArg (fun F => F p) hA
    have hright := congrArg (fun F => F (Pi p)) hA
    have hpoint : Pi (L p) = Pi (L (Pi p)) := by
      calc
        Pi (L p) = A (Pi p) := by
          simpa [tail, Pi, L, LinearMap.comp_apply] using hleft
        _ = A (Pi (Pi p)) := by
          rw [hPiPi]
        _ = Pi (L (Pi p)) := by
          symm
          simpa [tail, Pi, L, LinearMap.comp_apply] using hright
    simpa [RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent,
      tail, Pi, L, LinearMap.comp_apply] using hpoint
  · intro hdescent spdpKappa ell S shift hSlen hshiftDegree hSlog
      hshiftLog hshiftVars hadm
    let tail :=
      routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns
    let Pi := routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail
    let L := routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift
    refine ⟨Pi.comp L, ?_⟩
    simpa [RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent,
      tail, Pi, L] using
      hdescent spdpKappa ell S shift hSlen hshiftDegree hSlog
        hshiftLog hshiftVars hadm

/-- Therefore the stable-generator-map target and the projection-intertwining
target are equivalent for the head-span tail. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionIntertwines_iff_stableGeneratorMaps
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionIntertwines
        M n hn2 htb hns ↔
      RouteBRicherSPDPStableCandidateLogWindowChosenComplementStableGeneratorMaps
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns) := by
  rw [routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionIntertwines_iff_descent]
  exact
    routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_iff_stableGeneratorMaps
      M n hn2 htb hns

/-- The original log-window chosen-complement invariant is exactly the
projection-descent condition for the head-span tail. -/
theorem routeBRicherSPDPStableCandidate_logWindowChosenComplementInvariant_for_headSpanTail_iff_descent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns) ↔
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
        M n hn2 htb hns := by
  rw [routeBRicherSPDPStableCandidate_logWindowChosenComplementInvariant_iff_stableGeneratorMaps]
  exact
    (routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_iff_stableGeneratorMaps
      M n hn2 htb hns).symm

/-! ## Axiom audit anchors -/

#print axioms routeBRicherSPDPStableCandidateProjection_apply_eq_zero_iff_projectionComplement
#print axioms RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_iff_stableGeneratorMaps
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionIntertwines_iff_descent
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionIntertwines_iff_stableGeneratorMaps
#print axioms routeBRicherSPDPStableCandidate_logWindowChosenComplementInvariant_for_headSpanTail_iff_descent

end PallLean.Paper93.Paper283
