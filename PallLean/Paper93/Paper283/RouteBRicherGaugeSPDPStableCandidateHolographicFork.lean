import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadSpanStableMapsProof
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailKernelCriterionProof
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailConcreteEscapeWitness

/-!
# Route B head-tail holographic fork

This module is the roll-up for the Section 39 head-tail fork exposed by the
canonical log-window head-span tail.

The positive branch is now stated through the sharper proof interfaces:

* second-pass closure of finite head-span generators;
* stability of the chosen-projection kernel, or the stronger residual-row
  annihilation condition.

The negative branch is the concrete coordinate obstruction:

* a visible monomial coefficient after the selected projection refutes the
  same holographic-invariance interface.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-! ## Checked boundary cases -/

/-- Multilinear projection is idempotent.  This is the algebra used by the
empty second-pass generator boundary case below. -/
theorem mlProj_idempotent {σ : Type*} [DecidableEq σ] {F : Type*}
    [CommRing F] (p : MvPolynomial σ F) :
    mlProj (mlProj p) = mlProj p := by
  change Finsupp.filter _ (Finsupp.filter _ p) = Finsupp.filter _ p
  ext α
  simp only [Finsupp.filter_apply]
  split <;> rfl

/-- Boundary case for finite head-span second-pass closure: if the second
generator is the empty derivative with unit shift, the row is just `mlProj`
again, hence already lies in the log-window head span by idempotence. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadSpanGeneratorSecondPassClosure_nil_one
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {headKappa headEll : Nat}
    (T : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (headShift : SATDeciderGaugeSpace M n hn2 htb hns)
    (hTlen : T.length = headKappa)
    (hheadShiftDegree : headShift.totalDegree <= headEll)
    (hheadShiftVars : headShift.vars <= T.toFinset)
    (hTadm : SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition T)
    (hheadKappaLog : headKappa <= Nat.log 2 n)
    (hheadEllLog : headEll <= Nat.log 2 n) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
        [] 1 ∈
      routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns := by
  have hgen :
      mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ∈
        mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition
          headKappa headEll
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) := by
    unfold mlBlockedSpdpSubspace
    exact Submodule.subset_span
      ⟨T, headShift, hTlen, hheadShiftDegree, hheadShiftVars, hTadm, rfl⟩
  have hhead :
      mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ∈
        routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns :=
    (routeBRicherSPDPStableCandidateLogWindowHeadSpan_contains
      M n hn2 htb hns headKappa headEll hheadKappaLog hheadEllLog) hgen
  simpa [routeBSPDPGeneratorRow, SPDP.iterDerivList, mlProj_idempotent]
    using hhead

/-- Boundary case for finite head-span second-pass closure: if the second
derivative list is longer than the variable support of the already-projected
head generator, admissibility forces some second-pass variable to be absent
from that support, so the second derivative pass is zero. -/
theorem routeBRicherSPDPStableCandidate_secondPassClosure_of_secondSupportTooSmall
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {spdpKappa : Nat}
    {T S : List (Fin (RouteBCookLevinDim M n hn2 htb hns))}
    {headShift shift : SATDeciderGaugeSpace M n hn2 htb hns}
    (hSlen : S.length = spdpKappa)
    (hadm : SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S)
    (hsmall :
      (mlProj
        (headShift *
          SPDP.iterDerivList T
            (compiledPoly (cook_levin_compilation M n hn2 htb hns)))).vars.card <
        spdpKappa) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
        S shift ∈
      routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns := by
  let q : SATDeciderGaugeSpace M n hn2 htb hns :=
    mlProj
      (headShift *
        SPDP.iterDerivList T
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)))
  have hsmallq : q.vars.card < S.length := by
    simpa [q, hSlen] using hsmall
  have hnotSub : ¬ S.toFinset ⊆ q.vars := by
    intro hsub
    have hcardS : S.toFinset.card = S.length :=
      List.toFinset_card_of_nodup hadm.1
    have hle : S.toFinset.card <= q.vars.card := Finset.card_le_card hsub
    have hlt : q.vars.card < S.toFinset.card := by
      simpa [hcardS] using hsmallq
    exact (Nat.not_lt_of_ge hle) hlt
  have hex : ∃ v, v ∈ S.toFinset ∧ v ∉ q.vars := by
    by_contra h
    apply hnotSub
    intro v hvS
    by_contra hvq
    exact h ⟨v, hvS, hvq⟩
  rcases hex with ⟨v, hvS, hvq⟩
  have hzero : SPDP.iterDerivList S q = 0 :=
    IterDerivHelpers.iterDerivList_eq_zero_of_mem_notMem_vars
      S v q (by simpa using hvS) hvq
  change mlProj (shift * SPDP.iterDerivList S q) ∈
    routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns
  rw [hzero, mul_zero, mlProj_zero]
  exact Submodule.zero_mem _

/-- Boundary case for the chosen-projection branch: if the selected projection
is the identity map, then the residual `p - Π p` is zero, so strict residual
generator annihilation holds. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_of_projection_eq_id
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hPi :
      routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns) =
        LinearMap.id) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
      M n hn2 htb hns := by
  intro spdpKappa ell p S shift hSlen hshiftDegree hSlog hshiftLog
    hshiftVars hadm
  let tail := routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns
  let Pi := routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail
  have hPiApply : Pi p = p := by
    have h :=
      congrArg
        (fun F : SATDeciderGaugeSpace M n hn2 htb hns →ₗ[Rat]
            SATDeciderGaugeSpace M n hn2 htb hns => F p)
        hPi
    simpa [Pi, tail] using h
  have hpSub : p - Pi p = 0 := by
    rw [hPiApply]
    simp
  change routeBSPDPGeneratorRow M n hn2 htb hns (p - Pi p) S shift = 0
  rw [hpSub, routeBSPDPGeneratorRow_zero]

/-! ## Head-span escape closure -/

/-- If the finite head-span generator second-pass closure fails, the failure is
already a concrete log-window generator-map escape from the canonical head
span. -/
theorem routeBRicherSPDPStableCandidate_headSpanGeneratorMapEscape_of_not_generatorSecondPassClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hnot :
      ¬ RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorSecondPassClosure
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorMapEscapeWitness
      M n hn2 htb hns := by
  classical
  by_contra hnoEscape
  apply hnot
  intro headKappa headEll spdpKappa ell T headShift S shift
    hTlen hheadShiftDegree hheadShiftVars hTadm hheadKappaLog
    hheadEllLog hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm
  let p :=
    mlProj
      (headShift *
        SPDP.iterDerivList T
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)))
  have hpGen :
      p ∈
        mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition
          headKappa headEll
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) := by
    unfold mlBlockedSpdpSubspace
    exact Submodule.subset_span
      ⟨T, headShift, hTlen, hheadShiftDegree, hheadShiftVars,
        hTadm, by simp [p]⟩
  have hpHead :
      p ∈ routeBRicherSPDPStableCandidateLogWindowHeadSpan
        M n hn2 htb hns :=
    (routeBRicherSPDPStableCandidateLogWindowHeadSpan_contains
      M n hn2 htb hns headKappa headEll hheadKappaLog hheadEllLog) hpGen
  by_contra hrowNotHead
  exact hnoEscape
    ⟨spdpKappa, ell, p, S, shift, hpHead, hSlen, hshiftDegree,
      hSlog, hshiftLog, hshiftVars, hadm,
      by simpa [p] using hrowNotHead⟩

/-- Finite head-span generator second-pass closure is exactly absence of a
concrete log-window generator-map escape from the canonical head span. -/
theorem routeBRicherSPDPStableCandidate_generatorSecondPassClosure_iff_no_headSpanGeneratorMapEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorSecondPassClosure
        M n hn2 htb hns ↔
      ¬ RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorMapEscapeWitness
        M n hn2 htb hns := by
  constructor
  · intro hhead
    exact
      routeBRicherSPDPStableCandidate_no_headSpanGeneratorMapEscape_of_stableGeneratorMaps
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_of_generatorSecondPassClosure
          M n hn2 htb hns hhead)
  · intro hnoEscape
    by_contra hnot
    exact hnoEscape
      (routeBRicherSPDPStableCandidate_headSpanGeneratorMapEscape_of_not_generatorSecondPassClosure
        M n hn2 htb hns hnot)

/-- Positive Route B head-tail fork package using the newest proof-facing
interfaces: finite head-span second-pass closure plus chosen-projection kernel
stability, together with the two existing P-side consumer fields. -/
structure RouteBRicherSPDPStableCandidateHeadTailSecondPassKernelFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    Type where
  head_second_pass_closure :
    RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorSecondPassClosure
      M n hn2 htb hns
  projection_kernel_stable :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
      M n hn2 htb hns
  unprojected_preimage :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowUnprojectedPreimage
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateRows M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns))
  p_window_cover :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns

/-- Second-pass head-span closure and chosen-projection kernel stability lower
to the existing row-closure/descent frontier. -/
def routeBRicherSPDPStableCandidate_headTailRowClosureDescentFrontier_of_secondPass_kernelStable
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailSecondPassKernelFrontier
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHeadTailRowClosureDescentFrontier
      M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_headTailRowClosureDescentFrontier_of_headSpanStableGeneratorMaps
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_of_generatorSecondPassClosure
      M n hn2 htb hns frontier.head_second_pass_closure)
    (routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_of_projectionKernelStableGeneratorMaps
      M n hn2 htb hns frontier.projection_kernel_stable)
    frontier.unprojected_preimage
    frontier.p_window_cover

/-- The positive fork package proves the Section 39-facing holographic
invariance interface for the canonical head-span tail. -/
theorem routeBRicherSPDPStableCandidate_holographicInvariance_of_secondPass_kernelStable
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailSecondPassKernelFrontier
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHolographicInvariance
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_holographicInvariance_for_headSpanTail_of_headSpanStableGeneratorMaps_descent
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_of_generatorSecondPassClosure
      M n hn2 htb hns frontier.head_second_pass_closure)
    (routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_of_projectionKernelStableGeneratorMaps
      M n hn2 htb hns frontier.projection_kernel_stable)

/-- The same positive fork package proves the projected P-side bound, once
the preimage and P-window consumer fields are supplied. -/
theorem routeBRicherSPDPStableCandidate_projectedPSideBound_of_secondPass_kernelStable
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailSecondPassKernelFrontier
        M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)) :=
  routeBRicherSPDPStableCandidate_projectedPSideBound_of_rowClosureDescentFrontier
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headTailRowClosureDescentFrontier_of_secondPass_kernelStable
      M n hn2 htb hns frontier)

/-- Second-pass head-span closure plus residual-row annihilation is a stronger
positive route to the same holographic-invariance interface. -/
theorem routeBRicherSPDPStableCandidate_holographicInvariance_of_secondPass_residualGeneratorZero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hhead :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorSecondPassClosure
        M n hn2 htb hns)
    (hzero :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHolographicInvariance
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_holographicInvariance_for_headSpanTail_of_headSpanStableGeneratorMaps_descent
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_of_generatorSecondPassClosure
      M n hn2 htb hns hhead)
    (routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_of_residualGeneratorZero
      M n hn2 htb hns hzero)

/-- A visible projected monomial coefficient refutes the same Section 39
holographic-invariance interface. -/
theorem routeBRicherSPDPStableCandidate_not_holographicInvariance_of_visibleCoefficientEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hcoord :
      RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateHolographicInvariance
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_not_holographicInvariance_for_headSpanTail_of_logWindowProjectionEscapeWitness
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_visibleCoefficientEscapeObstruction
      M n hn2 htb hns hcoord)

/-- The empty-generator visible coefficient obstruction also refutes the same
Section 39 holographic-invariance interface. -/
theorem routeBRicherSPDPStableCandidate_not_holographicInvariance_of_mlProjVisibleCoefficientEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hcoord :
      RouteBRicherSPDPStableCandidateHeadSpanTailMlProjVisibleCoefficientEscapeWitness
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateHolographicInvariance
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_not_holographicInvariance_for_headSpanTail_of_logWindowProjectionEscapeWitness
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_mlProjVisibleCoefficientEscape
      M n hn2 htb hns hcoord)

/-- Once the finite head-span second-pass closure is supplied, the remaining
chosen-projection branch is exactly a dichotomy: either Section 39
holographic invariance holds for the canonical head-span tail, or there is a
visible projected monomial coefficient escaping the selected complement. -/
theorem routeBRicherSPDPStableCandidate_holographicInvariance_or_visibleCoefficientEscape_of_secondPassClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hhead :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorSecondPassClosure
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHolographicInvariance
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns) ∨
      RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
        M n hn2 htb hns := by
  classical
  by_cases hstable :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
        M n hn2 htb hns
  · left
    exact
      routeBRicherSPDPStableCandidate_holographicInvariance_for_headSpanTail_of_headSpanStableGeneratorMaps_descent
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_of_generatorSecondPassClosure
          M n hn2 htb hns hhead)
        (routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_of_projectionKernelStableGeneratorMaps
          M n hn2 htb hns hstable)
  · right
    have hnotCriterion :
        ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelCriterion
            M n hn2 htb hns := by
      intro hcriterion
      exact hstable
        ((routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_iff_kernelCriterion
          M n hn2 htb hns).mpr hcriterion)
    have hescape :
        RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
          M n hn2 htb hns := by
      by_contra hnoEscape
      exact hnotCriterion
        ((routeBRicherSPDPStableCandidate_headSpanTailKernelCriterion_iff_no_logWindowProjectionEscapeWitness
          M n hn2 htb hns).mpr hnoEscape)
    exact
      routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_of_headSpanTailLogWindowProjectionEscapeWitness
        M n hn2 htb hns hescape

/-- With finite head-span second-pass closure in hand, holographic invariance
is equivalent to the absence of a visible coefficient escape for the chosen
head-span-tail projection. -/
theorem routeBRicherSPDPStableCandidate_holographicInvariance_iff_no_visibleCoefficientEscape_of_secondPassClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hhead :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorSecondPassClosure
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHolographicInvariance
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns) ↔
      ¬ RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
        M n hn2 htb hns := by
  constructor
  · intro hinv hcoord
    exact
      (routeBRicherSPDPStableCandidate_not_holographicInvariance_of_visibleCoefficientEscape
        M n hn2 htb hns hcoord) hinv
  · intro hno
    cases
      routeBRicherSPDPStableCandidate_holographicInvariance_or_visibleCoefficientEscape_of_secondPassClosure
        M n hn2 htb hns hhead with
    | inl hinv => exact hinv
    | inr hcoord => exact False.elim (hno hcoord)

/-- Fully exposed Route B fork after the head-span reduction: either the
finite head span already has a concrete log-window generator-map escape, or
the Section 39 holographic interface holds for the canonical head-span tail,
or the chosen projection has a visible monomial-coefficient escape. -/
theorem routeBRicherSPDPStableCandidate_headSpanEscape_or_holographicInvariance_or_visibleCoefficientEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorMapEscapeWitness
        M n hn2 htb hns ∨
      RouteBRicherSPDPStableCandidateHolographicInvariance
          M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail
            M n hn2 htb hns) ∨
        RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
          M n hn2 htb hns := by
  classical
  by_cases hhead :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorSecondPassClosure
        M n hn2 htb hns
  · right
    exact
      routeBRicherSPDPStableCandidate_holographicInvariance_or_visibleCoefficientEscape_of_secondPassClosure
        M n hn2 htb hns hhead
  · left
    exact
      routeBRicherSPDPStableCandidate_headSpanGeneratorMapEscape_of_not_generatorSecondPassClosure
        M n hn2 htb hns hhead

/-! ## Axiom audit anchors -/

#print axioms mlProj_idempotent
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadSpanGeneratorSecondPassClosure_nil_one
#print axioms routeBRicherSPDPStableCandidate_secondPassClosure_of_secondSupportTooSmall
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_of_projection_eq_id
#print axioms routeBRicherSPDPStableCandidate_headSpanGeneratorMapEscape_of_not_generatorSecondPassClosure
#print axioms routeBRicherSPDPStableCandidate_generatorSecondPassClosure_iff_no_headSpanGeneratorMapEscape
#print axioms RouteBRicherSPDPStableCandidateHeadTailSecondPassKernelFrontier
#print axioms routeBRicherSPDPStableCandidate_headTailRowClosureDescentFrontier_of_secondPass_kernelStable
#print axioms routeBRicherSPDPStableCandidate_holographicInvariance_of_secondPass_kernelStable
#print axioms routeBRicherSPDPStableCandidate_projectedPSideBound_of_secondPass_kernelStable
#print axioms routeBRicherSPDPStableCandidate_holographicInvariance_of_secondPass_residualGeneratorZero
#print axioms routeBRicherSPDPStableCandidate_not_holographicInvariance_of_visibleCoefficientEscape
#print axioms routeBRicherSPDPStableCandidate_not_holographicInvariance_of_mlProjVisibleCoefficientEscape
#print axioms routeBRicherSPDPStableCandidate_holographicInvariance_or_visibleCoefficientEscape_of_secondPassClosure
#print axioms routeBRicherSPDPStableCandidate_holographicInvariance_iff_no_visibleCoefficientEscape_of_secondPassClosure
#print axioms routeBRicherSPDPStableCandidate_headSpanEscape_or_holographicInvariance_or_visibleCoefficientEscape

end PallLean.Paper93.Paper283
