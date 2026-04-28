import PallLean.Paper93.DeepMath.PathB.ZeroProfileNormalFormInstantiationProgress
import PallLean.Paper93.Paper283.RouteBRicherGaugePWindowCover
import PallLean.Paper93.Paper283.RouteBRicherGaugeConcreteWChargedClosure

/-!
# Route B projected zero-profile P-window progress

This file separates the part that the projected zero-profile target really
proves from the part still demanded by the current Route B P-window APIs.

The positive result is a projected finite-span/rank bridge: a quotiented
zero-profile span can produce a projected P-window cover if the projected
P-window subspace is shown to land in the projected zero-profile span.

The diagnostic result is that the existing fixed-profile zero-histogram slot is
equivalent to the full unprojected `CookLevinZeroHistogramShiftCommonSpan`.
-/

namespace PallLean
namespace Paper93
namespace DeepMath
namespace PathB

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP SPDP

attribute [local instance] Classical.dec

/-- A budgeted projected common span bounds the finrank of the exact projected
zero-profile shifted span. -/
theorem zeroProfileProjectedShiftSpan_finrank_le_of_commonSpanWithBudget
    {n L κ budget : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hspan :
      ZeroProfileProjectedCommonSpanWithBudget κ factors project budget) :
    Module.finrank ℚ ↥(zeroProfileProjectedShiftSpan κ factors project) ≤
      budget := by
  classical
  rcases hspan with ⟨G, hG_card, hG_span⟩
  have hle :
      zeroProfileProjectedShiftSpan κ factors project ≤
        Submodule.span ℚ
          (↑G : Set (MvPolynomial (Fin n) ℚ)) := by
    rw [zeroProfileProjectedShiftSpan_eq_span_projectedShiftImageSet]
    exact Submodule.span_le.mpr hG_span
  haveI hprojFinite :
      Module.Finite ℚ ↥(zeroProfileProjectedShiftSpan κ factors project) :=
    zeroProfileProjectedShiftSpan_finite κ factors project
  haveI hspanFinite :
      Module.Finite ℚ
        ↥(Submodule.span ℚ
          (↑G : Set (MvPolynomial (Fin n) ℚ))) :=
    Module.Finite.span_of_finite ℚ (Finset.finite_toSet G)
  exact
    (Submodule.finrank_mono hle).trans
      ((finrank_span_finset_le_card G).trans hG_card)

/-- The quotiented zero-profile target really does close the projected
zero-profile shifted-span rank, with no residual payment. -/
theorem cookLevinZeroProfileQuotientedShiftCommonSpan_projectedShiftSpan_finrank_le
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hquot :
      CookLevinZeroProfileQuotientedShiftCommonSpan
        M n hn htb hns project) :
    Module.finrank ℚ
        ↥(zeroProfileProjectedShiftSpan (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn htb hns).get i)
          project) ≤
      withinProfileBound (Nat.log 2 n) :=
  zeroProfileProjectedShiftSpan_finrank_le_of_commonSpanWithBudget
    (κ := Nat.log 2 n)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    project hquot.2.2

/-- The zero-histogram fixed-profile slot in the current profile-compression
API is exactly the full unprojected zero-profile shifted common span.  This is
the checked point where a merely projected zero-profile span no longer matches
the existing all-profile/P-window route. -/
theorem cookLevinAllBoundedProfileCommonSpanAtProfile_zero_iff_shiftCommonSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    CookLevinAllBoundedProfileCommonSpanAtProfile
        M n hn htb hns zeroProfileHistogram ↔
      CookLevinZeroHistogramShiftCommonSpan M n hn htb hns := by
  constructor
  · intro hall
    rcases hall with ⟨G, hG_card, hG_span⟩
    refine ⟨G, hG_card, ?_⟩
    intro q hq
    have hqSpan :
        q ∈ Submodule.span ℚ
          (zeroProfileShiftImageSet (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn htb hns).get i)) :=
      Submodule.subset_span hq
    have hqAll :
        q ∈
          allBoundedProfilePostSpan
            (cook_levin_compilation M n hn htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn htb hns).get i)
            (cookLevinConstraintType M n hn htb hns)
            zeroProfileHistogram := by
      simpa [allBoundedProfilePostSpan_zeroProfile_eq_shiftImageSpan] using
        hqSpan
    exact hG_span hqAll
  · exact
      cookLevinAllBoundedProfileCommonSpanAtProfile_zero_of_shiftCommonSpan
        M n hn htb hns

end PathB
end DeepMath
end Paper93
end PallLean

namespace PallLean.Paper93.Paper283

open MvPolynomial
open TuringMachine
open SymmetricPowerBound
open WithinProfileBound
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Missing containment needed to let a projected zero-profile span serve as a
Route B projected P-window cover.

This is deliberately a projected statement: it does not ask for, or reconstruct,
the old full unprojected zero-profile common span. -/
def RouteBProjectedPWindowControlledByZeroProfileProjection
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)) : Prop :=
  routeBRicherGaugeProjectedPWindowSubspace M n hn2 htb hns Pi ≤
    zeroProfileProjectedShiftSpan (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      project

/-- A quotiented zero-profile common span gives a projected P-window finite
span cover once the projected P-window has been shown to land in that projected
zero-profile span. -/
noncomputable def routeBRicherGauge_projectedPWindowFiniteSpanCover_of_zeroProfileQuotientedShiftCommonSpan
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hquot :
      CookLevinZeroProfileQuotientedShiftCommonSpan
        M n hn2 htb hns project)
    (hcontrol :
      RouteBProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns project Pi)
    (hpoly :
      withinProfileBound (Nat.log 2 n) <= n ^ 200) :
    RouteBRicherGaugeProjectedPWindowFiniteSpanCover
      M n hn2 htb hns Pi where
  span :=
    zeroProfileProjectedShiftSpan (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      project
  finite := by
    simpa [RouteBCookLevinDim] using
      (zeroProfileProjectedShiftSpan_finite (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project)
  contains := hcontrol
  rank_bound := by
    exact
      (cookLevinZeroProfileQuotientedShiftCommonSpan_projectedShiftSpan_finrank_le
        M n hn2 htb hns project hquot).trans hpoly

/-- A budgeted projected zero-profile common span, without any singleton-kernel
or residual hypothesis, is already enough for the projected P-window rank
consumer.  This is the paper-faithful shape used by Boolean/multilinear
normalization: the final projected/log-window path only needs containment in
the selected projected zero-profile span plus the corresponding budget. -/
noncomputable def routeBRicherGauge_projectedPWindowFiniteSpanCover_of_zeroProfileProjectedCommonSpanWithBudget
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    {budget : Nat}
    (hspan :
      ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project budget)
    (hcontrol :
      RouteBProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns project Pi)
    (hpoly : budget <= n ^ 200) :
    RouteBRicherGaugeProjectedPWindowFiniteSpanCover
      M n hn2 htb hns Pi where
  span :=
    zeroProfileProjectedShiftSpan (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      project
  finite := by
    simpa [RouteBCookLevinDim] using
      (zeroProfileProjectedShiftSpan_finite (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project)
  contains := hcontrol
  rank_bound :=
    (zeroProfileProjectedShiftSpan_finrank_le_of_commonSpanWithBudget
      (κ := Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      project hspan).trans hpoly

/-- Projected rank bridge from a budgeted projected zero-profile common span.
Unlike the singleton-quotient constructor, this has no kernel/residual fields;
it is the direct consumer for Boolean-normalized or otherwise projected
normal-form classifiers. -/
theorem routeBRicherGauge_projectedPSideBound_of_zeroProfileProjectedCommonSpanWithBudget
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    {budget : Nat}
    (hspan :
      ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project budget)
    (hcontrol :
      RouteBProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns project Pi)
    (hpoly : budget <= n ^ 200) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) :=
  routeBRicherGauge_projectedPSideBound_of_projectedFiniteSpanCover
    M n hn2 htb hns Pi
    (routeBRicherGauge_projectedPWindowFiniteSpanCover_of_zeroProfileProjectedCommonSpanWithBudget
      M n hn2 htb hns project Pi hspan hcontrol hpoly)

/-- Projected rank bridge from a quotiented zero-profile span plus the missing
projected P-window containment. -/
theorem routeBRicherGauge_projectedPSideBound_of_zeroProfileQuotientedShiftCommonSpan
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hquot :
      CookLevinZeroProfileQuotientedShiftCommonSpan
        M n hn2 htb hns project)
    (hcontrol :
      RouteBProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns project Pi)
    (hpoly :
      withinProfileBound (Nat.log 2 n) <= n ^ 200) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) :=
  routeBRicherGauge_projectedPSideBound_of_projectedFiniteSpanCover
    M n hn2 htb hns Pi
    (routeBRicherGauge_projectedPWindowFiniteSpanCover_of_zeroProfileQuotientedShiftCommonSpan
      M n hn2 htb hns project Pi hquot hcontrol hpoly)

/-- Diagnostic: the current endpoint charged P-window bridge still carries an
unprojected P-window cover. -/
theorem routeBRicherGauge_endpointChargedPWindowBridge_forces_unprojectedPWindowCover
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4) (charge : ProfileCharge n)
    (bridge :
      RouteBRicherGaugeEndpointChargedPWindowBridge
        M n hn2 htb hns hn4 charge) :
    ∃ cover : RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover
        M n hn2 htb hns,
      cover = bridge.cover :=
  ⟨bridge.cover, rfl⟩

/-- Diagnostic rank form: the current endpoint charged P-window bridge still
feeds Route B through the unprojected flat P-side rank bound. -/
theorem routeBRicherGauge_endpointChargedPWindowBridge_forces_unprojectedPSideRankBound
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4) (charge : ProfileCharge n)
    (bridge :
      RouteBRicherGaugeEndpointChargedPWindowBridge
        M n hn2 htb hns hn4 charge) :
    RouteBSATUnprojectedPSideRankBound M n hn2 htb hns :=
  routeBRicherGauge_unprojectedPSideRankBound_of_finiteSpanCover
    M n hn2 htb hns bridge.cover

/-! ## Axiom audit anchors -/

#print axioms zeroProfileProjectedShiftSpan_finrank_le_of_commonSpanWithBudget
#print axioms cookLevinZeroProfileQuotientedShiftCommonSpan_projectedShiftSpan_finrank_le
#print axioms cookLevinAllBoundedProfileCommonSpanAtProfile_zero_iff_shiftCommonSpan
#print axioms RouteBProjectedPWindowControlledByZeroProfileProjection
#print axioms routeBRicherGauge_projectedPWindowFiniteSpanCover_of_zeroProfileQuotientedShiftCommonSpan
#print axioms routeBRicherGauge_projectedPWindowFiniteSpanCover_of_zeroProfileProjectedCommonSpanWithBudget
#print axioms routeBRicherGauge_projectedPSideBound_of_zeroProfileProjectedCommonSpanWithBudget
#print axioms routeBRicherGauge_projectedPSideBound_of_zeroProfileQuotientedShiftCommonSpan
#print axioms routeBRicherGauge_endpointChargedPWindowBridge_forces_unprojectedPWindowCover
#print axioms routeBRicherGauge_endpointChargedPWindowBridge_forces_unprojectedPSideRankBound

end PallLean.Paper93.Paper283
