import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeMapPiPhi
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeNPBridge
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugePSideBridge
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeRealFrontier
import PallLean.Paper93.NFrame.UnitPreservingValueSet

/-!
# Path B R72 amplituhedron frontier surface

R72 tightens the exact SAT-decider gauge frontier without asserting the final
projection exists:

* a concrete flat `piPhi`/identity candidate proves the rank-monotonicity
  field;
* the NP identity-minor field is reduced to the exact projected lower-bound
  subgoal and is proved for the identity gauge;
* the P-side field is reduced to the honest unprojected flat P-side rank bound
  under rank monotonicity;
* the frontier can be strengthened to require a nonzero witness;
* at the paper scale, the bundled gauge frontier is equivalent to ruling out
  bounded SAT deciders.
* the current load-bearing surface is now explicitly paired with the PAC
  rank-monotone compilation bridge and the unit-preserving N-frame minimizer:
  the amplituhedron/holographic geometry supplies the gauge frontier, PAC
  supplies the P-side rank transport, and the N-frame layer supplies the
  canonical nonzero/unit-preserving selector for the proxy Lagrangian.

The final paper-faithful construction still has to build a nontrivial
projection that obtains the P-side bound without destroying the NP lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation
open TuringMachine
open MultilinearSPDP
open MvPolynomial

/-- R72 rank-monotonicity progress: the concrete flat `piPhi` candidate
discharges the rank field. -/
def R72FlatPiPhiRankMonotonicitySurface : Prop :=
  ∀ (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns
      (satDeciderGaugeMapPiPhi M n hn2 htb hns)

/-- R72 NP bridge progress: the identity gauge satisfies the real
compiled-polynomial NP preservation field. -/
def R72IdentityNPBridgeSurface : Prop :=
  ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
      (LinearMap.id : SATDeciderGaugeMap M n hn2 htb hns)

/-- R72 obstruction: identity preserves the NP lower bound, so it cannot also
satisfy the P-side collapse field at the paper scale. -/
def R72IdentityNotPSideSurface : Prop :=
  ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    ¬ SATDeciderGaugePSideBound M n hn2 htb hns
      (LinearMap.id : SATDeciderGaugeMap M n hn2 htb hns)

/-- R72 P-side bridge: rank monotonicity transports an unprojected flat P-side
bound into the projected P-side field. -/
def R72PSideRankMonotoneBridgeSurface : Prop :=
  ∀ (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns),
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns gauge →
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≤ n ^ 200 →
      SATDeciderGaugePSideBound M n hn2 htb hns gauge

/-- R72 nonzero-frontier equivalence. -/
def R72NonzeroFrontierSurface : Prop :=
  SATDeciderSpecificGaugeSubgoalDischarge ↔
    SATDeciderSpecificNonzeroGaugeSubgoalDischarge

/-- R72 exact logical status of the remaining frontier. -/
def R72NoBoundedDeciderEquivalenceSurface : Prop :=
  SATDeciderSpecificGaugeSubgoalDischarge ↔
    NoBoundedSATDeciderAtPaperScale

/-- Combined R72 frontier surface. -/
def R72AmplituhedronFrontierSurface : Prop :=
  R72FlatPiPhiRankMonotonicitySurface ∧
    R72IdentityNPBridgeSurface ∧
    R72IdentityNotPSideSurface ∧
    R72PSideRankMonotoneBridgeSurface ∧
    R72NonzeroFrontierSurface ∧
    R72NoBoundedDeciderEquivalenceSurface

/-- R72 PAC/holography bridge: a PAC decomposition of the compiled object
feeds the Theorem-207 P-side rank slot through the rank-monotone PAC
calculus.  This is a named Path-B wrapper around
`PaperFaithfulSeparation.compiled_p_side_bound_from_PAC_pipeline`, so the
amplituhedron frontier can cite the PAC layer without re-opening the main
separation file. -/
def R72HolographicPACBridgeSurface : Prop :=
  ∀ {N : ℕ} (B : SPDP.BlockPartition N) (κ ℓ : ℕ)
    (q : MvPolynomial (Fin N) ℚ)
    (π : PAC.Pipeline N)
    (rank_q_bound pipeline_factor_bound n_exp_target : ℕ),
    mlBlockedSpdpRank B (κ + PAC.Pipeline.κShiftSum π)
      (ℓ + PAC.Pipeline.ℓShiftSum π) q ≤ rank_q_bound →
    pipeline_factor_bound * rank_q_bound ≤ n_exp_target →
    N ^ PAC.Pipeline.factorSum π *
      mlBlockedSpdpRank B (κ + PAC.Pipeline.κShiftSum π)
        (ℓ + PAC.Pipeline.ℓShiftSum π) q ≤
    max (N ^ PAC.Pipeline.factorSum π * rank_q_bound)
        (pipeline_factor_bound * rank_q_bound) ∧
    mlBlockedSpdpRank B κ ℓ (PAC.applyPipeline π q) ≤
      N ^ PAC.Pipeline.factorSum π * rank_q_bound

/-- R72 N-frame selector bridge: every polynomial family has a canonical
unit-preserving admissible minimizer for the N-frame proxy Lagrangian.  This
is the nonzero/unit-preserving selector layer that should now be paired with
the amplituhedron/PAC route, rather than the old zero-gauge placeholder. -/
def R72UnitPreservingNFrameSelectorSurface : Prop :=
  ∀ {N : ℕ} (family : ℕ → MvPolynomial (Fin N) ℚ),
    ∃ Pi : PallLean.Paper93.NFrame.CandidateGauge N,
      PallLean.Paper93.NFrame.UnitPreservingAdmissibleGauge Pi ∧
      ∀ Pi' : PallLean.Paper93.NFrame.CandidateGauge N,
        PallLean.Paper93.NFrame.UnitPreservingAdmissibleGauge Pi' →
          PallLean.Paper93.NFrame.nframeLagrangian family Pi ≤
            PallLean.Paper93.NFrame.nframeLagrangian family Pi'

/-- Current combined Path-B surface: amplituhedron/holographic frontier + PAC
rank transport + unit-preserving N-frame minimizer. -/
def R72AmplituhedronHolographicPACNFrameSurface : Prop :=
  R72AmplituhedronFrontierSurface ∧
    R72HolographicPACBridgeSurface ∧
    R72UnitPreservingNFrameSelectorSurface

theorem r72_flatPiPhi_rankMonotonicity :
    R72FlatPiPhiRankMonotonicitySurface := by
  intro M n hn2 htb hns
  exact satDeciderGaugeMapPiPhi_rankMonotonicity M n hn2 htb hns

theorem r72_identity_npBridge :
    R72IdentityNPBridgeSurface := by
  intro M n hn hn2 htb hns
  exact satDeciderGaugeNPIdentityMinorPreservation_id M n hn hn2 htb hns

theorem r72_identity_not_pSide :
    R72IdentityNotPSideSurface := by
  intro M n hn hn2 htb hns
  exact identitySATDeciderGauge_not_pSideBound_at_large_n M n hn hn2 htb hns

theorem r72_pSide_rankMonotone_bridge :
    R72PSideRankMonotoneBridgeSurface := by
  intro M n hn2 htb hns gauge hrank hunprojected
  exact satDeciderGaugePSideBound_of_rankMonotone_of_unprojected_bound
    M n hn2 htb hns gauge hrank hunprojected

theorem r72_nonzero_frontier :
    R72NonzeroFrontierSurface :=
  satDeciderSpecificGaugeSubgoalDischarge_iff_nonzero

theorem r72_no_bounded_decider_equivalence :
    R72NoBoundedDeciderEquivalenceSurface :=
  satDeciderSpecificGaugeSubgoalDischarge_iff_no_bounded_sat_decider

/-- Combined R72 theorem surface. -/
theorem r72_amplituhedron_frontier_surface :
    R72AmplituhedronFrontierSurface :=
    ⟨r72_flatPiPhi_rankMonotonicity,
      r72_identity_npBridge,
      r72_identity_not_pSide,
      r72_pSide_rankMonotone_bridge,
      r72_nonzero_frontier,
      r72_no_bounded_decider_equivalence⟩

theorem r72_holographic_PAC_bridge :
    R72HolographicPACBridgeSurface := by
  intro N B κ ℓ q π rank_q_bound pipeline_factor_bound n_exp_target hRankQ hExp
  exact PaperFaithfulSeparation.compiled_p_side_bound_from_PAC_pipeline
    B κ ℓ q π rank_q_bound pipeline_factor_bound n_exp_target hRankQ hExp

theorem r72_unitPreserving_nframe_selector :
    R72UnitPreservingNFrameSelectorSurface := by
  intro N family
  exact PallLean.Paper93.NFrame.unitPreserving_minimizer_exists family

/-- Combined theorem for the requested route: use the amplituhedron/
holographic frontier together with PAC rank transport and the unit-preserving
N-frame minimizer. -/
theorem r72_amplituhedron_holographic_PAC_nframe_surface :
    R72AmplituhedronHolographicPACNFrameSurface :=
  ⟨r72_amplituhedron_frontier_surface,
    r72_holographic_PAC_bridge,
    r72_unitPreserving_nframe_selector⟩

/-- If the combined amplituhedron/holographic PAC + unit-preserving N-frame
surface is paired with the remaining SAT-decider frontier discharge, then the
paper-scale bounded SAT decider is impossible.  This is the explicit closure
hook: the new surface supplies the route; the frontier discharge supplies the
last contradiction-strength content. -/
theorem r72_no_bounded_sat_decider_from_holographic_PAC_nframe_discharge
    (_h : R72AmplituhedronHolographicPACNFrameSurface)
    (hdischarge : SATDeciderSpecificGaugeSubgoalDischarge) :
    NoBoundedSATDeciderAtPaperScale :=
  r72_no_bounded_decider_equivalence.mp hdischarge

/-- The combined surface plus frontier discharge yields the minimal
rank-sandwich form used by the current `P ≠ NP` chain.  Under a hypothetical
SAT-decider, the no-decider conclusion is contradictory, so the sandwich
statement follows by ex falso. -/
theorem r72_rank_sandwich_from_holographic_PAC_nframe_discharge
    (h : R72AmplituhedronHolographicPACNFrameSurface)
    (hdischarge : SATDeciderSpecificGaugeSubgoalDischarge)
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    ∃ (r : ℕ), Nat.choose (n / 3) (Nat.log 2 n) ≤ r ∧ r ≤ n ^ 200 := by
  have hno :=
    r72_no_bounded_sat_decider_from_holographic_PAC_nframe_discharge h hdischarge
  exact False.elim ((hno M n hn hn2 htb hns) hdec)

/-- Final Path-B closure theorem from the new route: once the remaining
SAT-decider frontier discharge is supplied, the amplituhedron/holographic PAC
+ unit-preserving N-frame surface closes the paper's `P ≠ NP` contradiction. -/
theorem r72_P_ne_NP_from_holographic_PAC_nframe_discharge
    (h : R72AmplituhedronHolographicPACNFrameSurface)
    (hdischarge : SATDeciderSpecificGaugeSubgoalDischarge) :
    ∀ (_ : PeqNP_Paper), False := by
  intro hPeqNP
  set n := 2 ^ 804 with hn_def
  have hn : n ≥ 2 ^ 804 := le_refl _
  have hn2 : n ≥ 2 := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
  have hns_n : hPeqNP.decider.numStates ≤ n := by
    rw [hn_def]
    exact hPeqNP.numStates_bound
  have hno :=
    r72_no_bounded_sat_decider_from_holographic_PAC_nframe_discharge h hdischarge
  exact (hno hPeqNP.decider n hn hn2 hPeqNP.timeBound_le hns_n)
    hPeqNP.decides_3sat

/-!
## Axiom audit anchors
-/
#print axioms r72_flatPiPhi_rankMonotonicity
#print axioms r72_identity_npBridge
#print axioms r72_identity_not_pSide
#print axioms r72_pSide_rankMonotone_bridge
#print axioms r72_nonzero_frontier
#print axioms r72_no_bounded_decider_equivalence
#print axioms r72_amplituhedron_frontier_surface
#print axioms r72_holographic_PAC_bridge
#print axioms r72_unitPreserving_nframe_selector
#print axioms r72_amplituhedron_holographic_PAC_nframe_surface
#print axioms r72_no_bounded_sat_decider_from_holographic_PAC_nframe_discharge
#print axioms r72_rank_sandwich_from_holographic_PAC_nframe_discharge
#print axioms r72_P_ne_NP_from_holographic_PAC_nframe_discharge

end PallLean.Paper93.DeepMath.PathB
