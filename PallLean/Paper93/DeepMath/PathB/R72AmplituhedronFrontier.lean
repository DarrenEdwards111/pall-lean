import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeMapPiPhi
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeNPBridge
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugePSideBridge
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeRealFrontier

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

The final paper-faithful construction still has to build a nontrivial
projection that obtains the P-side bound without destroying the NP lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation
open TuringMachine
open MultilinearSPDP

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

end PallLean.Paper93.DeepMath.PathB
