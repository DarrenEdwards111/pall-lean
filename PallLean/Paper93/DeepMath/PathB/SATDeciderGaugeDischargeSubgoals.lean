import PallLean.Paper93.DeepMath.PathB.R70FinalTheoremSurface

/-!
# SAT-decider gauge discharge subgoals

This file does not construct the remaining SAT-decider gauge.  It only splits
the existing `SATDeciderSpecificGaugeDischarge` frontier from
`R70FinalTheoremSurface` into the three field-level obligations of
`GlobalGodMoveGauge.IsAmplituhedronGauge`, then repackages their conjunction.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine

/-- Polynomial space for the Cook-Levin compilation used by the SAT-decider
gauge frontier. -/
abbrev SATDeciderGaugeSpace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Type :=
  MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) Rat

/-- Linear gauge type for the Cook-Levin compilation used by the frontier. -/
abbrev SATDeciderGaugeMap
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Type :=
  SATDeciderGaugeSpace M n hn2 htb hns →ₗ[Rat]
    SATDeciderGaugeSpace M n hn2 htb hns

/-- Subgoal (i): the gauge is rank-monotone for every polynomial. -/
def SATDeciderGaugeRankMonotonicity
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns) : Prop :=
  ∀ (κ ℓ : Nat) (p : SATDeciderGaugeSpace M n hn2 htb hns),
    mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
        κ ℓ (gauge p) ≤
      mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
        κ ℓ p

/-- Subgoal (ii): the gauged compiled polynomial has the projected P-side
rank bound. -/
def SATDeciderGaugePSideBound
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns) : Prop :=
  mlBlockedSpdpRank
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ≤ n ^ 200

/-- Subgoal (iii): for SAT-deciders, the gauged compiled polynomial preserves
the NP-side identity-minor lower bound. -/
def SATDeciderGaugeNPIdentityMinorPreservation
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns) : Prop :=
  DecidesSAT M →
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)))

/-- The explicit three-subgoal package matching
`GlobalGodMoveGauge.IsAmplituhedronGauge`. -/
def SATDeciderGaugeSubgoals
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns) : Prop :=
  SATDeciderGaugeRankMonotonicity M n hn2 htb hns gauge ∧
    SATDeciderGaugePSideBound M n hn2 htb hns gauge ∧
      SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns gauge

/-- The three explicit subgoals are exactly the fields of
`GlobalGodMoveGauge.IsAmplituhedronGauge`. -/
theorem satDeciderGaugeSubgoals_iff_isAmplituhedronGauge
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns) :
    SATDeciderGaugeSubgoals M n hn2 htb hns gauge ↔
      GlobalGodMoveGauge.IsAmplituhedronGauge M n hn hn2 htb hns gauge := by
  constructor
  · intro h
    exact
      { rank_monotone := h.1
        p_side_bound := h.2.1
        preserves_identity_minor_for_sat_deciders := h.2.2 }
  · intro h
    exact ⟨h.rank_monotone, h.p_side_bound, h.preserves_identity_minor_for_sat_deciders⟩

/-- Top-level form of the remaining frontier, stated with the three explicit
subgoals instead of the bundled `GlobalGodMoveGauge` structure. -/
def SATDeciderSpecificGaugeSubgoalDischarge : Prop :=
  ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_hdec : DecidesSAT M),
    ∃ (gauge : SATDeciderGaugeMap M n hn2 htb hns),
      SATDeciderGaugeSubgoals M n hn2 htb hns gauge

/-- The explicit subgoal package constructs the existing R70 discharge
surface. -/
theorem satDeciderSpecificGaugeDischarge_of_subgoals
    (h : SATDeciderSpecificGaugeSubgoalDischarge) :
    SATDeciderSpecificGaugeDischarge := by
  intro M n hn hn2 htb hns hdec
  obtain ⟨gauge, hgauge⟩ := h M n hn hn2 htb hns hdec
  exact ⟨gauge,
    (satDeciderGaugeSubgoals_iff_isAmplituhedronGauge
      M n hn hn2 htb hns gauge).mp hgauge⟩

/-- Conversely, the existing R70 discharge surface splits into the three
explicit subgoals. -/
theorem satDeciderSpecificGaugeSubgoals_of_discharge
    (h : SATDeciderSpecificGaugeDischarge) :
    SATDeciderSpecificGaugeSubgoalDischarge := by
  intro M n hn hn2 htb hns hdec
  obtain ⟨gauge, hgauge⟩ := h M n hn hn2 htb hns hdec
  exact ⟨gauge,
    (satDeciderGaugeSubgoals_iff_isAmplituhedronGauge
      M n hn hn2 htb hns gauge).mpr hgauge⟩

/-- Equivalence between the R70 bundled frontier and the explicit three-subgoal
frontier. -/
theorem satDeciderSpecificGaugeSubgoalDischarge_iff :
    SATDeciderSpecificGaugeSubgoalDischarge ↔
      SATDeciderSpecificGaugeDischarge :=
  ⟨satDeciderSpecificGaugeDischarge_of_subgoals,
   satDeciderSpecificGaugeSubgoals_of_discharge⟩

/-- Usability theorem: the R70 conditional closure accepts the explicit
three-subgoal package. -/
theorem pathB_if_sat_decider_specific_gauge_subgoals
    (h : SATDeciderSpecificGaugeSubgoalDischarge) :
    PathBUpstreamAxiomPNESurface :=
  pathB_if_sat_decider_specific_gauge_discharge
    (satDeciderSpecificGaugeDischarge_of_subgoals h)

end PallLean.Paper93.DeepMath.PathB
