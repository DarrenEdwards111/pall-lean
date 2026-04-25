import PallLean.Paper93.DeepMath.PathB.R72AmplituhedronFrontier

/-!
# Identity obstructions for the SAT-decider gauge frontier

This file closes two false paths for the exact Cook-Levin SAT-decider gauge
frontier at the paper scale.  It does not construct the final Pi-star projection:
it only records that any map satisfying the three explicit
`SATDeciderGaugeSubgoals` cannot be the identity map, and therefore cannot be
the existing flat `piPhi` map either.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine

/-- At the paper scale, the identity map itself cannot satisfy the three
SAT-decider gauge subgoals.  The obstruction is already the P-side field:
identity preserves the exact real compiled-polynomial NP lower bound, so it
cannot also satisfy the projected P-side rank collapse. -/
theorem identitySATDeciderGauge_not_satDeciderGaugeSubgoals_at_large_n
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ¬ SATDeciderGaugeSubgoals M n hn2 htb hns
      (identitySATDeciderGauge M n hn2 htb hns) := by
  intro hsubgoals
  exact identitySATDeciderGauge_not_pSideBound_at_large_n
    M n hn hn2 htb hns hsubgoals.2.1

/-- Any successful three-subgoal SAT-decider gauge witness at the paper scale
is not the identity map. -/
theorem satDeciderGaugeSubgoals_forces_ne_identitySATDeciderGauge_at_large_n
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hsubgoals : SATDeciderGaugeSubgoals M n hn2 htb hns gauge) :
    gauge ≠ identitySATDeciderGauge M n hn2 htb hns := by
  intro hgauge
  subst gauge
  exact identitySATDeciderGauge_not_satDeciderGaugeSubgoals_at_large_n
    M n hn hn2 htb hns hsubgoals

/-- The existing flat `piPhi` candidate cannot satisfy the three SAT-decider
gauge subgoals at the paper scale.  R72 identifies this flat candidate with
the identity map, so the same P-side obstruction applies. -/
theorem satDeciderGaugeMapPiPhi_not_satDeciderGaugeSubgoals_at_large_n
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ¬ SATDeciderGaugeSubgoals M n hn2 htb hns
      (satDeciderGaugeMapPiPhi M n hn2 htb hns) := by
  intro hsubgoals
  rw [satDeciderGaugeMapPiPhi_eq_id] at hsubgoals
  exact identitySATDeciderGauge_not_satDeciderGaugeSubgoals_at_large_n
    M n hn hn2 htb hns hsubgoals

/-- Any successful three-subgoal SAT-decider gauge witness at the paper scale
is not the existing flat `piPhi` map. -/
theorem satDeciderGaugeSubgoals_forces_ne_satDeciderGaugeMapPiPhi_at_large_n
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hsubgoals : SATDeciderGaugeSubgoals M n hn2 htb hns gauge) :
    gauge ≠ satDeciderGaugeMapPiPhi M n hn2 htb hns := by
  intro hgauge
  subst gauge
  exact satDeciderGaugeMapPiPhi_not_satDeciderGaugeSubgoals_at_large_n
    M n hn hn2 htb hns hsubgoals

/-!
## Axiom audit anchors
-/
#print axioms identitySATDeciderGauge_not_satDeciderGaugeSubgoals_at_large_n
#print axioms satDeciderGaugeSubgoals_forces_ne_identitySATDeciderGauge_at_large_n
#print axioms satDeciderGaugeMapPiPhi_not_satDeciderGaugeSubgoals_at_large_n
#print axioms satDeciderGaugeSubgoals_forces_ne_satDeciderGaugeMapPiPhi_at_large_n

end PallLean.Paper93.DeepMath.PathB
