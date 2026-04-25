import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeDischargeSubgoals
import PallLean.PaperFaithfulCompilation

/-!
# Zero gauge obstruction for the NP identity-minor subgoal

The zero linear map discharges the P-side bound trivially, but it cannot
discharge the SAT-decider NP identity-minor preservation subgoal when the
binomial lower bound is positive.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine

/-- The zero linear gauge cannot satisfy the NP identity-minor preservation
subgoal for a SAT decider once the binomial lower bound is positive. -/
theorem zeroGauge_not_npIdentityMinorPreservation_of_binomial_pos
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (hbinom_pos : 0 < Nat.choose (n / 3) (Nat.log 2 n)) :
    ¬ SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
      (0 : SATDeciderGaugeMap M n hn2 htb hns) := by
  intro hpres
  have hle_zero : Nat.choose (n / 3) (Nat.log 2 n) ≤ 0 := by
    simpa [SATDeciderGaugeNPIdentityMinorPreservation,
      SATDeciderGaugeMap, SATDeciderGaugeSpace,
      mlBlockedSpdpRank_zero] using hpres hdec
  exact (not_lt_of_ge hle_zero) hbinom_pos

/-- Consequently, the zero linear gauge cannot satisfy the full three-subgoal
package whenever the SAT-decider NP lower bound is positive. -/
theorem zeroGauge_not_satDeciderGaugeSubgoals_of_binomial_pos
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (hbinom_pos : 0 < Nat.choose (n / 3) (Nat.log 2 n)) :
    ¬ SATDeciderGaugeSubgoals M n hn2 htb hns
      (0 : SATDeciderGaugeMap M n hn2 htb hns) := by
  intro hsubgoals
  exact zeroGauge_not_npIdentityMinorPreservation_of_binomial_pos
    M n hn2 htb hns hdec hbinom_pos hsubgoals.2.2

/-- At the paper scale `n ≥ 2^804`, the zero gauge cannot satisfy the
NP identity-minor preservation subgoal for a SAT decider. -/
theorem zeroGauge_not_npIdentityMinorPreservation_at_large_n
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    ¬ SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
      (0 : SATDeciderGaugeMap M n hn2 htb hns) := by
  exact zeroGauge_not_npIdentityMinorPreservation_of_binomial_pos
    M n hn2 htb hns hdec
    (lt_of_le_of_lt (Nat.zero_le _)
      (PaperFaithfulCompilation.arithmetic_gap_2pow804 n hn))

/-- At the paper scale `n ≥ 2^804`, the zero gauge cannot satisfy the full
SAT-decider gauge subgoal package. -/
theorem zeroGauge_not_satDeciderGaugeSubgoals_at_large_n
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    ¬ SATDeciderGaugeSubgoals M n hn2 htb hns
      (0 : SATDeciderGaugeMap M n hn2 htb hns) := by
  exact zeroGauge_not_satDeciderGaugeSubgoals_of_binomial_pos
    M n hn2 htb hns hdec
    (lt_of_le_of_lt (Nat.zero_le _)
      (PaperFaithfulCompilation.arithmetic_gap_2pow804 n hn))

end PallLean.Paper93.DeepMath.PathB
