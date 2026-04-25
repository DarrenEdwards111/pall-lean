import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeDischargeSubgoals
import PallLean.PaperFaithfulCompilation

/-!
# Nonzero frontier for SAT-decider gauges

This file records a small obstruction built directly from the exact
`SATDeciderGaugeSubgoals`: once the NP identity-minor lower bound is positive,
any successful SAT-decider gauge must send the compiled Cook-Levin polynomial
to a nonzero polynomial. In particular, the gauge linear map itself cannot be
the zero map.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine

/-- NP identity-minor preservation forces the gauged compiled polynomial to be
nonzero whenever the binomial lower bound is positive. -/
theorem satDeciderGaugeNPIdentityMinorPreservation_forces_compiledPoly_image_ne_zero
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hdec : DecidesSAT M)
    (hbinom_pos : 0 < Nat.choose (n / 3) (Nat.log 2 n))
    (hpres : SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns gauge) :
    gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≠ 0 := by
  intro hzero
  have hle_zero : Nat.choose (n / 3) (Nat.log 2 n) ≤ 0 := by
    have hpres' := hpres hdec
    simpa [hzero, MultilinearSPDP.mlBlockedSpdpRank_zero] using hpres'
  exact (not_lt_of_ge hle_zero) hbinom_pos

/-- The full three-subgoal package forces the gauged compiled polynomial to be
nonzero whenever the binomial lower bound is positive. -/
theorem satDeciderGaugeSubgoals_forces_compiledPoly_image_ne_zero
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hdec : DecidesSAT M)
    (hbinom_pos : 0 < Nat.choose (n / 3) (Nat.log 2 n))
    (hsubgoals : SATDeciderGaugeSubgoals M n hn2 htb hns gauge) :
    gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≠ 0 :=
  satDeciderGaugeNPIdentityMinorPreservation_forces_compiledPoly_image_ne_zero
    M n hn2 htb hns gauge hdec hbinom_pos hsubgoals.2.2

/-- Consequently, any gauge satisfying the full three-subgoal package is a
nonzero linear map whenever the binomial lower bound is positive. -/
theorem satDeciderGaugeSubgoals_forces_gauge_ne_zero
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hdec : DecidesSAT M)
    (hbinom_pos : 0 < Nat.choose (n / 3) (Nat.log 2 n))
    (hsubgoals : SATDeciderGaugeSubgoals M n hn2 htb hns gauge) :
    gauge ≠ 0 := by
  intro hgauge_zero
  have himage_ne_zero :=
    satDeciderGaugeSubgoals_forces_compiledPoly_image_ne_zero
      M n hn2 htb hns gauge hdec hbinom_pos hsubgoals
  apply himage_ne_zero
  rw [hgauge_zero]
  simp

/-- At the paper scale `n ≥ 2^804`, the binomial gap is automatic, so the
exact SAT-decider subgoals force a nonzero gauged compiled polynomial. -/
theorem satDeciderGaugeSubgoals_forces_compiledPoly_image_ne_zero_at_large_n
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hdec : DecidesSAT M)
    (hsubgoals : SATDeciderGaugeSubgoals M n hn2 htb hns gauge) :
    gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≠ 0 :=
  satDeciderGaugeSubgoals_forces_compiledPoly_image_ne_zero
    M n hn2 htb hns gauge hdec
    (lt_of_le_of_lt (Nat.zero_le _)
      (PaperFaithfulCompilation.arithmetic_gap_2pow804 n hn))
    hsubgoals

/-- At the paper scale `n ≥ 2^804`, any successful SAT-decider gauge witness is
a nonzero linear map. -/
theorem satDeciderGaugeSubgoals_forces_gauge_ne_zero_at_large_n
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hdec : DecidesSAT M)
    (hsubgoals : SATDeciderGaugeSubgoals M n hn2 htb hns gauge) :
    gauge ≠ 0 :=
  satDeciderGaugeSubgoals_forces_gauge_ne_zero
    M n hn2 htb hns gauge hdec
    (lt_of_le_of_lt (Nat.zero_le _)
      (PaperFaithfulCompilation.arithmetic_gap_2pow804 n hn))
    hsubgoals

/-- Strengthened frontier: the remaining SAT-decider gauge subgoal can require
the witness to be nonzero on the compiled polynomial at no extra cost. -/
def SATDeciderSpecificNonzeroGaugeSubgoalDischarge : Prop :=
  ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_hdec : DecidesSAT M),
    ∃ (gauge : SATDeciderGaugeMap M n hn2 htb hns),
      SATDeciderGaugeSubgoals M n hn2 htb hns gauge ∧
        gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≠ 0 ∧
          gauge ≠ 0

/-- The original frontier implies the nonzero strengthened frontier. -/
theorem satDeciderSpecificNonzeroGaugeSubgoalDischarge_of_subgoals
    (h : SATDeciderSpecificGaugeSubgoalDischarge) :
    SATDeciderSpecificNonzeroGaugeSubgoalDischarge := by
  intro M n hn hn2 htb hns hdec
  obtain ⟨gauge, hsubgoals⟩ := h M n hn hn2 htb hns hdec
  refine ⟨gauge, hsubgoals, ?_, ?_⟩
  · exact satDeciderGaugeSubgoals_forces_compiledPoly_image_ne_zero_at_large_n
      M n hn hn2 htb hns gauge hdec hsubgoals
  · exact satDeciderGaugeSubgoals_forces_gauge_ne_zero_at_large_n
      M n hn hn2 htb hns gauge hdec hsubgoals

/-- The nonzero strengthened frontier forgets back to the original frontier. -/
theorem satDeciderSpecificGaugeSubgoalDischarge_of_nonzero
    (h : SATDeciderSpecificNonzeroGaugeSubgoalDischarge) :
    SATDeciderSpecificGaugeSubgoalDischarge := by
  intro M n hn hn2 htb hns hdec
  obtain ⟨gauge, hsubgoals, _, _⟩ := h M n hn hn2 htb hns hdec
  exact ⟨gauge, hsubgoals⟩

/-- The remaining SAT-decider gauge frontier is equivalent to its nonzero
witness form. -/
theorem satDeciderSpecificGaugeSubgoalDischarge_iff_nonzero :
    SATDeciderSpecificGaugeSubgoalDischarge ↔
      SATDeciderSpecificNonzeroGaugeSubgoalDischarge :=
  ⟨satDeciderSpecificNonzeroGaugeSubgoalDischarge_of_subgoals,
   satDeciderSpecificGaugeSubgoalDischarge_of_nonzero⟩

end PallLean.Paper93.DeepMath.PathB
