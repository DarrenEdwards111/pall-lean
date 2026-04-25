import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeDischargeSubgoals
import PallLean.PaperFaithfulCompilation

/-!
# A concrete `SATDeciderGaugeMap` candidate from `piPhi`

This file keeps the existing flat Cook-Levin `SATDeciderGaugeMap` type and
instantiates it with the paper-faithful `piPhi` infrastructure on the
zero-tableau `UVSplit`.  This is deliberately only the rank-monotonicity field:
it does not claim the P-side bound or NP identity-minor preservation.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine

/-- The flat Cook-Levin space as a degenerate `UVSplit`: all variables are
clause-sheet variables and there are no tableau variables. -/
noncomputable def flatCookLevinUVSplit
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    UVSplit where
  numU := (cook_levin_compilation M n hn2 htb hns).numVars
  numV := 0

/-- In the flat split, `keepU` keeps every variable. -/
theorem flatCookLevinUVSplit_keepU_all
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ∀ i : (flatCookLevinUVSplit M n hn2 htb hns).Idx,
      keepU (flatCookLevinUVSplit M n hn2 htb hns) i := by
  intro i
  exact i.isLt

/-- Concrete candidate for the existing flat `SATDeciderGaugeMap`, obtained by
specialising `piPhi` to the flat zero-tableau split. -/
noncomputable def satDeciderGaugeMapPiPhi
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeMap M n hn2 htb hns :=
  piPhi (flatCookLevinUVSplit M n hn2 htb hns)

/-- The `piPhi` candidate is the identity on the flat Cook-Levin space. -/
theorem satDeciderGaugeMapPiPhi_eq_id
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    satDeciderGaugeMapPiPhi M n hn2 htb hns = LinearMap.id := by
  unfold satDeciderGaugeMapPiPhi piPhi PiStarConcrete.piZero
  exact PiStarConcrete.piSubst_all_kept
    (keepU (flatCookLevinUVSplit M n hn2 htb hns))
    (flatCookLevinUVSplit_keepU_all M n hn2 htb hns)
    (0 : (flatCookLevinUVSplit M n hn2 htb hns).Idx → Rat)

/-- The concrete `piPhi` candidate is a projection gauge. -/
theorem satDeciderGaugeMapPiPhi_isProjectionGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    GaugeMonotonicity.IsProjectionGauge
      (satDeciderGaugeMapPiPhi M n hn2 htb hns) :=
  piPhi_isProjectionGauge (flatCookLevinUVSplit M n hn2 htb hns)

/-- Rank-monotonicity for the concrete `piPhi` candidate, stated in the
existing SAT-decider subgoal vocabulary. -/
theorem satDeciderGaugeMapPiPhi_rankMonotonicity
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns
      (satDeciderGaugeMapPiPhi M n hn2 htb hns) :=
  piPhi_isRankMonotoneGauge
    (flatCookLevinUVSplit M n hn2 htb hns)
    (cook_levin_compilation M n hn2 htb hns).partition

/-- Applying the concrete candidate to any polynomial leaves it fixed.  This is
useful for downstream experiments that want to rewrite the flat candidate away
without opening the `piPhi` definition. -/
theorem satDeciderGaugeMapPiPhi_apply
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    satDeciderGaugeMapPiPhi M n hn2 htb hns p = p := by
  rw [satDeciderGaugeMapPiPhi_eq_id]
  rfl

end PallLean.Paper93.DeepMath.PathB
