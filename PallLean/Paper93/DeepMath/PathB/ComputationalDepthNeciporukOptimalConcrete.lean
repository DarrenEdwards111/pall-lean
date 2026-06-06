import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukOptimalBound

/-!
# Optimal Nečiporuk bound: a witnessed numeric instance

Validates the *optimal* (`N²/log N`) chain end-to-end on real numbers — exercising the new closure /
branching / rewire machinery (`Qset`, `card_blockResiduals_le_pow`, `neciporuk_formula_lower_bound_opt`).

Take `b = 10`, `m = 102 = ⌊2^10 / 10⌋` (the balanced choice).  Then `2^10 = 1024 ≤ 2·(102·10) = 2040`
and `102·10 = 1020 ≤ 1024`, so the balance bounds hold; the variable count is
`N = nn 10 102 = 102·10 + 2^10 = 2044`, and `hardF_rate_sq_opt` gives
`litCount F ≥ N² / (64·10) = 2044² / 640 = 6528`.

`hardF_litCount_lower_opt_concrete` proves exactly this.  Still `n²/log n`, **not** P vs NP.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace NecHard

open scoped BigOperators

/-- **Witnessed optimal instance.**  At `b = 10`, `m = 102` (`N = 2044` variables), any `B₂` formula
computing `hardF` has at least `6528` literals — via the optimal `N²/(64·b)` bound. -/
theorem hardF_litCount_lower_opt_concrete
    (F : BFormula (nn 10 102)) (hF : ∀ x, BFormula.eval F x = hardF x) :
    6528 ≤ BFormula.litCount F := by
  have h := hardF_rate_sq_opt 102 10 (by norm_num) (by norm_num) (by norm_num) F hF
  have hd : Dsize 10 = 1024 := by rw [dsize_eq]; norm_num
  have hval : (nn 10 102) ^ 2 / (64 * 10) = 6528 := by
    have hnn : nn 10 102 = 2044 := by unfold nn; omega
    rw [hnn]; norm_num
  rw [hval] at h
  exact h

end NecHard

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.NecHard.hardF_litCount_lower_opt_concrete
