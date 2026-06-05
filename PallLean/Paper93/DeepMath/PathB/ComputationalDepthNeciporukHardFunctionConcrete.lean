import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukHardFunctionExplicit

/-!
# Nečiporuk concrete hard function (Stage 4): a concrete numeric super-linear instance

The headline bound `hardF_litCount_lower_explicit` is a parametric inequality.  This file *instantiates*
it at a concrete point to exhibit an explicit numeral lower bound that beats the variable count by a
factor `> 3` — a witnessed super-linear formula-size lower bound (not just an asymptotic claim).

Take `b = 10`, `m = 2^10 = 1024` (the balanced family: data region size = number of blocks).  Then:

* variables `N = nn 10 1024 = 1024·10 + 2^10 = 11264`;
* the per-block content `m·(2^b − 1) = 1024·1023 = 1047552`, slack `2(m+1) = 2050`;
* alphabet `2N + 17 = 22545 ≤ 2^15`, so `clog₂ ≤ 15` and the denominator `2·clog₂ ≤ 30`.

Hence any `B₂` formula `F` computing `hardF` has `litCount F ≥ (1047552 − 2050)/30 = ⌈1045502/30⌉`,
so `litCount F ≥ 34850 > 3·11264 = 3N`.

`hardF_litCount_lower_concrete` proves exactly this.  It validates the whole Nečiporuk chain end-to-end
on real numbers.  Still `n²/log²n`-regime, **not** P vs NP.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace NecHard

open scoped BigOperators

/-- **A concrete super-linear instance.**  At `b = 10`, `m = 1024` (so `N = 11264` variables), any
`B₂` formula computing `hardF` has at least `34850` literals — more than `3·N`.  A witnessed,
fully-numeric Nečiporuk formula-size lower bound. -/
theorem hardF_litCount_lower_concrete
    (F : BFormula (nn 10 1024)) (hF : ∀ x, BFormula.eval F x = hardF x) :
    34850 ≤ BFormula.litCount F := by
  have h := hardF_litCount_lower_explicit (b := 10) (m := 1024) F hF
  have hd10 : Dsize 10 = 1024 := by rw [dsize_eq]; norm_num
  have hnn : 2 * nn 10 1024 + 17 = 22545 := by unfold nn; omega
  rw [hd10, hnn] at h
  -- h : 1024 * (1024 - 1) ≤ 2 * Nat.clog 2 22545 * litCount F + 2 * (1024 + 1)
  set c := Nat.clog 2 22545 with hc
  have hclog : c ≤ 15 := by
    rw [hc]; exact Nat.clog_le_of_le_pow (by norm_num)
  have hbnd : 2 * c * BFormula.litCount F ≤ 30 * BFormula.litCount F := by
    refine Nat.mul_le_mul ?_ (le_refl _)
    omega
  omega

end NecHard

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.NecHard.hardF_litCount_lower_concrete
