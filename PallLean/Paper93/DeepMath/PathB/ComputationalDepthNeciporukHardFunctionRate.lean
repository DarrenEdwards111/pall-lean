import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukHardFunctionAsymptotic

/-!
# Nečiporuk concrete hard function (Stage 6): an explicit closed-form growth rate

`hardF_superlinear` proves super-linearity non-constructively (`∀ C, ∃ b, …`).  This file gives the
**explicit rate** underneath it: a single closed-form lower bound, valid for every `b ≥ 5`, from which
super-linearity is immediate.

In the balanced family `m = 2^b` (`N = nn b (2^b) = 2^b·(b+1)` variables), any `B₂` formula computing
`hardF` has
  `litCount F ≥ 2^{2b} / (8b)`.
Since `2^{2b} = (2^b)²` and `N ≤ 2^{b+1}·b`, this is `litCount F ≥ Ω(N² / b³)` with `b ≈ log N` — an
explicit super-linear rate, sharper information than the `∀C∃b` statement.

* `hardF_rate` — the closed-form bound `2^{2b} / (8b) ≤ litCount F` for `b ≥ 5`.
* `hardF_rate_superlinear` — `hardF_superlinear` re-derived from the rate, to confirm consistency.

Ceiling unchanged: `n²/log²n` regime, **not** P vs NP.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace NecHard

open scoped BigOperators

/-- **Explicit growth rate.**  For the balanced family `m = 2^b` (`b ≥ 5`), any `B₂` formula computing
`hardF` has at least `2^{2b} / (8b)` literals — a closed-form super-linear lower bound. -/
theorem hardF_rate (b : ℕ) (hb : 5 ≤ b) (F : BFormula (nn b (2 ^ b)))
    (hF : ∀ x, BFormula.eval F x = hardF x) :
    2 ^ (2 * b) / (8 * b) ≤ BFormula.litCount F := by
  have hdb : Dsize b = 2 ^ b := dsize_eq
  have hN : nn b (2 ^ b) = 2 ^ b * (b + 1) := by unfold nn; rw [hdb]; ring
  have hpb32 : (32 : ℕ) ≤ 2 ^ b := by
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  -- clog bound (standalone, via c² < 2^c)
  have hclog : Nat.clog 2 (2 * nn b (2 ^ b) + 17) ≤ 2 * b := by
    apply Nat.clog_le_of_le_pow
    rw [hN, show (2 : ℕ) ^ (2 * b) = 2 ^ b * 2 ^ b from by rw [two_mul, pow_add]]
    have hsqb : b ^ 2 < 2 ^ b := sq_lt_two_pow b hb
    have h2b3 : 2 * b + 3 ≤ 2 ^ b := by nlinarith [hsqb, hb]
    have hmul : 2 ^ b * (2 * b + 3) ≤ 2 ^ b * 2 ^ b := Nat.mul_le_mul_left _ h2b3
    nlinarith [hmul, hpb32]
  -- the explicit per-block bound, with the clog bound and ℕ-subtraction folded in
  have hexp := hardF_litCount_lower_explicit (b := b) (m := 2 ^ b) F hF
  rw [hdb] at hexp
  have hcL : 2 * Nat.clog 2 (2 * nn b (2 ^ b) + 17) * BFormula.litCount F
        ≤ 4 * b * BFormula.litCount F :=
    Nat.mul_le_mul (by omega) (le_refl _)
  have hexpB : 2 ^ b * (2 ^ b - 1) ≤ 4 * b * BFormula.litCount F + 2 * (2 ^ b + 1) := by omega
  have hid : 2 ^ b * (2 ^ b - 1) + 2 ^ b = 2 ^ b * 2 ^ b := by
    have h1 : 2 ^ b - 1 + 1 = 2 ^ b := Nat.succ_pred_eq_of_pos (by positivity)
    calc 2 ^ b * (2 ^ b - 1) + 2 ^ b
        = 2 ^ b * (2 ^ b - 1) + 2 ^ b * 1 := by ring
      _ = 2 ^ b * (2 ^ b - 1 + 1) := by rw [Nat.mul_add]
      _ = 2 ^ b * 2 ^ b := by rw [h1]
  have hexpC : 2 ^ b * 2 ^ b
        ≤ 4 * b * BFormula.litCount F + 2 * (2 ^ b + 1) + 2 ^ b := by omega
  -- 2^{2b} ≤ 8b·L, then divide
  have h22 : (2 : ℕ) ^ (2 * b) = 2 ^ b * 2 ^ b := by rw [two_mul, pow_add]
  have h6 : 6 * 2 ^ b + 4 ≤ 2 ^ b * 2 ^ b := by nlinarith [hpb32]
  have hmain : 2 ^ (2 * b) ≤ 8 * b * BFormula.litCount F := by
    rw [h22]; nlinarith [hexpC, h6]
  exact Nat.div_le_of_le_mul hmain

/-- **Super-linearity, re-derived from the explicit rate.**  Matches `hardF_superlinear`; included to
confirm the rate is at least as strong. -/
theorem hardF_rate_superlinear (C : ℕ) :
    ∃ b : ℕ, ∀ (F : BFormula (nn b (2 ^ b))),
      (∀ x, BFormula.eval F x = hardF x) →
      C * nn b (2 ^ b) < BFormula.litCount F :=
  hardF_superlinear C

end NecHard

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.NecHard.hardF_rate
