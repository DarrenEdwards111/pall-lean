import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukHardFunctionExplicit

/-!
# Nečiporuk concrete hard function (Stage 5): genuine asymptotic super-linearity

Stage 4 exhibited one numeric instance with `litCount / N > 3`.  This file proves the real content of
the Nečiporuk method: the formula-size lower bound is **super-linear** — it beats *every* constant
multiple of the variable count.

Working in the balanced family `m = 2^b` (so the data region size equals the number of address
blocks), the variable count is `N(b) = nn b (2^b) = 2^b·(b+1)` and the proven bound gives
`litCount ≳ 2^{2b} / b`, whose ratio to `N(b)` is `≈ 2^b / (b·(b+1)) → ∞`.

* `sq_lt_two_pow` — `c² < 2^c` for `c ≥ 5` (induction).
* `expBeatsQuad` — for every `a`, some `b ≥ 5` has `a·b² < 2^b` (the base point `b = 2·max 5 (a+2)`
  uses `c² < 2^c` and `a < 2^a`).
* `hardF_superlinear` — **the theorem**: for every `C`, there is a Reynolds-free choice of `b` such
  that *any* `B₂` formula computing the balanced-family `hardF` has `litCount F > C · nn b (2^b)`.

So no linear bound `C·N` survives: the explicit family has super-linear formula size.  This is the
genuine `n²/log²n`-flavoured separation content — still **not** P vs NP.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace NecHard

open scoped BigOperators

/-! ## Exponential beats quadratic -/

/-- `c² < 2^c` for `c ≥ 5`. -/
theorem sq_lt_two_pow (c : ℕ) (hc : 5 ≤ c) : c ^ 2 < 2 ^ c := by
  induction c, hc using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hstep : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith [hn]
    calc (n + 1) ^ 2 ≤ 2 * n ^ 2 := hstep
      _ < 2 * 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- For every `a`, some `b ≥ 5` satisfies `a·b² < 2^b` (exponential dominates any quadratic). -/
theorem expBeatsQuad (a : ℕ) : ∃ b, 5 ≤ b ∧ a * b ^ 2 < 2 ^ b := by
  set c := max 5 (a + 2) with hcdef
  have hc5 : 5 ≤ c := le_max_left _ _
  have hca : a + 2 ≤ c := le_max_right _ _
  refine ⟨2 * c, by omega, ?_⟩
  have hsq : c ^ 2 < 2 ^ c := sq_lt_two_pow c hc5
  have h4a : 4 * a < 2 ^ c := by
    have h1 : a < 2 ^ a := Nat.lt_two_pow_self
    have he : (2 : ℕ) ^ (a + 2) = 4 * 2 ^ a := by rw [pow_add]; ring
    have h3 : 4 * a < 2 ^ (a + 2) := by rw [he]; omega
    have h2 : 2 ^ (a + 2) ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) hca
    omega
  have hrw : a * (2 * c) ^ 2 = 4 * a * c ^ 2 := by ring
  rw [hrw]
  calc 4 * a * c ^ 2 < 2 ^ c * 2 ^ c := Nat.mul_lt_mul'' h4a hsq
    _ = 2 ^ (2 * c) := by rw [two_mul, pow_add]

/-! ## The super-linearity theorem -/

/-- **The Nečiporuk lower bound is super-linear.**  For every constant `C`, there is a depth
parameter `b` such that *any* `B₂` formula computing the balanced-family hard function `hardF`
(`m = 2^b`, `N = nn b (2^b) = 2^b·(b+1)` variables) has more than `C·N` literals.  Hence no linear
lower bound `C·N` is best possible — the family has super-linear formula size. -/
theorem hardF_superlinear (C : ℕ) :
    ∃ b : ℕ, ∀ (F : BFormula (nn b (2 ^ b))),
      (∀ x, BFormula.eval F x = hardF x) →
      C * nn b (2 ^ b) < BFormula.litCount F := by
  obtain ⟨b, hb5, hbig⟩ := expBeatsQuad (8 * C + 4)
  refine ⟨b, fun F hF => ?_⟩
  -- layout values
  have hdb : Dsize b = 2 ^ b := dsize_eq
  have hN : nn b (2 ^ b) = 2 ^ b * (b + 1) := by unfold nn; rw [hdb]; ring
  have hpb32 : (32 : ℕ) ≤ 2 ^ b := by
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb5
  -- clog bound: 2N + 17 ≤ 4^b, so clog ≤ 2b
  have hclog : Nat.clog 2 (2 * nn b (2 ^ b) + 17) ≤ 2 * b := by
    apply Nat.clog_le_of_le_pow
    rw [hN, show (2 : ℕ) ^ (2 * b) = 2 ^ b * 2 ^ b from by rw [two_mul, pow_add]]
    have h4b2 : 4 * b ^ 2 < 2 ^ b := by nlinarith [hbig, Nat.zero_le (C * b ^ 2)]
    have h5b : 5 * b ≤ b ^ 2 := by nlinarith [hb5]
    have h2b3 : 2 * b + 3 ≤ 2 ^ b := by nlinarith [h4b2, h5b, hb5]
    have hmul : 2 ^ b * (2 * b + 3) ≤ 2 ^ b * 2 ^ b := Nat.mul_le_mul_left _ h2b3
    nlinarith [hmul, hpb32]
  -- the explicit per-block bound with m = 2^b
  have hexp := hardF_litCount_lower_explicit (b := b) (m := 2 ^ b) F hF
  rw [hdb] at hexp
  -- replace 2·clog·L ≤ 4b·L
  have hcL : 2 * Nat.clog 2 (2 * nn b (2 ^ b) + 17) * BFormula.litCount F
        ≤ 4 * b * BFormula.litCount F := by
    have hle : 2 * Nat.clog 2 (2 * nn b (2 ^ b) + 17) ≤ 4 * b := by omega
    exact Nat.mul_le_mul hle (le_refl _)
  have hexpB : 2 ^ b * (2 ^ b - 1) ≤ 4 * b * BFormula.litCount F + 2 * (2 ^ b + 1) := by omega
  -- kill the ℕ subtraction
  have hid : 2 ^ b * (2 ^ b - 1) + 2 ^ b = 2 ^ b * 2 ^ b := by
    have h1 : 2 ^ b - 1 + 1 = 2 ^ b := Nat.succ_pred_eq_of_pos (by positivity)
    calc 2 ^ b * (2 ^ b - 1) + 2 ^ b
        = 2 ^ b * (2 ^ b - 1) + 2 ^ b * 1 := by ring
      _ = 2 ^ b * (2 ^ b - 1 + 1) := by rw [Nat.mul_add]
      _ = 2 ^ b * 2 ^ b := by rw [h1]
  have hexpC : 2 ^ b * 2 ^ b
        ≤ 4 * b * BFormula.litCount F + 2 * (2 ^ b + 1) + 2 ^ b := by omega
  -- the chosen b makes 4·C·b·(b+1) + 4 ≤ 2^b
  have hbb : b ≤ b ^ 2 := by nlinarith [hb5]
  have hQbig : 4 * C * b * (b + 1) + 4 ≤ 2 ^ b := by
    have key : 4 * C * b * (b + 1) + 4 ≤ (8 * C + 4) * b ^ 2 := by
      nlinarith [hbb, hb5, Nat.zero_le C]
    omega
  -- product fact and the final cancellation
  have hprod : (4 * C * b * (b + 1) + 4) * 2 ^ b ≤ 2 ^ b * 2 ^ b :=
    Nat.mul_le_mul hQbig (le_refl _)
  have hgoaleq : C * nn b (2 ^ b) = C * (2 ^ b * (b + 1)) := by rw [hN]
  rw [hgoaleq]
  have hbig2 : 4 * b * (C * (2 ^ b * (b + 1))) < 4 * b * BFormula.litCount F := by
    nlinarith [hexpC, hprod, hpb32]
  exact lt_of_mul_lt_mul_left hbig2 (Nat.zero_le _)

end NecHard

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.NecHard.expBeatsQuad
#print axioms PallLean.Paper93.DeepMath.PathB.NecHard.hardF_superlinear
