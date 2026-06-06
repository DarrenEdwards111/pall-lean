import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukHardFunctionAsymptotic

/-!
# Nečiporuk concrete hard function (Stage 7): the optimal `N²/log²N` rate

`hardF_rate` (Stage 6) gave `litCount ≥ 2^{2b}/(8b) ≈ N²/log³N` for the *balanced* family `m = 2^b`.
That choice is suboptimal: the method `neciporuk_formula_lower_bound` is tight, but balancing the block
count against the *data* region wastes a `log` factor.  The right choice balances the **address**
region against the data region: `m·b ≈ 2^b` (so both halves are `≈ N/2`).  This reaches the documented
ceiling for this formalisation, `N²/log²N`.

* `exists_balanced_m` — for `b ≥ 5`, some `m` has `2^b ≤ 2·(m·b)` and `m·b ≤ 2^b` (`m = 2^b / b`).
* `hardF_rate_sq` — under those two balance bounds, any `B₂` formula computing `hardF` has
  `litCount F ≥ (nn b m)² / (64·b²)`.
* `hardF_rate_sq_family` — the headline: for every `b ≥ 5`, some `m` makes
  `litCount F ≥ (nn b m)² / (64·b²)` for any formula computing the `nn b m`-variable `hardF`.

Since `b ≈ log₂(nn b m)`, this is `litCount ≥ Ω(N² / log²N)` — the classic Nečiporuk-formalisation
ceiling.  Still a genuine **restricted** lower bound, **not** P vs NP.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace NecHard

open scoped BigOperators

/-- A block count `m` balancing the address region against the data region: `m·b ≈ 2^b`. -/
theorem exists_balanced_m (b : ℕ) (hb : 5 ≤ b) :
    ∃ m, 2 ^ b ≤ 2 * (m * b) ∧ m * b ≤ 2 ^ b := by
  refine ⟨2 ^ b / b, ?_, Nat.div_mul_le_self _ _⟩
  have hbpos : 0 < b := by omega
  have hmod := Nat.mod_add_div (2 ^ b) b
  have hmlt : 2 ^ b % b < b := Nat.mod_lt _ hbpos
  have hpow2b : 2 * b ≤ 2 ^ b := by nlinarith [sq_lt_two_pow b hb, hb]
  have hcomm : b * (2 ^ b / b) = (2 ^ b / b) * b := Nat.mul_comm _ _
  omega

/-- **The optimal `N²/log²N` rate.**  When the address region balances the data region
(`2^b ≤ 2·m·b ≤ 2·2^b`), any `B₂` formula computing `hardF` has `litCount F ≥ (nn b m)² / (64·b²)`. -/
theorem hardF_rate_sq (m b : ℕ) (hb : 5 ≤ b)
    (hlo : 2 ^ b ≤ 2 * (m * b)) (hhi : m * b ≤ 2 ^ b)
    (F : BFormula (nn b m)) (hF : ∀ x, BFormula.eval F x = hardF x) :
    (nn b m) ^ 2 / (64 * b ^ 2) ≤ BFormula.litCount F := by
  have hdb : Dsize b = 2 ^ b := dsize_eq
  have hNval : nn b m = m * b + 2 ^ b := by unfold nn; rw [hdb]
  have hpb32 : (32 : ℕ) ≤ 2 ^ b := by
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have hNub : nn b m ≤ 2 * 2 ^ b := by rw [hNval]; omega
  -- clog bound: 2·nn + 17 ≤ 4^b
  have hclog : Nat.clog 2 (2 * nn b m + 17) ≤ 2 * b := by
    apply Nat.clog_le_of_le_pow
    rw [show (2 : ℕ) ^ (2 * b) = 2 ^ b * 2 ^ b from by rw [two_mul, pow_add]]
    have h1 : 2 * nn b m + 17 ≤ 4 * 2 ^ b + 17 := by omega
    nlinarith [hpb32, h1]
  -- explicit per-block bound, clog-bounded, ℕ-subtraction folded away
  have hexp := hardF_litCount_lower_explicit (b := b) (m := m) F hF
  rw [hdb] at hexp
  have hexpB : m * (2 ^ b - 1) ≤ 4 * b * BFormula.litCount F + 2 * (m + 1) := by
    have hcL : 2 * Nat.clog 2 (2 * nn b m + 17) * BFormula.litCount F
          ≤ 4 * b * BFormula.litCount F := Nat.mul_le_mul (by omega) (le_refl _)
    omega
  have hfold : m * 2 ^ b = m * (2 ^ b - 1) + m := by
    have h1 : 2 ^ b - 1 + 1 = 2 ^ b := Nat.succ_pred_eq_of_pos (by positivity)
    calc m * 2 ^ b = m * (2 ^ b - 1 + 1) := by rw [h1]
      _ = m * (2 ^ b - 1) + m := by ring
  have hexp2 : m * 2 ^ b ≤ 4 * b * BFormula.litCount F + 3 * m + 2 := by rw [hfold]; omega
  -- assemble 2^{2b} ≤ 16 b² L
  have hA : 2 * b * (m * 2 ^ b)
        ≤ 2 * b * (4 * b * BFormula.litCount F + 3 * m + 2) :=
    Nat.mul_le_mul_left _ hexp2
  have hB : 6 * (m * b) ≤ 6 * 2 ^ b := Nat.mul_le_mul_left _ hhi
  have h12 : 12 * 2 ^ b + 8 * b ≤ 2 ^ b * 2 ^ b := by
    nlinarith [hpb32, Nat.lt_two_pow_self (n := b)]
  have hmain : 2 ^ b * 2 ^ b ≤ 16 * b ^ 2 * BFormula.litCount F := by
    nlinarith [mul_le_mul_right' hlo (2 ^ b), hA, hB, h12]
  -- N² ≤ 4·2^{2b} ≤ 64 b² L, then divide
  have hN2 : (nn b m) ^ 2 ≤ 64 * b ^ 2 * BFormula.litCount F := by
    have h1 : (nn b m) ^ 2 ≤ (2 * 2 ^ b) ^ 2 := Nat.pow_le_pow_left hNub 2
    nlinarith [h1, hmain]
  exact Nat.div_le_of_le_mul hN2

/-- **Headline.**  For every depth `b ≥ 5`, a block count `m` exists for which any `B₂` formula
computing the `nn b m`-variable `hardF` has `litCount F ≥ (nn b m)² / (64·b²) = Ω(N²/log²N)`. -/
theorem hardF_rate_sq_family (b : ℕ) (hb : 5 ≤ b) :
    ∃ m, ∀ (F : BFormula (nn b m)), (∀ x, BFormula.eval F x = hardF x) →
      (nn b m) ^ 2 / (64 * b ^ 2) ≤ BFormula.litCount F := by
  obtain ⟨m, hlo, hhi⟩ := exists_balanced_m b hb
  exact ⟨m, fun F hF => hardF_rate_sq m b hb hlo hhi F hF⟩

end NecHard

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.NecHard.hardF_rate_sq
#print axioms PallLean.Paper93.DeepMath.PathB.NecHard.hardF_rate_sq_family
