import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukQsetBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukHardFunctionSquare

/-!
# The rewire: optimal Nečiporuk formula lower bound (constant per leaf) + `hardF` re-derivation

`neciporuk_formula_lower_bound` charged `clog₂(|Tok n|) ≈ log n` bits per leaf, capping the formalised
`hardF` bound at `N²/log²N`.  `card_blockResiduals_le_pow` replaced that charge by a **constant** `4`.
This file rewires the formula lower bound accordingly and re-derives the `hardF` bound with a constant
denominator — the optimal Nečiporuk `n²/log n` regime.

* `log_card_blockResiduals_le` — `log₂ s_i ≤ 4·leavesIn(S_i) + 1` (from `card_blockResiduals_le_pow`).
* `neciporuk_formula_lower_bound_opt` — `∑ᵢ log₂ s_i ≤ 4·litCount F + #blocks` (constant per leaf;
  no `log n`).
* `hardF_litCount_lower_opt` — `m·(2^b − 1) ≤ 4·litCount F + (m + 1)` for any `B₂` formula computing
  `hardF` (was `≤ 2·clog₂(…)·litCount + 2(m+1)`).
* `hardF_litCount_lower_opt_div` — headline: `litCount F ≥ (m·(2^b − 1) − (m+1)) / 4`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open BFormula
open scoped BigOperators

variable {n : ℕ}

/-- `log₂ s_i ≤ 4·leavesIn(S_i) + 1` — the constant-per-leaf log bound. -/
theorem log_card_blockResiduals_le (S : Finset (Fin n)) (F : BFormula n) :
    Nat.log 2 ((blockResiduals S F).card) ≤ 4 * BFormula.leavesIn S F + 1 := by
  have h := card_blockResiduals_le_pow S F
  have he : 2 * 16 ^ (BFormula.leavesIn S F) = 2 ^ (4 * BFormula.leavesIn S F + 1) := by
    rw [show (16 : ℕ) = 2 ^ 4 from by norm_num, ← pow_mul, ← pow_succ']
  rw [he] at h
  calc Nat.log 2 ((blockResiduals S F).card)
      ≤ Nat.log 2 (2 ^ (4 * BFormula.leavesIn S F + 1)) := Nat.log_mono_right h
    _ = 4 * BFormula.leavesIn S F + 1 := Nat.log_pow (by norm_num) _

/-- **The rewire.**  Optimal Nečiporuk formula lower bound: `∑ᵢ log₂ s_i ≤ 4·litCount F + #blocks`.
A *constant* `4` per leaf, replacing the spurious `clog₂(|Tok n|) ≈ log n` charge. -/
theorem neciporuk_formula_lower_bound_opt {ι : Type*}
    (blocks : Finset ι) (S : ι → Finset (Fin n)) (F : BFormula n)
    (hdisj : (blocks : Set ι).PairwiseDisjoint S)
    (hcover : blocks.biUnion S = Finset.univ) :
    ∑ i ∈ blocks, Nat.log 2 ((blockResiduals (S i) F).card)
      ≤ 4 * BFormula.litCount F + blocks.card := by
  calc ∑ i ∈ blocks, Nat.log 2 ((blockResiduals (S i) F).card)
      ≤ ∑ i ∈ blocks, (4 * BFormula.leavesIn (S i) F + 1) :=
        Finset.sum_le_sum (fun i _ => log_card_blockResiduals_le (S i) F)
    _ = 4 * (∑ i ∈ blocks, BFormula.leavesIn (S i) F) + blocks.card := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul, Nat.mul_one]
    _ = 4 * BFormula.litCount F + blocks.card := by
        rw [BFormula.sum_leavesIn_of_partition blocks S F hdisj hcover]

namespace NecHard

variable {b m : ℕ}

/-- **`hardF` lower bound, rewired.**  `m·(2^b − 1) ≤ 4·litCount F + (m + 1)` — constant denominator,
no `log n` factor (cf. `hardF_litCount_lower` with `2·clog₂(…)·litCount + 2(m+1)`). -/
theorem hardF_litCount_lower_opt (F : BFormula (nn b m))
    (hF : ∀ x, BFormula.eval F x = hardF x) :
    m * (Dsize b - 1) ≤ 4 * BFormula.litCount F + (m + 1) := by
  classical
  have hnec := neciporuk_formula_lower_bound_opt
    (Finset.univ : Finset (Option (Fin m))) (blkS (b := b) (m := m)) F blkS_disj blkS_cover
  rw [Finset.card_univ, Fintype.card_option, Fintype.card_fin] at hnec
  have hconst : ∑ _k : Fin m, (Dsize b - 1) = m * (Dsize b - 1) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hper : ∀ k : Fin m,
      Dsize b - 1 ≤ Nat.log 2 ((blockResiduals (blkS (some k)) F).card) := by
    intro k
    rw [blkS_some]
    exact log_card_blockResiduals_hardF_ge k F hF
  have hge : m * (Dsize b - 1)
      ≤ ∑ k : Fin m, Nat.log 2 ((blockResiduals (blkS (some k)) F).card) :=
    hconst ▸ Finset.sum_le_sum (fun k _ => hper k)
  have hlow : m * (Dsize b - 1)
      ≤ ∑ o : Option (Fin m), Nat.log 2 ((blockResiduals (blkS o) F).card) := by
    rw [Fintype.sum_option]
    exact le_trans hge (Nat.le_add_left _ _)
  exact le_trans hlow hnec

/-- **Headline (division form), rewired.**  `litCount F ≥ (m·(2^b − 1) − (m+1)) / 4` — constant
denominator `4` (was `2·clog₂(2·nn + 17) ≈ log n`). -/
theorem hardF_litCount_lower_opt_div (F : BFormula (nn b m))
    (hF : ∀ x, BFormula.eval F x = hardF x) :
    (m * (Dsize b - 1) - (m + 1)) / 4 ≤ BFormula.litCount F := by
  have h := hardF_litCount_lower_opt F hF
  have key : m * (Dsize b - 1) - (m + 1) ≤ 4 * BFormula.litCount F := by omega
  calc (m * (Dsize b - 1) - (m + 1)) / 4
      ≤ (4 * BFormula.litCount F) / 4 := Nat.div_le_div_right key
    _ = BFormula.litCount F := by rw [Nat.mul_div_cancel_left _ (by norm_num)]

/-- **Optimal `N²/log N` rate.**  Under the balance bounds (`2^b ≤ 2·m·b ≤ 2·2^b`), any `B₂` formula
computing `hardF` has `litCount F ≥ (nn b m)² / (64·b)` — denominator *linear* in `b ≈ log N` (vs the
`b²` of `hardF_rate_sq`), i.e. the true Nečiporuk `n²/log n`. -/
theorem hardF_rate_sq_opt (m b : ℕ) (hb : 5 ≤ b)
    (hlo : 2 ^ b ≤ 2 * (m * b)) (hhi : m * b ≤ 2 ^ b)
    (F : BFormula (nn b m)) (hF : ∀ x, BFormula.eval F x = hardF x) :
    (nn b m) ^ 2 / (64 * b) ≤ BFormula.litCount F := by
  have hdb : Dsize b = 2 ^ b := dsize_eq
  have hNval : nn b m = m * b + 2 ^ b := by unfold nn; rw [hdb]
  have hpb32 : (32 : ℕ) ≤ 2 ^ b := by
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have hNub : nn b m ≤ 2 * 2 ^ b := by rw [hNval]; omega
  have hexp := hardF_litCount_lower_opt (b := b) (m := m) F hF
  rw [hdb] at hexp
  have hfold : m * 2 ^ b = m * (2 ^ b - 1) + m := by
    have h1 : 2 ^ b - 1 + 1 = 2 ^ b := Nat.succ_pred_eq_of_pos (by positivity)
    calc m * 2 ^ b = m * (2 ^ b - 1 + 1) := by rw [h1]
      _ = m * (2 ^ b - 1) + m := by ring
  have hexp2 : m * 2 ^ b ≤ 4 * BFormula.litCount F + 2 * m + 1 := by rw [hfold]; omega
  have hA : 2 * b * (m * 2 ^ b) ≤ 2 * b * (4 * BFormula.litCount F + 2 * m + 1) :=
    Nat.mul_le_mul_left _ hexp2
  have hB : 4 * (m * b) ≤ 4 * 2 ^ b := Nat.mul_le_mul_left _ hhi
  have h8 : 8 * 2 ^ b + 4 * b ≤ 2 ^ b * 2 ^ b := by
    nlinarith [hpb32, Nat.lt_two_pow_self (n := b)]
  have hmain : 2 ^ b * 2 ^ b ≤ 16 * b * BFormula.litCount F := by
    nlinarith [mul_le_mul_right' hlo (2 ^ b), hA, hB, h8]
  have hN2 : (nn b m) ^ 2 ≤ 64 * b * BFormula.litCount F := by
    have h1 : (nn b m) ^ 2 ≤ (2 * 2 ^ b) ^ 2 := Nat.pow_le_pow_left hNub 2
    nlinarith [h1, hmain]
  exact Nat.div_le_of_le_mul hN2

/-- **Headline (optimal).**  For every `b ≥ 5`, a block count `m` exists for which any `B₂` formula
computing the `nn b m`-variable `hardF` has `litCount F ≥ (nn b m)² / (64·b) = Ω(N²/log N)` — the
classic Nečiporuk optimal, with the `log n` factor removed. -/
theorem hardF_rate_opt_family (b : ℕ) (hb : 5 ≤ b) :
    ∃ m, ∀ (F : BFormula (nn b m)), (∀ x, BFormula.eval F x = hardF x) →
      (nn b m) ^ 2 / (64 * b) ≤ BFormula.litCount F := by
  obtain ⟨m, hlo, hhi⟩ := exists_balanced_m b hb
  exact ⟨m, fun F hF => hardF_rate_sq_opt m b hb hlo hhi F hF⟩

end NecHard

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.neciporuk_formula_lower_bound_opt
#print axioms PallLean.Paper93.DeepMath.PathB.NecHard.hardF_litCount_lower_opt_div
