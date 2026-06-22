import Mathlib

/-!
# Hard math (Toda/Razborov–Smolensky MOD degree) — `MOD_p` is degree `p−1` over `F_p` (proved)

The base case of the composite-`MOD` Toda degree bound: the prime-modulus `MOD_p` indicator has an **exact** low-degree
polynomial over `F_p`.  Via Fermat's little theorem, `[∑_{i∈S} x_i ≡ 0 mod p] = 1 − (∑_{i∈S} x_i)^{p−1}` over `ZMod p`
(`modpPoly`): the sum is degree `1`, raised to `p−1`, so the polynomial has total degree `≤ p−1` (`modpPoly_degree`), and it
is eval-correct — it equals the `MOD_p` residue-`0` indicator on Boolean inputs (`modpPoly_eval`), because `a^{p−1}` is `0`
when `a = 0` and `1` otherwise (Fermat).

This is the genuinely hard combinatorics' base rung: a single `MOD_p` gate has degree `p−1 = O(1)` in its fan-in — the
low-degree input that drives Beigel–Tarui's quasipolynomial `SYM∘AND` count.  (For composite `m = ∏ p_i^{a_i}`, CRT +
prime-power lifting reduce to this; the prime-power case is the remaining rung.)

## What is proved (clean axioms, no `sorry`)

* **`modpPoly`** — `1 − (∑_{i∈S} X_i)^{p−1}` over `ZMod p`.
* **`modpPoly_degree`** (PROVED) — `totalDegree (modpPoly p S) ≤ p − 1`.
* **`modpPoly_eval`** (PROVED) — `modpPoly p S` evaluates to the `MOD_p` residue-`0` indicator on Boolean inputs.

## Honest scope

This is the prime-modulus base case of the Toda/RS `MOD` degree (degree `p−1` over `F_p`).  Composite `m` needs the
prime-power lifting + CRT (the remaining hard rung); unconditional `NEXP ⊄ ACC⁰` is P≠NP-strength.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModpTodaPoly

open MvPolynomial Finset

variable {n : ℕ} (p : ℕ) [Fact p.Prime]

/-- The Boolean value as an `F_p` element. -/
def bv (b : Bool) : ZMod p := if b then 1 else 0

/-- The linear sum `∑_{i∈S} X_i` over `F_p`. -/
noncomputable def sumPoly (S : Finset (Fin n)) : MvPolynomial (Fin n) (ZMod p) := ∑ i ∈ S, X i

/-- **The Toda/RS `MOD_p` polynomial: `1 − (∑ X_i)^{p−1}` over `F_p`.** -/
noncomputable def modpPoly (S : Finset (Fin n)) : MvPolynomial (Fin n) (ZMod p) :=
  1 - (sumPoly p S) ^ (p - 1)

theorem sumPoly_degree (S : Finset (Fin n)) : (sumPoly p S).totalDegree ≤ 1 := by
  refine le_trans (totalDegree_finset_sum _ _) (Finset.sup_le ?_)
  intro i _; exact (totalDegree_X i).le

/-- **`MOD_p` has total degree `≤ p−1` over `F_p` (PROVED).** -/
theorem modpPoly_degree (S : Finset (Fin n)) : (modpPoly p S).totalDegree ≤ p - 1 := by
  refine le_trans (totalDegree_sub _ _) (max_le ?_ ?_)
  · simp [totalDegree_one]
  · refine le_trans (totalDegree_pow _ _) ?_
    refine le_trans (Nat.mul_le_mul_left _ (sumPoly_degree p S)) ?_
    simp

/-- **The Toda `MOD_p` polynomial is eval-correct: it is the `MOD_p` residue-`0` indicator on Boolean inputs (PROVED).** -/
theorem modpPoly_eval (S : Finset (Fin n)) (x : Fin n → Bool) :
    eval (fun i => bv p (x i)) (modpPoly p S)
      = if (∑ i ∈ S, bv p (x i)) = 0 then 1 else 0 := by
  have hsum : eval (fun i => bv p (x i)) (sumPoly p S) = ∑ i ∈ S, bv p (x i) := by
    simp [sumPoly, map_sum, eval_X]
  simp only [modpPoly, map_sub, map_one, map_pow, hsum]
  have hp1 : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).two_le; omega
  by_cases h : (∑ i ∈ S, bv p (x i)) = 0
  · rw [if_pos h, h, zero_pow hp1, sub_zero]
  · rw [ZMod.pow_card_sub_one_eq_one h, sub_self, if_neg h]

/-!
**`MOD_p` is degree `p−1` over `F_p`, proved.**  The exact low-degree Toda/RS representation of the prime-modulus `MOD` gate —
the base rung of the composite-`MOD` degree bound that drives Beigel–Tarui.  Remaining (open, not faked): the prime-power /
CRT lifting for composite `m`, and the unconditional `NEXP ⊄ ACC⁰`.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModpTodaPoly

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModpTodaPoly.modpPoly_degree
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModpTodaPoly.modpPoly_eval
