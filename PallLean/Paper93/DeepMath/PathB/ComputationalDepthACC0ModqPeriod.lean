import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModqFourier

/-!
# Brick (MOD_q period) — unconditional `MOD_q ∉` constant-depth `AC⁰[p]` for `n ≡ 1 mod (p−1)` (proved)

Discharging the conditional separation (Brick MOD_q indicator) for an infinite family of arities.  By Fermat, each
`(1−ζʲ) ∈ F_p^*` satisfies `(1−ζʲ)^{p−1} = 1`, so `(1−ζʲ)^n` is periodic in `n` with period `p−1`.  For `n ≡ 1 mod (p−1)`,
`(1−ζʲ)^n = 1−ζʲ`, hence the character sum `∑_{j<q}(1−ζʲ)^n = ∑_{j<q}(1−ζʲ) = q` (the `ζʲ` sum vanishes), and so
`Dsign(MOD_q) = q⁻¹·q = 1 ≠ 0` (`Dsign_modq_eq_one`).  Plugging into the conditional separation gives `MOD_q ∉` constant-depth
`AC⁰[p]` **unconditionally** for every `n ≡ 1 mod (p−1)` (with `(p−1)·2^d < n`).

For constant depth `d` and fixed odd `p`, `q` (with `q ∣ p−1`), this is the Razborov–Smolensky separation `MOD_q ∉ AC⁰[p]`
for infinitely many `n` — a genuine, unconditional, in-framework lower bound for `MOD_q`, `q > 2`.

## What is proved (clean axioms, no `sorry`)

* **`pow_eq_self_period`** (PROVED) — `x ≠ 0 → (p−1)∣(n−1) → 1 ≤ n → x^n = x` over `F_p`.
* **`Dsign_modq_eq_one`** (PROVED) — `n ≡ 1 mod (p−1) → Dsign(MOD_q) = 1`.
* **`modq_not_acc0p_depth_period`** (PROVED) — `n ≡ 1 mod (p−1), (p−1)·2^d < n → MOD_q ∉` depth-`d` `AC⁰[p]`, *unconditionally*.

## Honest scope

The unconditional `MOD_q` separation for `n ≡ 1 mod (p−1)` (an infinite family of arities; `ζ` a primitive `q`-th root,
`q ∣ p−1`).  It does **not** cover *all* large `n` (the full RS rank bound; tree's `Layer4`) nor the Williams cash-out.
General YBT and `NEXP ⊄ ACC⁰` remain open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModqPeriod

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit depth)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP (ModpOnly)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitRepr (bv)
open PallLean.Paper93.DeepMath.PathB.ACC0ParityWitness (signWt)
open PallLean.Paper93.DeepMath.PathB.ACC0ModqWitness (modqFn modq_not_acc0p_depth)
open PallLean.Paper93.DeepMath.PathB.ACC0ModqFourier (Dsign_modq)

variable {n p : ℕ} [Fact p.Prime]

/-- **`x^n = x` over `F_p` when `n ≡ 1 mod (p−1)` and `x ≠ 0` (PROVED).** -/
theorem pow_eq_self_period {x : ZMod p} (hx : x ≠ 0) (hper : (p - 1) ∣ (n - 1)) (hn1 : 1 ≤ n) :
    x ^ n = x := by
  obtain ⟨k, hk⟩ := hper
  have hn : n = 1 + (p - 1) * k := by omega
  rw [hn, pow_add, pow_one, pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow, mul_one]

/-- **`Dsign(MOD_q) = 1` for `n ≡ 1 mod (p−1)` (PROVED).** -/
theorem Dsign_modq_eq_one (q : ℕ) (hq2 : 2 ≤ q) (hq : (q : ZMod p) ≠ 0) (ζ : ZMod p)
    (hord : orderOf ζ = q) (hn1 : 1 ≤ n) (hper : (p - 1) ∣ (n - 1)) :
    (∑ x : Fin n → Bool, signWt p x * (bv (modqFn q x) : ZMod p)) = 1 := by
  rw [Dsign_modq q hq ζ hord]
  have hζ1 : ζ ≠ 1 := by intro h; rw [h, orderOf_one] at hord; omega
  have hsum : (∑ j ∈ Finset.range q, (1 - ζ ^ j) ^ n) = q := by
    have hpe : ∀ j ∈ Finset.range q, (1 - ζ ^ j) ^ n = 1 - ζ ^ j := by
      intro j _
      by_cases hz : (1 - ζ ^ j) = 0
      · rw [hz, zero_pow (by omega)]
      · exact pow_eq_self_period hz hper hn1
    rw [Finset.sum_congr rfl hpe, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    have hgeom : (∑ j ∈ Finset.range q, ζ ^ j) = 0 := by
      rw [geom_sum_eq hζ1 q, show ζ ^ q = 1 by rw [← hord, pow_orderOf_eq_one], sub_self, zero_div]
    rw [hgeom, sub_zero]
  rw [hsum, inv_mul_cancel₀ hq]

/-- **Unconditional `MOD_q ∉` constant-depth `AC⁰[p]` for `n ≡ 1 mod (p−1)` (PROVED).** -/
theorem modq_not_acc0p_depth_period (hp2 : p ≠ 2) (q : ℕ) (hq2 : 2 ≤ q) (hq : (q : ZMod p) ≠ 0)
    (ζ : ZMod p) (hord : orderOf ζ = q) (hn1 : 1 ≤ n) (hper : (p - 1) ∣ (n - 1)) {d : ℕ}
    (hd : (p - 1) * 2 ^ d < n) :
    ¬ ∃ C : ACC0Circuit n, ModpOnly p C ∧ depth C ≤ d ∧ ACC0CircuitModel.eval C = modqFn q :=
  modq_not_acc0p_depth hp2 q
    (by rw [Dsign_modq_eq_one q hq2 hq ζ hord hn1 hper]; exact one_ne_zero) hd

/-!
**The periodic `MOD_q` separation, proved.**  For `n ≡ 1 mod (p−1)`, `Dsign(MOD_q) = 1`, so `MOD_q ∉` constant-depth
`AC⁰[p]` unconditionally — an infinite family of arities, the genuine `q>2` Razborov–Smolensky separation (for these `n`).
Remaining (open, not faked): all large `n` (RS rank bound), Williams cash-out.  Not `NEXP ⊄ ACC⁰`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModqPeriod

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModqPeriod.modq_not_acc0p_depth_period
