import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ParityAC0
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModqPeriod

/-!
# Bridge (MOD_q ∉ AC⁰) — the classic `MOD`-counting lower bound in plain `AC⁰` (proved)

The `q > 2` analogue of `PARITY ∉ AC⁰`: the `MOD_q` function is not computable by constant-depth `AC⁰` circuits (the classic
`MOD_m ∉ AC⁰`).  Again via Razborov–Smolensky `AC⁰ ⊆ AC⁰[p]`: a `MOD`-free circuit is `AC⁰[p]` for every `p`
(`modFree_modpOnly`), so the unconditional periodic separation `MOD_q ∉ AC⁰[p]` for `n ≡ 1 mod (p−1)`
(`modq_not_acc0p_depth_period`) gives `MOD_q ∉ AC⁰` on the same arities.

## What is proved (clean axioms, no `sorry`)

* **`modq_not_ac0_period`** (PROVED) — given a prime `p ≠ 2` with a primitive `q`-th root `ζ`, for `n ≡ 1 mod (p−1)` and
  `(p−1)·2^d < n`, no depth-`d` `AC⁰` circuit computes `MOD_q`.
* **`mod3_not_ac0`** (PROVED) — the concrete instance `MOD_3 ∉ AC⁰` for `n ≡ 1 mod 6` (`p = 7`, `ζ = 2`).

## Honest scope

This is `MOD_q ∉ AC⁰` (for the arities `n ≡ 1 mod (p−1)`), via Razborov–Smolensky.  A *fully general* `MOD_q ∉ AC⁰` for every
prime `q` needs a prime `p ≡ 1 mod q` (Dirichlet) to host the `q`-th root — supplied here concretely (`q=3`, `p=7`).  The
**Williams cash-out** (`NEXP ⊄ ACC⁰`) is a different, P≠NP-strength theorem and remains **open** / not faked.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModqAC0

open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit depth)
open PallLean.Paper93.DeepMath.PathB.ACC0ParityAC0 (ModFree modFree_modpOnly)
open PallLean.Paper93.DeepMath.PathB.ACC0ModqWitness (modqFn)
open PallLean.Paper93.DeepMath.PathB.ACC0ModqPeriod (modq_not_acc0p_depth_period)

/-- **`MOD_q ∉ AC⁰` for `n ≡ 1 mod (p−1)` (PROVED).**  Given a primitive `q`-th root `ζ` in `F_p` (`p ≠ 2` prime), no
depth-`d` `MOD`-free (`AC⁰`) circuit computes `MOD_q` once `n ≡ 1 mod (p−1)` and `(p−1)·2^d < n`. -/
theorem modq_not_ac0_period {n p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (q : ℕ) (hq2 : 2 ≤ q)
    (hq : (q : ZMod p) ≠ 0) (ζ : ZMod p) (hord : orderOf ζ = q) (hn1 : 1 ≤ n)
    (hper : (p - 1) ∣ (n - 1)) {d : ℕ} (hd : (p - 1) * 2 ^ d < n) :
    ¬ ∃ C : ACC0Circuit n, ModFree C ∧ depth C ≤ d ∧ ACC0CircuitModel.eval C = modqFn q := by
  rintro ⟨C, hfree, hdep, hev⟩
  exact modq_not_acc0p_depth_period hp2 q hq2 hq ζ hord hn1 hper hd
    ⟨C, modFree_modpOnly p C hfree, hdep, hev⟩

private theorem three_ne_zero_mod7 : ((3 : ℕ) : ZMod 7) ≠ 0 := by decide

private theorem orderOf_two_mod7 : orderOf (2 : ZMod 7) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

/-- **`MOD_3 ∉ AC⁰` for `n ≡ 1 mod 6` (PROVED).**  The concrete `q = 3` instance (`p = 7`, `ζ = 2`, a primitive cube root of
unity mod 7). -/
theorem mod3_not_ac0 {n : ℕ} (hn1 : 1 ≤ n) (hper : 6 ∣ (n - 1)) {d : ℕ} (hd : 6 * 2 ^ d < n) :
    ¬ ∃ C : ACC0Circuit n, ModFree C ∧ depth C ≤ d ∧ ACC0CircuitModel.eval C = modqFn 3 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact modq_not_ac0_period (p := 7) (by norm_num) 3 (by norm_num) three_ne_zero_mod7
    (2 : ZMod 7) orderOf_two_mod7 hn1 (by simpa using hper) (by simpa using hd)

/-!
**`MOD_q ∉ AC⁰`, proved.**  The `MOD`-counting lower bound in plain `AC⁰`, via Razborov–Smolensky — generalising
`PARITY ∉ AC⁰` to `MOD_q`, concretely `MOD_3 ∉ AC⁰`.  Remaining (open, not faked): the Williams cash-out to `NEXP ⊄ ACC⁰`.
Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModqAC0

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModqAC0.mod3_not_ac0
