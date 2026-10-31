import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaIndicator

/-!
# The single `MOD_p` gate's exact-mod-`p^{2^k}` integer indicator (PROVED)

The across-depth assembly's first genuine rung: supply the Toda indicator's start polynomial via the
**Fermat lift**, completing the integer-route representation of one `MOD_p` gate.

`ACC0TodaIndicator.todaIterate_indicator` amplifies *any* mod-`p` `{0,1}` start `q` to mod-`p^{2^k}`.
The missing piece was the start `q` for a `MOD_p` gate: its degree-`(p−1)` Fermat indicator
`1 − y^{p−1}` (here over `ℤ`), which by Fermat's little theorem is `≡ [p ∣ y] (mod p)`.

  `fermat_lift` — over `ℤ`: `p ∣ ((1 − y^{p−1}) − [p ∣ y])` (the start congruence; `b = [p ∣ y] ∈ {0,1}`).
  `todaMod_amplifies` — feeding it through `A^{[k]}`: `p^{2^k} ∣ (A^{[k]}(1 − y^{p−1}) − [p ∣ y])`.

So a `MOD_p` gate on an integer count `y` is represented by `A^{[k]}(1 − y^{p−1})`, whose value is
`≡ [p ∣ y] (mod p^{2^k})` — exact once `p^{2^k} ≥ 2`.  As a polynomial in the inputs (`y = ` the count
polynomial of degree `d`), the degree is `(p−1)·d · 3^k` (Fermat `p−1`, then `A^{[k]}` ×`3^k`): polylog
for `k ≈ log log`, **independent of fan-in** — the integer-route exact low-degree `MOD` gate.

## What is proved (clean axioms, no `sorry`)

* `fermat_lift` — the Fermat-little-theorem start congruence over `ℤ`.
* `todaMod_amplifies` — the `MOD_p` gate's value `≡ [p ∣ y] (mod p^{2^k})` via the lifted Toda iterate.

## Honest scope

This is the single `MOD_p` gate, value-level on its integer count `y`.  The remaining wall: build `y` as
the polynomial count of a depth-`d` subcircuit layer, thread the per-gate moduli `p^{2^k}` consistently
across depth, and assemble into one exact quasipoly `SYM∘AND` (with `AND`/`OR` via their own
representation).  That assembly is the Beigel–Tarui integer construction body, not built here.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TodaModGate

open PallLean.Paper93.DeepMath.PathB.ACC0TodaIterate (todaAmpIter todaAmpIter_amplifies)

/-- **The Fermat lift (proved): `p ∣ ((1 − y^{p−1}) − [p ∣ y])` over `ℤ`.**  The degree-`(p−1)` Fermat
indicator `1 − y^{p−1}` represents the `MOD_p` value `[p ∣ y] ∈ {0,1}` modulo `p`. -/
theorem fermat_lift (p : ℕ) [Fact p.Prime] (y : ℤ) :
    (p : ℤ) ∣ ((1 - y ^ (p - 1)) - (if (p : ℤ) ∣ y then 1 else 0)) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  by_cases h : (p : ℤ) ∣ y
  · simp only [if_pos h]
    have hy : (y : ZMod p) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
    rw [hy]
    have hz : (0 : ZMod p) ^ (p - 1) = 0 := by
      rw [zero_pow]; exact Nat.sub_ne_zero_of_lt (Fact.out (p := p.Prime)).one_lt
    rw [hz]; ring
  · simp only [if_neg h]
    have hy : (y : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
    rw [ZMod.pow_card_sub_one_eq_one hy]; ring

/-- **The `MOD_p` gate's Toda indicator (proved).**  For prime `p` and integer count `y`, the value of
`A^{[k]}` applied to the Fermat indicator is `≡ [p ∣ y] (mod p^{2^k})`: an exact `{0,1}` `MOD_p` value
once `p^{2^k} ≥ 2`. -/
theorem todaMod_amplifies (p : ℕ) [Fact p.Prime] (y : ℤ) (k : ℕ) :
    (p : ℤ) ^ (2 ^ k) ∣
      (todaAmpIter k (1 - y ^ (p - 1)) - (if (p : ℤ) ∣ y then 1 else 0)) := by
  refine todaAmpIter_amplifies ?_ (fermat_lift p y) k
  by_cases h : (p : ℤ) ∣ y
  · right; simp [h]
  · left; simp [h]

/-!
**`MOD_p` Toda indicator proved.**  `A^{[k]}(1 − y^{p−1})` represents the `MOD_p` value `[p ∣ y]` mod
`p^{2^k}` — degree `(p−1)·3^k` in the count (independent of fan-in), exact once `p^{2^k} ≥ 2`.  The
across-depth assembly (count-as-polynomial, consistent moduli, full `SYM∘AND`) is the remaining wall.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0TodaModGate

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TodaModGate.todaMod_amplifies
