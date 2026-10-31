import Mathlib

/-!
# Interpreter grind, value-bound (assembled): configs are polynomial-size (PROVED)

Assembling the value-bound's three components — fuel `k ≤ s`, code `encode c ≤ E`, input `n ≤ s` — into a
single **polynomial config-size bound**.  A universal interpreter encodes a configuration as
`Nat.pair k (Nat.pair (encode c) n)`; with the component bounds (`evaln_bound` for `k`,`n`;
`encode_le_of_isSubcode` for the code `E`), the encoded config is polynomial in `s` and `E`:

  `pair_le_sq` — `Nat.pair a b ≤ (a + b + 1)^2`.
  `config_encode_le` — `k ≤ s → encode_c ≤ E → n ≤ s → Nat.pair k (Nat.pair encode_c n) ≤
    (s + (E + s + 1)^2 + 1)^2`.

So every configuration a universal interpreter manipulates (when simulating an `s`-fuel computation of a
subcode of `c₀`, with `E = encode c₀`) has size `≤ poly(s, encode c₀)` — the quantitative value-bound the
interpreter needs.  For the diagonal, `s = bound e`, `E = encode (ofNat e) = e`, giving config size
`≤ poly(bound e, e)`.

## What is proved (clean axioms, no `sorry`)

* `pair_le_sq` — quadratic upper bound on `Nat.pair`.
* `config_encode_le` — the polynomial config-size bound assembling the value-bound components.

## Honest scope

The assembled value-bound (configs are poly-size), the quantitative data a universal interpreter consumes.
Building the explicit interpreter that *produces* such configs (and whose fuel the `prec`-solve then bounds
by `D = poly(s, E)`) is the remaining construction.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0EffSimConfigBound

/-- **Quadratic upper bound on `Nat.pair` (proved).** -/
theorem pair_le_sq (a b : ℕ) : Nat.pair a b ≤ (a + b + 1) ^ 2 := by
  rw [Nat.pair]
  split
  · ring_nf; nlinarith [Nat.le_of_lt ‹a < b›]
  · ring_nf; nlinarith [Nat.not_lt.mp ‹¬ a < b›]

/-- **Polynomial config-size bound (proved): configs are `poly(s, E)`.**  Assembles the fuel/input bound
(`k, n ≤ s`) and the code bound (`encode_c ≤ E`) into a single polynomial bound on the encoded config. -/
theorem config_encode_le {k encode_c n s E : ℕ} (hk : k ≤ s) (hc : encode_c ≤ E) (hn : n ≤ s) :
    Nat.pair k (Nat.pair encode_c n) ≤ (s + (E + s + 1) ^ 2 + 1) ^ 2 := by
  have hinner : Nat.pair encode_c n ≤ (E + s + 1) ^ 2 :=
    le_trans (pair_le_sq encode_c n) (by gcongr <;> omega)
  calc Nat.pair k (Nat.pair encode_c n)
      ≤ (k + Nat.pair encode_c n + 1) ^ 2 := pair_le_sq k _
    _ ≤ (s + (E + s + 1) ^ 2 + 1) ^ 2 := by gcongr

/-!
**Value-bound assembled.**  Every interpreter configuration `(k, c, n)` with `k, n ≤ s` and
`encode c ≤ E` encodes to a number `≤ (s + (E+s+1)² + 1)²` — polynomial in `s, E`.  For the diagonal
(`s = bound e`, `E = e`) this is `poly(bound e, e)`.  The explicit interpreter producing these configs (and
the `prec`-solve bounding its fuel by `D = poly(s, E)`) remains the construction.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0EffSimConfigBound

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EffSimConfigBound.config_encode_le
