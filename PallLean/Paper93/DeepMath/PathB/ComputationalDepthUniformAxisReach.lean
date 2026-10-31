import PallLean.Paper93.DeepMath.PathB.ComputationalDepthIndirectDiagonalization

/-!
# The uniform axis: the alternation-trading engine's unconditional reach, and its ceiling

Switching routes to the uniform axis — the one place with **unconditional, non-circular** SAT-specific
lower bounds.  The Lipton–Viglas engine (`IndirectDiagonalization.lipton_viglas_engine`, proved) refutes
`NTIME(n^q) ⊆ DTS(n^p)` for every `p² < 2q²` — i.e. `SAT ∉ DTS(n^c)` for `c = p/q < √2`, from the four
standard trading ingredients and the nondeterministic time hierarchy.  Nothing here assumes SAT is
hard; the bound comes from diagonalization, so it is **not circular**.

This file states the engine's reach on the uniform axis and pins its **ceiling** honestly.

## What is proved

* **`uniform_refutes`** — the engine's reach: for every window point `p² < 2q²`, the simulation
  `NTIME(q) ⊆ DTS(p)` is refuted (re-exposing `lipton_viglas_engine`).  Unconditional.
* **`window_seven_fifths`** — a concrete window point `p/q = 7/5 = 1.4 < √2` (`49 < 50`): the reach is
  non-vacuous.
* **`window_below_two`** — the CEILING, formalized: every window point has `p < 2q`.  So the engine's
  reach is strictly below `c = 2` — it can never prove `SAT ∉ DTS(n²)`, let alone superpolynomial.

## Honest scope — the ceiling is the point

The single-round trade caps at `√2 ≈ 1.414`.  The best known alternation-trading (Fortnow–Van
Melkebeek, Williams) reaches `c = 2·cos(π/7) ≈ 1.801` — still `< 2`, still polynomial, and
`window_below_two` shows *any* bound from this window shape is `< 2`.  So the uniform axis gives a
**real, unconditional, non-circular** SAT lower bound, but capped far below the separation: the gap
from `~n^{1.8}` to superpolynomial is the method's ceiling, not a formalization gap.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniformAxisReach

open PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization

/-- **The engine's unconditional reach (proved).**  For every window point `p² < 2q²`, the simulation
`NTIME(n^q) ⊆ DTS(n^p)` is refuted — the Lipton–Viglas time-space tradeoff, non-circular. -/
theorem uniform_refutes (W : TradingWorld) (p q : ℕ) (hq : 1 ≤ q) (hqp : q ≤ p)
    (hlt : p * p < 2 * (q * q)) : ¬ (∀ L, W.NTIME q L → W.DTS p L) :=
  lipton_viglas_engine W p q hq hqp hlt

/-- **A concrete window point (proved).**  `p/q = 7/5 = 1.4 < √2`: `49 < 50`.  The reach is
non-vacuous. -/
theorem window_seven_fifths : (7 : ℕ) * 7 < 2 * (5 * 5) := by omega

/-- **The ceiling, formalized (proved).**  Every window point satisfies `p < 2q`.  So the engine's
reach is strictly below `c = 2`: it can never reach `SAT ∉ DTS(n²)`, let alone superpolynomial.  The
uniform axis is capped far below the separation. -/
theorem window_below_two (p q : ℕ) (hq : 1 ≤ q) (hlt : p * p < 2 * (q * q)) : p < 2 * q := by
  cases Nat.lt_or_ge p (2 * q) with
  | inl h => exact h
  | inr h =>
    exfalso
    have e : (2 * q) * q = 2 * (q * q) := Nat.mul_assoc 2 q q
    have h1 : (2 * q) * q ≤ (2 * q) * (2 * q) := Nat.mul_le_mul (le_refl (2 * q)) (by omega)
    have h2 : (2 * q) * (2 * q) ≤ p * p := Nat.mul_le_mul h h
    omega

end PallLean.Paper93.DeepMath.PathB.UniformAxisReach

#print axioms PallLean.Paper93.DeepMath.PathB.UniformAxisReach.uniform_refutes
#print axioms PallLean.Paper93.DeepMath.PathB.UniformAxisReach.window_seven_fifths
#print axioms PallLean.Paper93.DeepMath.PathB.UniformAxisReach.window_below_two
