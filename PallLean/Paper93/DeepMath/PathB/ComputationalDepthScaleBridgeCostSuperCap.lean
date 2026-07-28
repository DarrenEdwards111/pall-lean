import Mathlib.Tactic

/-!
# Discharging `cost_super` with the scale bridge — the receipt: it is provably capped short

`cost_super` (`SAT ∉ P`) is superpolynomial reach: hardness at *every* exponent `c` (for all `c`,
`SAT ∉ DTS(n^c)`).  The corpus already proves the scale bridge's two facts:

* `ScaleBridge.uniform_hardness_scales_down` — `EXP ≠ NEXP ⟹ P ≠ NP` (proved), but it *consumes*
  `EXP ≠ NEXP`, a separation of the same strength;
* `UniformAxisReach.window_below_two` — the Lipton–Viglas engine's reach is capped at `c < 2` (proved).

This file closes the loop machine-checked: a reach **capped below `c = 2`** is *not* superpolynomial, so
the scale bridge cannot discharge `cost_super`.  Discharging it needs a scale bridge whose reach is
unbounded — which is the P-vs-NP scale barrier itself.

## What is proved

* **`capped_not_superpoly`** — a method whose reach is capped below `t ≥ 1` misses exponent `t`, so it is
  not superpolynomial.
* **`scale_bridge_reach_insufficient`** — instantiated at the engine's cap `t = 2`: a reach capped below
  `c = 2` (which `window_below_two` proves the scale bridge is) is not superpolynomial, hence does not
  discharge `cost_super`.

## Honest scope

This is the *receipt*, not a discharge.  It proves the scale bridge, as it stands, provably falls short
of `cost_super` — the cap `c < 2` is the method's ceiling (best known alternation-trading reaches
`≈ 1.801`, still `< 2`), not a formalization gap.  To discharge `cost_super` you need a scale bridge with
unbounded reach, or `EXP ≠ NEXP` — each the P-vs-NP scale barrier.  Nothing here is `P ≠ NP`; it is the
proof that the scale bridge does not cross it.
-/

namespace PallLean.Paper93.DeepMath.PathB.ScaleBridgeCostSuperCap

-- A method's **reach** is the exponents `c` at which it certifies hardness (`SAT ∉ DTS(n^c)`).

/-- **Superpolynomial reach** — hardness at *every* exponent.  This is `SAT ∉ P`, i.e. `cost_super`. -/
def SuperpolyReach (reaches : ℕ → Prop) : Prop := ∀ c, reaches c

/-- **Capped reach** — the method certifies hardness only at exponents strictly below `t`. -/
def CappedBelow (reaches : ℕ → Prop) (t : ℕ) : Prop := ∀ c, reaches c → c < t

/-- **A capped method is not superpolynomial (proved).**  If a reach is capped below `t ≥ 1`, then
assuming it were superpolynomial gives `reaches t`, hence `t < t` — contradiction.  So a bounded scale
reach never certifies hardness at every exponent. -/
theorem capped_not_superpoly (reaches : ℕ → Prop) (t : ℕ) (ht : 1 ≤ t)
    (hcap : CappedBelow reaches t) : ¬ SuperpolyReach reaches := by
  intro hsuper
  exact absurd (hcap t (hsuper t)) (lt_irrefl t)

/-- **The scale bridge does not discharge `cost_super` (proved).**  The Lipton–Viglas engine is capped
below `c = 2` (`UniformAxisReach.window_below_two`).  A reach capped below `2` is not superpolynomial, so
it cannot certify `SAT ∉ P` — it does not discharge `cost_super`. -/
theorem scale_bridge_reach_insufficient (reaches : ℕ → Prop)
    (hcap : CappedBelow reaches 2) : ¬ SuperpolyReach reaches :=
  capped_not_superpoly reaches 2 (by norm_num) hcap

/-- **The exact missing exponent (proved).**  A scale bridge capped below `2` fails already at `c = 2`
(`SAT ∉ DTS(n²)`) — it never even reaches the quadratic exponent, let alone the unbounded reach
`cost_super` demands. -/
theorem scale_bridge_misses_quadratic (reaches : ℕ → Prop)
    (hcap : CappedBelow reaches 2) : ¬ reaches 2 :=
  fun h => absurd (hcap 2 h) (lt_irrefl 2)

end PallLean.Paper93.DeepMath.PathB.ScaleBridgeCostSuperCap

#print axioms PallLean.Paper93.DeepMath.PathB.ScaleBridgeCostSuperCap.scale_bridge_reach_insufficient
