import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DynamicSPDPCalibration

/-!
# ACC⁰ composition — how stacking modular gates drives the statistic count, and the budget blow‑up

The calibration (`…ACC0DynamicSPDPCalibration`) showed a function of `k` weight statistics has `≤ 2^{(d+1)^k}`
realized features: single modulus (`k=1`) is polynomial at the Gödel level, more moduli cost more.  This file
formalizes the **composition** step: an ACC⁰ circuit composing `m` modular gates is a function of the `m`‑tuple of
their statistics, so the statistic count is `k = m` — the number of gates.  Since ACC⁰ circuits have *polynomially
many* gates, `m` grows, and the realized‑feature budget leaves polynomial immediately.

## What is proved (clean axioms, no `sorry`)

* `combinedStat` / `composed_realized_le` — a circuit that is a function `F` of the outputs of `m` modular gates
  (each a function of its own weight statistic) factors through the combined `m`‑tuple statistic, so its realized
  low‑degree features number `≤ 2^{(d+1)^m}`.  The statistic count of a depth‑2 ACC⁰ circuit **is its gate count**.
* `budget_exponent_ge_two_pow` — `2^m ≤ (d+1)^m` (for `d ≥ 1`): the budget *exponent* `(d+1)^m` is itself at least
  exponential in the gate count `m`, so the budget `2^{(d+1)^m}` is at least *doubly* exponential in `m`.
* `composed_budget_ge_sq` — `(d+1)^2 ≤ (d+1)^m` for `m ≥ 2`: two gates already push the budget exponent past the
  single‑gate value.

## Verdict — the method reaches a single gate, composition breaks it

The reach is sharp and matches the AC⁰[p] → ACC⁰ frontier exactly:

* **1 gate** (`m=1`, AC⁰[p]‑style): budget `2^{(d+1)} = 2^{O(log n)}` at the Gödel level — **polynomial**
  (`godel_symmetric_realized_poly`).  The framework explains a single modular gate cleanly.
* **2 gates** (`m=2`, the first mixed‑moduli composition): budget `2^{(log n+1)^2} = 2^{O(log² n)}` —
  **quasi‑polynomial**.
* **`m` gates** (real ACC⁰, `m = poly(n)`): budget `2^{(d+1)^m} ≥ 2^{2^m}` — **doubly exponential in the gate
  count**, hopelessly super‑polynomial.

So the statistic/feature‑counting argument is **vacuous for composed ACC⁰ circuits**: counting works per‑gate but
the count `k = m` grows with composition, and the budget blows past polynomial at the very first mixed‑modulus
stacking.  This is the same lesson as the Gödel feature‑count vacuity, one level up: an A1 bound for the full ACC⁰
class (`ACC0LowRealizedGodelSPDP`) **cannot come from counting statistics** — it must come from the genuine ACC⁰
structure (the Razborov–Smolensky / correlation argument that composed modular circuits *still* approximate
low‑degree), which is exactly the open, `NP ⊄ ACC⁰`‑strength content the framework localizes but does not supply.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0Composition

open PallLean.Paper93.DeepMath.PathB.RankContextualWidth
open PallLean.Paper93.DeepMath.PathB.ProjectedContextualRank
open PallLean.Paper93.DeepMath.PathB.LowDegreeProjection
open PallLean.Paper93.DeepMath.PathB.SPDPFeatureProjection
open PallLean.Paper93.DeepMath.PathB.GodelHierarchySPDPScaling
open PallLean.Paper93.DeepMath.PathB.ACC0DynamicSPDPCalibration

variable {a : ℕ}

/-- The combined statistic of `m` gates: the `m`‑tuple of their individual statistics. -/
def combinedStat {m : ℕ} (stats : Fin m → ((Fin a → Bool) → ℕ)) : (Fin a → Bool) → (Fin m → ℕ) :=
  fun v j => stats j v

/-- **Composition drives the statistic count to the gate count (proved).**  A circuit that is a function `F` of
the outputs of `m` modular gates (each a function of its own weight statistic, each bounded by the input weight)
factors through the combined `m`‑tuple statistic, so it has `≤ 2^{(d+1)^m}` realized low‑degree features.  The
statistic count `k` of a composed ACC⁰ circuit equals its gate count `m`. -/
theorem composed_realized_le {m : ℕ} (stats : Fin m → ((Fin a → Bool) → ℕ)) (d : ℕ)
    (hbound : ∀ v j, hw v ≤ d → stats j v ≤ d) (H : Finset ((Fin m → ℕ) → Bool)) :
    (H.image (fun F => lowDegProj a d (statRow (combinedStat stats) F))).card ≤ 2 ^ ((d + 1) ^ m) := by
  apply kStat_realized_le (combinedStat stats) d _ H
  intro v j hv
  exact hbound v j hv

/-- **The budget exponent is exponential in the gate count (proved): `2^m ≤ (d+1)^m`** for `d ≥ 1`.  Hence the
budget `2^{(d+1)^m}` is at least doubly exponential in `m`. -/
theorem budget_exponent_ge_two_pow {d m : ℕ} (hd : 1 ≤ d) : 2 ^ m ≤ (d + 1) ^ m :=
  Nat.pow_le_pow_left (by omega) m

/-- **Two gates already exceed the single‑gate budget exponent (proved): `(d+1)^2 ≤ (d+1)^m`** for `m ≥ 2`. -/
theorem composed_budget_ge_sq {d m : ℕ} (hm : 2 ≤ m) : (d + 1) ^ 2 ≤ (d + 1) ^ m :=
  Nat.pow_le_pow_right (by omega) hm

/-- **The composed budget dominates a doubly‑exponential in the gate count (proved): `2^{2^m} ≤ 2^{(d+1)^m}`** for
`d ≥ 1`.  For super‑logarithmically many gates this is super‑polynomial — the counting argument is vacuous for
real ACC⁰ circuits. -/
theorem composed_budget_ge_double_exp {d m : ℕ} (hd : 1 ≤ d) : 2 ^ (2 ^ m) ≤ 2 ^ ((d + 1) ^ m) :=
  Nat.pow_le_pow_right (by norm_num) (budget_exponent_ge_two_pow hd)

end PallLean.Paper93.DeepMath.PathB.ACC0Composition

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Composition.composed_realized_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Composition.budget_exponent_ge_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Composition.composed_budget_ge_double_exp
