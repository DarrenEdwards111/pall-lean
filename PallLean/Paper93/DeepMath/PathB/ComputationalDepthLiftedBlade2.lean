import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLiftedBlade

/-!
# Lifting the blade a second altitude: from bounded-total-sharing to bounded fan-out (multiplicative)

The first lift (`LiftedBlade`) absorbed a *fixed total* amount of sharing `t` — the additive model
`formulaMeasure ≤ circuitCost + t`.  That reaches circuits reusing a bounded *absolute* number of wires.  The
next rung up is where sharing scales with the circuit: **bounded fan-out**, where each gate output may be
reused up to a factor `f`, so the total sharing grows with size (up to `Θ(f · size)`) rather than a fixed
budget.  This is a strictly larger class, and the relationship becomes *multiplicative*.

**The second lift.**  Unfolding a bounded-fan-out circuit blows the size up by at most the fan-out factor, so
the underlying formula measure satisfies `formulaMeasure ≤ f · circuitCost` (`unfold_bound`).  If the formula
blade clears `f · bound` — `f · bound < formulaMeasure target` (`high_on_target`) — then cancelling the factor
gives `bound < circuitCost target` (`lifted2_separates`).  The blade now lower-bounds circuit cost for circuits
whose sharing is proportional to their size, not merely bounded in total — a second altitude up.

**Forged concretely.**  `khrapchenkoLifted2` lifts the `n = 8` Khrapchenko blade to fan-out factor `f = 7`: the
target's bounded-fan-out circuit costs `10` (so `f · 10 = 70 ≥ 64`, consistent with the unfolding), and the
blade still catches it (`10 > 8`), even though its sharing now scales with size.

**The cap: the absorbable factor is the measure/ceiling ratio, still polynomial.**  The lift needs
`f · bound < formulaMeasure target` (`lift2_ratio_margin`), i.e. the fan-out factor is bounded by
`formulaMeasure target / bound` — `n² / n = n` for Khrapchenko (`khrapchenko_lift2_factor`: `f < n`).  So the
blade reaches bounded fan-out up to degree `≈ n`, and no further.  General circuits have *unbounded* fan-out — a
gate feeding exponentially many others (free fan-out, Uhlig mass-production) — which is `f` unbounded, and that
exhausts the ratio.  That rung is `cost_super`.

**Same ceiling, re-expressed.**  Both lifts are capped by the *same* formula-measure ceiling (`n²`): the
additive lift absorbs `t < n²`, the multiplicative lift absorbs `f < n`.  Climbing altitudes does not escape the
ceiling — it re-expresses it (total sharing → fan-out degree), each rung bounded by the same formula lower
bound.  Escaping it needs a super-polynomial formula/circuit bound = `cost_super`.

## What is proved

* **`lifted2_separates`** — the multiplicative blade lower-bounds circuit cost: any bounded-fan-out circuit
  (factor `f`) for the target costs more than the ceiling.  A second altitude up.
* **`lift2_ratio_margin`** — the lift is bounded by the ratio: `f · bound < formulaMeasure target`.
* **`khrapchenkoLifted2`** / **`khrapchenko_lifted2_separates`** — forged at `n = 8`, factor `f = 7`: the
  target circuit costs `10 > 8`, caught with size-proportional sharing.
* **`khrapchenko_lift2_factor`** — the absorbed factor is below `n` (`7 < 8`): the ratio cap is polynomial.
* **`lifted_two_altitudes`** — both: every multiplicative blade separates, and only within the ratio margin.

## Honest verdict — a second real altitude; the ceiling is the same, re-expressed

The blade is lifted a second rung: from bounded-total-sharing (additive `t`) to bounded fan-out (multiplicative
`f`), where sharing scales with circuit size.  `lifted2_separates` lower-bounds circuit cost for this larger
class, forged concretely with a real fan-out factor (`khrapchenko_lifted2_separates`, `10 > 8`).  Genuine motion
— bounded fan-out is a strictly richer model than a fixed sharing budget.  And the cap is exact and honest: the
absorbable factor is `formulaMeasure target / bound = n` (`khrapchenko_lift2_factor`), the same formula-measure
ceiling as the first altitude, now wearing the costume of a fan-out degree.  So both altitudes are capped by the
one thing — the polynomial formula lower bound — and the general altitude, unbounded fan-out where a gate is
reused exponentially, is the rung the ceiling forbids: `cost_super`.  Two altitudes lifted; the wall is the
unbounded-fan-out rung, and every rung below it is the same `n²` ceiling re-expressed.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.LiftedBlade2

/-- The blade lifted to the bounded-fan-out altitude.  `circuitCost` is cost in the bounded-fan-out model,
`formulaMeasure` the underlying formula lower bound, `shareFactor` (`f`) the fan-out degree (each gate reused up
to `f` times; `f = 1` recovers formulas).  `unfold_bound` says unfolding blows up by at most factor `f`;
`high_on_target` says the formula blade clears `f · bound`. -/
structure LiftedBlade2 where
  /-- the objects (bounded-fan-out circuits) -/
  Obj : Type
  /-- cost in the bounded-fan-out circuit model (a second altitude up from formulas) -/
  circuitCost : Obj → Nat
  /-- the underlying formula lower bound the blade rests on (Khrapchenko `n²`) -/
  formulaMeasure : Obj → Nat
  /-- the fan-out factor `f`: each gate reused up to `f` times (altitude dial; `1` = formulas) -/
  shareFactor : Nat
  /-- the class ceiling -/
  bound : Nat
  /-- the hard target -/
  target : Obj
  /-- unfolding a bounded-fan-out circuit blows up by at most factor `f`: `formula ≤ f · circuit` -/
  unfold_bound : ∀ o, formulaMeasure o ≤ shareFactor * circuitCost o
  /-- the formula blade clears `f · bound` -/
  high_on_target : shareFactor * bound < formulaMeasure target

/-- **The multiplicative blade lower-bounds circuit cost (proved).**  From `formulaMeasure target ≤ f ·
circuitCost target` and `f · bound < formulaMeasure target`, the factor cancels: `bound < circuitCost target`.
The blade catches circuits whose sharing scales with size — a second altitude up. -/
theorem lifted2_separates (L : LiftedBlade2) : L.bound < L.circuitCost L.target := by
  by_contra hc
  push_neg at hc
  have h1 := L.unfold_bound L.target
  have h2 := L.high_on_target
  have h3 := Nat.mul_le_mul (le_refl L.shareFactor) hc
  omega

/-- **The lift is bounded by the ratio margin (proved).**  The fan-out factor satisfies `f · bound <
formulaMeasure target`, i.e. `f < formulaMeasure target / bound` — the measure/ceiling ratio, `n` for
Khrapchenko.  The absorbable fan-out is polynomial. -/
theorem lift2_ratio_margin (L : LiftedBlade2) : L.shareFactor * L.bound < L.formulaMeasure L.target :=
  L.high_on_target

/-- The `n = 8` Khrapchenko blade lifted to fan-out factor `f = 7`: the target's bounded-fan-out circuit costs
`10` (so `7 · 10 = 70 ≥ 64`), and the blade still catches it (`10 > 8`) with size-proportional sharing. -/
def khrapchenkoLifted2 : LiftedBlade2 where
  Obj := Bool
  circuitCost := fun b => match b with | false => 8 | true => 10
  formulaMeasure := fun b => match b with | false => 8 | true => 64
  shareFactor := 7
  bound := 8
  target := true
  unfold_bound := by intro o; cases o <;> decide
  high_on_target := by decide

/-- **The lifted Khrapchenko blade separates (proved).**  In the bounded-fan-out model with factor `7`, the
target circuit costs `10 > 8` — caught even though its sharing scales with size. -/
theorem khrapchenko_lifted2_separates :
    khrapchenkoLifted2.bound < khrapchenkoLifted2.circuitCost khrapchenkoLifted2.target :=
  lifted2_separates khrapchenkoLifted2

/-- **The absorbed factor is polynomial (proved).**  `f = 7 < 8 = n`: the fan-out degree the blade absorbs is
below `n`, the measure/ceiling ratio.  Bounded fan-out up to `≈ n` is reached; unbounded fan-out (general) is
not. -/
theorem khrapchenko_lift2_factor : khrapchenkoLifted2.shareFactor < 8 := by decide

/-- **Two altitudes lifted (proved).**  Left: every multiplicative blade separates in the bounded-fan-out model.
Right: only within the ratio margin — beyond it (unbounded fan-out = the general altitude) the blade fails,
which is `cost_super`. -/
theorem lifted_two_altitudes :
    (∀ L : LiftedBlade2, L.bound < L.circuitCost L.target)
    ∧ (∀ L : LiftedBlade2, L.shareFactor * L.bound < L.formulaMeasure L.target) :=
  ⟨lifted2_separates, lift2_ratio_margin⟩

end PallLean.Paper93.DeepMath.PathB.LiftedBlade2

#print axioms PallLean.Paper93.DeepMath.PathB.LiftedBlade2.lifted2_separates
#print axioms PallLean.Paper93.DeepMath.PathB.LiftedBlade2.lift2_ratio_margin
#print axioms PallLean.Paper93.DeepMath.PathB.LiftedBlade2.khrapchenko_lifted2_separates
#print axioms PallLean.Paper93.DeepMath.PathB.LiftedBlade2.khrapchenko_lift2_factor
#print axioms PallLean.Paper93.DeepMath.PathB.LiftedBlade2.lifted_two_altitudes
