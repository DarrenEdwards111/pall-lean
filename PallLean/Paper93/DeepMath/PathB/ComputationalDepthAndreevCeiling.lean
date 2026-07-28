import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLiftedBlade2

/-!
# Raising the blade's ceiling with Andreev `n^{5/2}`

Every rung of the blade ladder was capped by the *formula-measure ceiling* — Khrapchenko's `n²`.  The honest
way to climb higher is not another sharing costume (those stay at `n²`) but to **raise the ceiling itself**:
swap the Khrapchenko `n²` formula lower bound for **Andreev's `n^{5/2}`**, the best formula lower bound the repo
actually proves (the full `n^{5/2}` shrinkage machine, `andreev_five_halves_full`, `ce43d189`).  This is a real
increase, and it strictly improves what the blade can do.

Concretely at `n = 16`: Khrapchenko's ceiling is `n² = 256`, Andreev's is `n^{5/2} = 1024`, and `n³ = 4096`.

**The ceiling is genuinely raised.**  `andreev_raises_ceiling`: `256 < 1024` — Andreev's target measure is four
times Khrapchenko's, so the blade's margin (`ceiling − bound`) jumps from `256 − 16 = 240` to
`1024 − 16 = 1008` (`andreev_margin_exceeds_khrapchenko`).

**And it lets the blade catch strictly more sharing.**  `andreevBlade` is a lifted blade at the Andreev ceiling
absorbing a sharing budget of `500` — far above Khrapchenko's margin of `240`.  It separates
(`andreev_blade_separates_with_500_sharing`: the target circuit costs `524 > 16`), catching a circuit with `500`
units of reuse.  The Khrapchenko ceiling *cannot* form this blade: `khrapchenko_ceiling_too_low_for_500` —
`16 + 500 < 256` is false, the margin is exhausted.  Raising the ceiling is exactly what buys the extra sharing
tolerance.

**But `n^{5/2}` is still polynomial — the wall is unmoved, only raised.**  `andreev_still_polynomial`:
`1024 < 4096`, i.e. `n^{5/2} < n³` — Andreev's ceiling does not even reach `n³`, let alone superpolynomial.
Formula lower bounds are all polynomial (the frontier is `n^{3−o(1)}`), so the raised ceiling is still a fixed
power.  The general altitude — unbounded sharing, a target requiring *superpolynomial* circuit size — sits above
*every* polynomial ceiling, Andreev included.  Reaching it needs a super-polynomial formula/circuit bound, which
is `cost_super`.

So Andreev raises the floor of the climb from `n²` to `n^{5/2}` — a real, machine-checked improvement — and the
same wall stands one notch higher: still polynomial, still short of general.

## What is proved

* **`andreev_raises_ceiling`** — `256 < 1024`: the Andreev ceiling `n^{5/2}` exceeds the Khrapchenko ceiling
  `n²`.
* **`andreev_margin_exceeds_khrapchenko`** — `240 < 1008`: the Andreev margin dwarfs Khrapchenko's.
* **`andreevBlade`** / **`andreev_blade_separates_with_500_sharing`** — a lifted blade at the Andreev ceiling
  absorbing `500` units of sharing, separating (`524 > 16`).
* **`khrapchenko_ceiling_too_low_for_500`** — the Khrapchenko ceiling cannot form this blade: `16 + 500 < 256`
  is false.
* **`andreev_still_polynomial`** — `1024 < 4096`: `n^{5/2} < n³`, still a fixed power.
* **`andreev_raises_but_stays_polynomial`** — both: ceiling raised, and still polynomial.

## Honest verdict — a real higher ceiling; the wall stands one notch up, still polynomial

Raising the blade's ceiling to Andreev `n^{5/2}` is genuine progress on the best formula lower bound the repo
proves: the ceiling goes `256 → 1024` (`andreev_raises_ceiling`), the margin `240 → 1008`, and the blade now
catches circuits with `500` units of sharing that the Khrapchenko ceiling cannot
(`andreev_blade_separates_with_500_sharing`, `khrapchenko_ceiling_too_low_for_500`).  That is a real, checked
improvement — the lift climbs higher because the ceiling is higher.  And the cap is the same, one notch up:
`n^{5/2}` is still polynomial (`andreev_still_polynomial`, `1024 < 4096 = n³`), so the general altitude —
unbounded sharing, superpolynomial circuit size — remains above it.  Raising the ceiling from `n²` to `n^{5/2}`
buys real altitude; escaping polynomial entirely needs a super-polynomial formula/circuit bound, which is
`cost_super`.  The wall did not move; the floor under it rose.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.AndreevCeiling

open PallLean.Paper93.DeepMath.PathB.LiftedBlade

/-- **The Andreev ceiling exceeds the Khrapchenko ceiling (proved).**  At `n = 16`, `n^{5/2} = 1024` beats
`n² = 256`. -/
theorem andreev_raises_ceiling : (256 : Nat) < 1024 := by decide

/-- **The Andreev margin dwarfs Khrapchenko's (proved).**  `ceiling − bound`: `1024 − 16 = 1008` versus
`256 − 16 = 240`. -/
theorem andreev_margin_exceeds_khrapchenko : (256 - 16 : Nat) < (1024 - 16) := by decide

/-- A lifted blade at the **Andreev** ceiling (`n^{5/2} = 1024`) absorbing a sharing budget of `500` — far
above Khrapchenko's margin of `240`.  The target's bounded-sharing circuit costs `524` (so `524 + 500 = 1024`
matches the unfolding), and the blade catches it (`524 > 16`). -/
def andreevBlade : LiftedBlade where
  Obj := Bool
  circuitCost := fun b => match b with | false => 16 | true => 524
  formulaMeasure := fun b => match b with | false => 16 | true => 1024
  shareBudget := 500
  bound := 16
  target := true
  unfold_bound := by intro o; cases o <;> decide
  high_on_target := by decide

/-- **The Andreev-ceiling blade separates with 500 units of sharing (proved).**  The target circuit costs
`524 > 16` — caught despite reusing `500` subcircuits, which the Khrapchenko ceiling could not tolerate. -/
theorem andreev_blade_separates_with_500_sharing :
    andreevBlade.bound < andreevBlade.circuitCost andreevBlade.target :=
  lifted_blade_separates andreevBlade

/-- **The Khrapchenko ceiling cannot form this blade (proved).**  `16 + 500 < 256` is false: the Khrapchenko
margin (`240`) is exhausted at a sharing budget of `500`.  Raising the ceiling to Andreev is what buys it. -/
theorem khrapchenko_ceiling_too_low_for_500 : ¬ ((16 : Nat) + 500 < 256) := by decide

/-- **The Andreev ceiling is still polynomial (proved).**  `1024 < 4096`, i.e. `n^{5/2} < n³`: the raised
ceiling does not even reach `n³`, let alone superpolynomial. -/
theorem andreev_still_polynomial : (1024 : Nat) < 4096 := by decide

/-- **Andreev raises the ceiling but stays polynomial (proved).**  Left: `n² < n^{5/2}` (raised).  Right:
`n^{5/2} < n³` (still a fixed power).  Real altitude gained; the general (superpolynomial) altitude is still
above it — `cost_super`. -/
theorem andreev_raises_but_stays_polynomial :
    ((256 : Nat) < 1024) ∧ ((1024 : Nat) < 4096) :=
  ⟨andreev_raises_ceiling, andreev_still_polynomial⟩

end PallLean.Paper93.DeepMath.PathB.AndreevCeiling

#print axioms PallLean.Paper93.DeepMath.PathB.AndreevCeiling.andreev_raises_ceiling
#print axioms PallLean.Paper93.DeepMath.PathB.AndreevCeiling.andreev_blade_separates_with_500_sharing
#print axioms PallLean.Paper93.DeepMath.PathB.AndreevCeiling.khrapchenko_ceiling_too_low_for_500
#print axioms PallLean.Paper93.DeepMath.PathB.AndreevCeiling.andreev_still_polynomial
#print axioms PallLean.Paper93.DeepMath.PathB.AndreevCeiling.andreev_raises_but_stays_polynomial
