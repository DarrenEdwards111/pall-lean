import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingTight

/-!
# Route F — trying to prove "the compilation spreads": it is an open space lower bound

This is the honest result of *attempting* the final lemma, "the Cook–Levin compilation spreads (active
width `≥ T/log n`)".  **It cannot be proved, because it is equivalent to a space lower bound for SAT — and
it is *false* for small-space deciders.**

## Why

The standard Cook–Levin tableau has `T` columns, but the head only *visits* `S` of them, where `S` is the
machine's **space**.  Cuts in the unvisited columns are trivial (`0` crossings, no information); the
meaningful cuts lie within the active width `S`.  So:

> "the compilation spreads"  ⟺  active width `S ≥ T/log n`  ⟺  **the SAT-decider uses `≥ T/log n` space.**

* `Spreads S T c n` — the spread condition `T ≤ (c·log₂ n)·S`.
* `not_spreads_of_smallSpace` (proved) — if `S < T/(c·log₂ n)` the machine does **not** spread.
* `shuttle_smallSpace_obstruction` (proved) — the explicit witness: a **width-2** (minimal-space)
  computation running `T > 2·c·log₂ n` steps does **not** spread, yet crosses its single active cut on
  *every* step (`crossings = T`).  So Route F's rank bound `A^{crossings} = A^T` blows up for it.

## The verdict — Route F relocates the difficulty, it does not remove it

Proving the spread claim for the Cook–Levin compilation of an *arbitrary* bounded SAT-decider means proving
that **every** such decider uses `≥ T/log n` space — a **space lower bound for SAT**.  That is itself a
major open problem (in the orbit of `L ≠ NP` / time–space tradeoffs), and is **false** for any small-space
SAT-decider, which — if `P = NP` — could well exist (the shuttle models exactly such a head).

So the whole Route-F line, proved end-to-end, terminates here honestly:

* the *mechanism* is fully proved (counting → product gap → lane fix → crossing-sequence reduction →
  pigeonhole → oblivious-wide ⇒ poly, with tightness shown);
* the *single remaining lemma* — "the compilation spreads" — is **not** a fact about polynomials or
  geometry that one can grind out.  It is an **open space lower bound for SAT**, equivalent in strength to
  the separation it was meant to prove.

This is the genuine frontier: Route F transforms "explicit super-polynomial circuit lower bound" into
"`T/log n` space lower bound for SAT-deciders" — a real, precise, *different* open problem, but an open
problem of the same `P`-vs-`NP` strength.  **Nothing here asserts it**, and the obstruction (small-space
deciders) is now a theorem, not a worry.
-/

namespace PallLean.Paper93.DeepMath.PathB.Crossings

open Finset

/-- **The spread condition.**  A machine using active width (space) `S` over time `T` "spreads" iff
`T ≤ (c·log₂ n)·S`, i.e. `S ≥ T/(c·log₂ n)` — exactly what makes the best active cut have `O(log n)`
crossings. -/
def Spreads (S T c n : ℕ) : Prop := T ≤ c * Nat.log 2 n * S

/-- **Small space ⇒ does not spread.** -/
theorem not_spreads_of_smallSpace {S T c n : ℕ} (h : c * Nat.log 2 n * S < T) :
    ¬ Spreads S T c n := by
  unfold Spreads; omega

/-- **The explicit obstruction.**  A width-`2` (minimal-space) computation running `T = 2·c·log₂ n + 1`
steps does not spread, yet crosses its active cut on every step (`crossings = T`) — so Route F's crossing
bound `A^T` is exponential for it.  Hence the spread claim is *false* for small-space deciders, and proving
it for SAT would be a space lower bound. -/
theorem shuttle_smallSpace_obstruction (c n : ℕ) :
    let T := 2 * (c * Nat.log 2 n) + 1
    ¬ Spreads 2 T c n ∧ crossings (fun t => t % 2) 0 T = T := by
  intro T
  refine ⟨not_spreads_of_smallSpace ?_, shuttle_crosses_every_step T⟩
  show c * Nat.log 2 n * 2 < T
  simp only [T]; omega

end PallLean.Paper93.DeepMath.PathB.Crossings

#print axioms PallLean.Paper93.DeepMath.PathB.Crossings.shuttle_smallSpace_obstruction
