import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCostSuperRobust

/-!
# The tower of restricted lower bounds: the pattern, and what climbing it requires

Darren's meta-observation: the repo proves circuit lower bounds at many **strengths** — depth-2,
depth-3, `AC⁰` (parity ∉ AC⁰), `AC⁰[p]` (MOD_q ∉ AC⁰[p]), `ACC⁰` (NEXP ⊄ ACC⁰), `NC¹` (Andreev
`n^{5/2}`) — a *tower* of rungs.  He asks whether the tower itself has a pattern we can learn from to
*climb* it to the full separation.

There is a pattern, and this file makes it precise.  Each rung is cracked by a method that bounds a
**hub parameter** which that rung's *restriction* makes bounded (bounded depth ⟹ bounded reach; algebraic
gates ⟹ bounded degree; formula ⟹ charged fan-in).  So each rung gives a bound `b d` at level `d`.  And
**climbing the tower is exactly amplification**: if the bounds grow up the tower (`2·b d ≤ b(d+1)`), they
reach the superpolynomial top — via the same `cost_super` engine (`CostSuperRobust.doubling_amplifies`).

## What is proved

* **`tower_climbs`** — if the tower's rung-bounds amplify (`2·b d ≤ b(d+1)`), then `b d ≥ 2^d · b 0`:
  the tower reaches the superpolynomial top.  Climbing = amplifying.
* **`flat_tower_stuck`** — a tower whose bounds don't grow (`b ≡ 1`) never climbs: the rungs stay at the
  base.  So the climb is not automatic — it is the growth condition.

## The pattern, and why the tower doesn't reach on its own

The rungs are real and proved — the base `b 0, b 1, …` exists (the switching lemma, the polynomial
method, Williams, shrinkage).  But the methods are **restriction-tied**: each exploits its rung's
restriction, and removing the restriction (climbing) removes the method's leverage.  In amplification
terms, the open input is the **climb** `2·b d ≤ b(d+1)` — that the lower bound at a *weaker* restriction
is at least a fixed factor larger than at a stronger one.  That per-rung growth is a self-improvement
across restrictions, and it is exactly `cost_super` (`CostSuperRobust`: any fixed ratio `> 1` per level
amplifies to superpolynomial; the growth itself is the wall).

So the pattern Darren senses is real: the tower of restricted lower bounds is the **base of an
amplification tower**, and the step that climbs it is the multiplicative growth of the bounds up the
rungs.  That step is the self-improvement / magnification we have been circling — `cost_super`.  The
tower's rungs are proved; the step that climbs from them to the top is the wall.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RestrictionTowerClimb

open PallLean.Paper93.DeepMath.PathB.CostSuperRobust
open PallLean.Paper93.DeepMath.PathB.DemandGeneration

/-- **Climbing the tower is amplification (proved).**  If the rung-bounds `b d` grow by at least a
factor `2` up the tower (`2·b d ≤ b(d+1)`), then `b d ≥ 2^d · b 0` — the tower reaches the
superpolynomial top.  This is `cost_super`'s doubling engine, read as climbing the restriction tower. -/
theorem tower_climbs (b : TowerDemand) (climb : ∀ d, 2 * b.D d ≤ b.D (d + 1)) (d : ℕ) :
    2 ^ d * b.D 0 ≤ b.D d :=
  doubling_amplifies b climb d

/-- **The climb is the one open input (proved).**  Given the per-rung growth, the whole tower is
scaled — the rungs are proved, and the sole remaining ingredient is the growth `climb`. -/
theorem climb_is_the_step (b : TowerDemand) (climb : ∀ d, 2 * b.D d ≤ b.D (d + 1)) :
    ∀ d, 2 ^ d * b.D 0 ≤ b.D d :=
  tower_climbs b climb

/-- **A flat tower never climbs (proved).**  Bounds that don't grow (`b ≡ 1`) stay at the base — the
rungs alone, without the growth step, do not reach the top. -/
theorem flat_tower_stuck : ∀ d, flatDemand.D d = 1 := flatDemand_eq

/-- **A sub-doubling climb still reaches the top (proved).**  Even a factor `3/2` per rung climbs — the
step need not double, only grow.  So the tower needs any fixed multiplicative growth up the rungs, not a
specific rate.  (Reuses `CostSuperRobust.ratio_three_halves_amplifies`.) -/
theorem sub_doubling_climb (b : TowerDemand) (climb : ∀ d, 3 * b.D d ≤ 2 * b.D (d + 1)) (d : ℕ) :
    3 ^ d * b.D 0 ≤ 2 ^ d * b.D d :=
  ratio_three_halves_amplifies b climb d

end PallLean.Paper93.DeepMath.PathB.RestrictionTowerClimb

#print axioms PallLean.Paper93.DeepMath.PathB.RestrictionTowerClimb.tower_climbs
#print axioms PallLean.Paper93.DeepMath.PathB.RestrictionTowerClimb.flat_tower_stuck
#print axioms PallLean.Paper93.DeepMath.PathB.RestrictionTowerClimb.sub_doubling_climb
