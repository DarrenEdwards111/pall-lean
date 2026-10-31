import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDemandGrowthSeam

/-!
# The per-rung growth for SAT's tower is the wall — the honest reduction, not a proof

The ask: prove the per-rung growth `2·D d ≤ D(d+1)` for SAT's tower.  That growth **is** `cost_super`
— established at the start of the session (`DemandGeneration.demand_superadditivity_is_cost_super`,
`Iff.rfl`) — so proving it is proving `P ≠ NP`.  It is **not** proved here.  This file does the honest
thing: reduce the per-rung growth to the single seam statement it is equivalent to, machine-check the
reduction, and state plainly that the remaining step is the wall.

## What is proved (the reduction, not the growth)

* **`per_rung_growth_iff_no_collision`** — the per-rung growth for the tower holds **iff** the seam
  never collides (`shared ≡ 0`): via `DemandGrowthSeam.growth_iff_no_collision`.  So "prove the per-rung
  growth for SAT" *is* "prove SAT's composition seam has no mass-production" — the same wall, restated.
* **`collision_breaks_growth`** — a single seam-collision at any rung (`0 < shared d`) breaks the growth
  there: `¬ (2·D d ≤ D(d+1))`.  So the growth needs *zero* collision at *every* rung.

## Honest verdict — I cannot prove it, and I will not fake it

The per-rung growth for SAT's tower is equivalent to `∀ d, shared d = 0` — SAT's seam admits **no
mass production** at any rung.  By the arc just built, that is exactly: no free-reach hub straddles the
seam (`SeamForcesHub`), which the seam does not force (`SeamReachBound`: reach is syntactic, the seam is
semantic), which is `cost_super`.  Proving it is `P ≠ NP`.  I have reduced it as far as it goes — to a
single, machine-checked, seam-local statement — and that statement is the wall.  Every route in this
thread lands here; this is the honest floor, not a crossing.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PerRungGrowthIsWall

open PallLean.Paper93.DeepMath.PathB.DemandGrowthSeam

/-- **The per-rung growth IS no-seam-collision (proved reduction).**  The per-rung growth `2·D d ≤
D(d+1)` for the tower holds iff the composition seam never collides (`shared ≡ 0`).  Proving the growth
for SAT is proving SAT's seam admits no mass production — the same wall, restated seam-locally. -/
theorem per_rung_growth_iff_no_collision (S : SeamDemand) :
    (∀ d, 2 * S.D d ≤ S.D (d + 1)) ↔ (∀ d, S.shared d = 0) :=
  growth_iff_no_collision S

/-- **A single collision breaks the growth (proved).**  If the seam collides at any rung
(`0 < shared d`), the per-rung growth fails there: the composed circuit dips below twice the copy.  So
the growth requires zero collision at every rung. -/
theorem collision_breaks_growth (S : SeamDemand) (d : ℕ) (hc : 0 < S.shared d) :
    ¬ (2 * S.D d ≤ S.D (d + 1)) := by
  intro hg
  have h := S.seam d
  omega

/-- **The growth demands zero collision everywhere (proved).**  The per-rung growth holds only if the
seam-collision vanishes at every rung — the single open statement for SAT, which is `cost_super`. -/
theorem growth_needs_no_collision_anywhere (S : SeamDemand)
    (hgrow : ∀ d, 2 * S.D d ≤ S.D (d + 1)) : ∀ d, S.shared d = 0 :=
  (per_rung_growth_iff_no_collision S).mp hgrow

end PallLean.Paper93.DeepMath.PathB.PerRungGrowthIsWall

#print axioms PallLean.Paper93.DeepMath.PathB.PerRungGrowthIsWall.per_rung_growth_iff_no_collision
#print axioms PallLean.Paper93.DeepMath.PathB.PerRungGrowthIsWall.collision_breaks_growth
#print axioms PallLean.Paper93.DeepMath.PathB.PerRungGrowthIsWall.growth_needs_no_collision_anywhere
