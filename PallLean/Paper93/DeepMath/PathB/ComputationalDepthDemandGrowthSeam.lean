import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRFTCostSuperBridge

/-!
# Attacking `separation_iff_growth`: what forces SAT's demand to grow lives at the composition seam

The one open hinge everything now hangs on is `separation_iff_growth` — that SAT's tower demand
*grows* (ratio `> 1`) rather than *collapses* (flat).  This file attacks it directly, and localizes
the decision to the **composition seam**: the depth-`d+1` tower is two copies of the depth-`d` tower,
so the demand obeys an inclusion–exclusion law

  `D(d+1) + shared d = 2·D d`   (`SeamDemand.seam`),

where `shared d` is the **seam-collision**: the demand served by gates straddling *both* copies (a
global straddler — the Uhlig mass-production object of `AttackNoSharing`).  The `2·D d` is the two
independent copies; the combining gate is `O(1)` and idealized away.

## What is proved — the mechanism, and a quantitative bar

* **`growth_iff_no_collision`** — full (ratio-2) growth holds **iff** the seam never collides
  (`shared ≡ 0`).  Exact doubling ⟺ no cross-copy sharing.
* **`collapse_iff_collision`** — the demand collapses at some level **iff** a seam-collision exists
  there.  Collapse *requires* a straddler.
* **`bounded_collision_ratio_three_halves`** — THE quantitative bar: if each seam-collision serves at
  most **half a copy** (`2·shared d ≤ D d`), the demand STILL grows at ratio `3/2` — superpolynomial
  (via `CostSuperRobust`).  So SAT need not resist *all* sharing, only *near-total* mass-production.
* **`collapse_needs_large_collision`** — contrapositive: to drop even below ratio `3/2` at a level,
  the collision must exceed half that copy (`D d < 2·shared d`).  Killing growth requires the
  straddler to serve *most* of both copies at once.
* **`seam_multiplicative_growth`** / **`seam_forces_observer_difference`** — the wiring: bounded
  seam-collision ⟹ `MultiplicativeGrowth` ⟹ (through `RFTCostSuperBridge`) the two observers are
  non-equivalent, i.e. `SAT ∉ P`.

## Honest scope — the bar is sharpened, the wall is not crossed

The mechanism is fully proved: growth is forced unless a gate serves *more than half of both copies at
once* at the seam.  What remains open is exactly whether SAT's composition seam admits such a
near-total straddler — that is `cost_super` / Uhlig mass-production, now **localized to the seam and
quantified** (near-total, not any sharing).  Proving SAT's seam-collision stays below half a copy is
`cost_super`; nothing here does that, and nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DemandGrowthSeam

open PallLean.Paper93.DeepMath.PathB.GodMoveBridgeRFT
open PallLean.Paper93.DeepMath.PathB.RFTCostSuperBridge
open PallLean.Paper93.DeepMath.PathB.DemandGeneration

/-- **The composition seam.**  `D d` is the tower demand at depth `d`; `shared d` is the seam-collision
(demand served by gates straddling both copies of the depth-`d` tower inside depth-`d+1`); the seam law
`D(d+1) + shared d = 2·D d` is inclusion–exclusion (two independent copies minus the overlap; the
`O(1)` combiner idealized away). -/
structure SeamDemand where
  D : ℕ → ℕ
  shared : ℕ → ℕ
  base : 1 ≤ D 0
  seam : ∀ d, D (d + 1) + shared d = 2 * D d

/-- The seam's underlying tower demand. -/
def SeamDemand.toTower (S : SeamDemand) : TowerDemand := ⟨S.D, S.base⟩

/-! ### The mechanism -/

/-- **Full growth ⟺ no seam-collision (proved).**  The demand doubles at every level exactly when the
two copies never share (`shared ≡ 0`). -/
theorem growth_iff_no_collision (S : SeamDemand) :
    (∀ d, 2 * S.D d ≤ S.D (d + 1)) ↔ (∀ d, S.shared d = 0) := by
  constructor
  · intro h d; have hs := S.seam d; have hh := h d; omega
  · intro h d; have hs := S.seam d; have hh := h d; omega

/-- **Collapse ⟺ a seam-collision (proved).**  The demand falls short of doubling at some level
exactly when a straddler serves both copies there. -/
theorem collapse_iff_collision (S : SeamDemand) :
    (∃ d, S.D (d + 1) < 2 * S.D d) ↔ (∃ d, 0 < S.shared d) := by
  constructor
  · intro h
    cases h with
    | intro d hd => exact ⟨d, by have hs := S.seam d; omega⟩
  · intro h
    cases h with
    | intro d hd => exact ⟨d, by have hs := S.seam d; omega⟩

/-! ### The quantitative bar -/

/-- **Bounded collision still grows at ratio 3/2 (proved) — the sharpening.**  If each seam-collision
serves at most half a copy (`2·shared d ≤ D d`), the demand still satisfies the ratio-`3/2` premise,
hence (via `CostSuperRobust`) grows superpolynomially.  SAT need only resist *near-total*
mass-production, not all sharing. -/
theorem bounded_collision_ratio_three_halves (S : SeamDemand)
    (h : ∀ d, 2 * S.shared d ≤ S.D d) :
    ∀ d, 3 * S.D d ≤ 2 * S.D (d + 1) := by
  intro d
  have hs := S.seam d
  have hh := h d
  omega

/-- **Collapse requires a large collision (proved).**  To drop below ratio `3/2` at a level, the
seam-collision must serve more than half that copy — a near-total straddler.  Killing growth demands
almost complete mass-production of both copies. -/
theorem collapse_needs_large_collision (S : SeamDemand) (d : ℕ)
    (hcollapse : 2 * S.D (d + 1) < 3 * S.D d) :
    S.D d < 2 * S.shared d := by
  have hs := S.seam d
  omega

/-! ### The wiring to observers -/

/-- **Bounded seam-collision ⟹ multiplicative growth (proved).**  Instantiates the ratio at `3/2`. -/
theorem seam_multiplicative_growth (S : SeamDemand) (h : ∀ d, 2 * S.shared d ≤ S.D d) :
    MultiplicativeGrowth S.toTower := by
  refine ⟨3, 2, by omega, by omega, ?_⟩
  intro d
  show 3 * S.D d ≤ 2 * S.D (d + 1)
  exact bounded_collision_ratio_three_halves S h d

/-- **Bounded seam-collision ⟹ the observers are non-equivalent (proved).**  Through
`RFTCostSuperBridge.observers_differ_iff_growth`: if SAT's composition seam never mass-produces more
than half a copy, the P-observer and God-observer have different reachable sets — `SAT ∉ P`.  The two
open inputs are exactly `cost_super`: the bridge `separation_iff_growth`, and the semantic bound `h`
(SAT's seam stays below half a copy). -/
theorem seam_forces_observer_difference {Problem : Type} (P G : Observer Problem) (sat : Problem)
    (S : SeamDemand)
    (hPG : ∀ x, P x → G x) (hGsat : G sat) (complete : P sat → ∀ x, G x → P x)
    (separation_iff_growth : ¬ P sat ↔ MultiplicativeGrowth S.toTower)
    (h : ∀ d, 2 * S.shared d ≤ S.D d) :
    ¬ ObsEquiv P G :=
  (observers_differ_iff_growth P G sat S.toTower hPG hGsat complete separation_iff_growth).mpr
    (seam_multiplicative_growth S h)

end PallLean.Paper93.DeepMath.PathB.DemandGrowthSeam

#print axioms PallLean.Paper93.DeepMath.PathB.DemandGrowthSeam.growth_iff_no_collision
#print axioms PallLean.Paper93.DeepMath.PathB.DemandGrowthSeam.collapse_iff_collision
#print axioms PallLean.Paper93.DeepMath.PathB.DemandGrowthSeam.bounded_collision_ratio_three_halves
#print axioms PallLean.Paper93.DeepMath.PathB.DemandGrowthSeam.collapse_needs_large_collision
#print axioms PallLean.Paper93.DeepMath.PathB.DemandGrowthSeam.seam_multiplicative_growth
#print axioms PallLean.Paper93.DeepMath.PathB.DemandGrowthSeam.seam_forces_observer_difference
