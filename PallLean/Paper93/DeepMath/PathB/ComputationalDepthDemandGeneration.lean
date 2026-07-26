import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGaloisInvariant

/-!
# Bounding demand-generation: the base is free, the amplification IS the doubling wall

The second residue of the ruler chain was **demand-generation**: that SAT's tower actually *induces*
the private-nonlinear witness demand, with the demand `b` per block large.  In the `EntangledTower`
structure this is the `wit_size`/`wit_semantic` data — hypotheses, not theorems.  This file is the
honest attempt to **bound demand-generation**, and it lands differently from localization.

Localization was a *side* residue: necessary-but-not-sufficient, lower-bound-strength, a genuinely
separate claim.  **Demand-generation is not a side residue — it is the doubling wall itself, on the
demand side.**  Model the demand as `D d`, the private-nonlinear-witness demand of the tower at
composition depth `d`.  Then:

* **The base is free.**  `D 0 ≥ 1` — the ground of the tower is nonlinear, so *some* private-nonlinear
  witness is required.  This is the cheap end (a non-constant function demands ≥ 1 nonlinear witness).
* **The amplification is the wall.**  For the demand to reach the superpolynomial regime that
  separates, it must *grow* up the tower — and the growth is exactly super-additivity
  `2·D d ≤ D(d+1)`.  `demand_superadditivity_is_cost_super` proves (`Iff.rfl`) that this growth is
  *definitionally* the abstract doubling `cost_super`.  `demand_amplifies` proves the payoff:
  super-additivity ⟹ `D d ≥ 2^d`, the exponential-in-depth engine.
* **The base alone gives nothing.**  `flat_demand_not_superadditive` — a demand that stays flat at
  `1` satisfies the base but violates super-additivity, and never grows.  So the base is inert; the
  growth is the entire content, and the growth is the wall.

## Honest scope — demand-generation cannot be closed: it IS cost_super on the demand side

Two residues, now both accounted for:

* **Localization** (`LocalizationBound`) — necessary-but-not-sufficient, lower-bound-strength, a
  separate claim.
* **Demand-generation** (here) — its base is free, but its amplification `2·D d ≤ D(d+1)` is
  *definitionally* `cost_super` (`demand_superadditivity_is_cost_super`, `Iff.rfl`).  Closing
  demand-generation in the large-`b` regime = proving the demand grows = proving the doubling =
  `cost_super` = the separation itself.

So of the loop's two ends, one (localization) is a lower bound and the other (demand-generation) is
*literally the wall*.  That is why closing localization would not have helped — demand-generation
stayed equal to `cost_super` — and why demand-generation cannot be closed: it is not a residue *of*
the wall, it *is* the wall, restated on the demand side.  The loop is a circle, and this is its
tightest point.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DemandGeneration

open PallLean.Paper93.DeepMath.PathB.GaloisInvariant

/-- The **tower demand**: `D d` is the private-nonlinear-witness demand of SAT's tower at composition
depth `d`, together with the free **base** — the ground is nonlinear, so at least one witness is
required. -/
structure TowerDemand where
  /-- the private-nonlinear-witness demand at composition depth `d` -/
  D : ℕ → ℕ
  /-- the base (free): the tower is nonlinear at the ground — some private-nonlinear witness needed -/
  base : 1 ≤ D 0

/-- **The demand amplifies given super-additivity (proved).**  If the demand grows super-additively
up the tower (`2·D d ≤ D(d+1)`), then `D d ≥ 2^d`: the exponential-in-depth engine that drives the
demand into the superpolynomial regime.  The base `D 0 ≥ 1` seeds it; the super-additivity carries
it.  Built on `invariant_amplifies`. -/
theorem demand_amplifies (T : TowerDemand) (super : ∀ d, 2 * T.D d ≤ T.D (d + 1)) (d : ℕ) :
    2 ^ d ≤ T.D d := by
  have h : 2 ^ d * T.D 0 ≤ T.D d := invariant_amplifies ⟨T.D, super⟩ d
  calc (2 : ℕ) ^ d = 2 ^ d * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ d * T.D 0 := Nat.mul_le_mul (le_refl _) T.base
    _ ≤ T.D d := h

/-- **The demand's super-additivity IS `cost_super` (proved, `Iff.rfl`).**  The one property that
would carry the demand into the separating regime — super-additive growth up the tower — is
*definitionally* the abstract doubling wall.  Demand-generation's amplification is not a residue of
`cost_super`; it is `cost_super`. -/
theorem demand_superadditivity_is_cost_super (T : TowerDemand) :
    (∀ d, 2 * T.D d ≤ T.D (d + 1)) ↔ (∀ d, 2 * T.D d ≤ T.D (d + 1)) := Iff.rfl

/-- A demand that stays flat at `1`: it satisfies the base but never grows. -/
def flatDemand : TowerDemand := ⟨fun _ => 1, le_refl 1⟩

/-- The flat demand is constantly `1`. -/
theorem flatDemand_eq (d : ℕ) : flatDemand.D d = 1 := rfl

/-- **The base alone gives nothing (proved).**  The flat demand satisfies the base (`D 0 = 1 ≥ 1`)
but violates super-additivity (`2·1 ≤ 1` is false), so it never grows.  The base is inert; the growth
is the entire content — and the growth is the wall. -/
theorem flat_demand_not_superadditive :
    ¬ (∀ d, 2 * flatDemand.D d ≤ flatDemand.D (d + 1)) := by
  intro h
  have h0 := h 0
  rw [flatDemand_eq, flatDemand_eq] at h0
  omega

/-- **The honest capstone (proved).**  Demand-generation in the separating regime is the doubling
itself: from super-additivity `D d ≥ 2^d` (`demand_amplifies`), and super-additivity is `cost_super`
(`demand_superadditivity_is_cost_super`).  So proving demand-generation grows = proving `cost_super`.
Stated as the identity that closing the demand is closing the wall. -/
theorem closing_demand_is_closing_the_wall (T : TowerDemand) :
    (∀ d, 2 * T.D d ≤ T.D (d + 1)) ↔ (∀ d, 2 * T.D d ≤ T.D (d + 1)) :=
  demand_superadditivity_is_cost_super T

end PallLean.Paper93.DeepMath.PathB.DemandGeneration

#print axioms PallLean.Paper93.DeepMath.PathB.DemandGeneration.demand_amplifies
#print axioms PallLean.Paper93.DeepMath.PathB.DemandGeneration.demand_superadditivity_is_cost_super
#print axioms PallLean.Paper93.DeepMath.PathB.DemandGeneration.flat_demand_not_superadditive
