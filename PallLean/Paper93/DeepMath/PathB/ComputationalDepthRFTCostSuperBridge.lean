import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGodMoveBridgeRFT
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCostSuperRobust

/-!
# Wiring the RFT observer model onto cost_super: the material boundary difference IS multiplicative
# growth

`GodMoveBridgeRFT` proved the two observers are non-equivalent **iff** `SAT ∉ P`
(`nonequiv_iff_separation`), and that the difference which delivers this is a difference in the
*reachable set* — the "material" boundary difference — not the budget.  `CostSuperRobust` proved that
the separating content of `cost_super` is **multiplicative growth** of the tower demand (any fixed
ratio `> 1` per level), not the exact factor 2.

This file wires them: it names the demand-side condition (`MultiplicativeGrowth`) and, through the
one honest bridge `separation_iff_growth` (`SAT ∉ P ⟺ the tower demand grows` — the
`DemandGeneration`/`cost_super` identification), proves that the RFT **material boundary difference is
exactly multiplicative growth**:

  `¬ ObsEquiv P G  ⟺  MultiplicativeGrowth T`  (`observers_differ_iff_growth`).

So the two observers have genuinely different reachable sets on SAT **iff** SAT's tower demand
sustains a ratio `> 1` per level.  The God-observer sees the full multiplicative demand
(`growth_amplifies`: growth is the `(p/q)^d` amplification); the P-observer reaches SAT only in the
COLLAPSE (`flat_no_growth`: the flat demand has no growth — the `P = NP`-like world of
`budget_diff_consistent_with_equiv`, now on the demand side: `flat_world_observers_equiv`).

## Honest scope

The wiring is EXACT: the material boundary difference and multiplicative growth are the same
statement.  But it is a *relocation*, not a closure — the bridge `separation_iff_growth` (that SAT's
tower actually grows, rather than collapsing) is precisely `cost_super`, still open.  What the wiring
buys: the RFT non-equivalence is now expressed in the sharpest known form of the wall (ratio `> 1`,
not doubling), and the observer collapse is identified with the demand collapse (ratio `1`).  Nothing
here proves `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RFTCostSuperBridge

open PallLean.Paper93.DeepMath.PathB.GodMoveBridgeRFT
open PallLean.Paper93.DeepMath.PathB.CostSuperRobust
open PallLean.Paper93.DeepMath.PathB.DemandGeneration

/-- **Multiplicative growth of the tower demand**: the demand sustains some fixed ratio `p/q > 1` per
level.  This is the sharpened `cost_super` condition of `CostSuperRobust` — the separating content,
weaker than the exact doubling. -/
def MultiplicativeGrowth (T : TowerDemand) : Prop :=
  ∃ p q : ℕ, 1 ≤ q ∧ q < p ∧ ∀ d, p * T.D d ≤ q * T.D (d + 1)

/-- **Growth is the `(p/q)^d` amplification (proved).**  When the demand grows, it grows to its power
— the God-observer's full-demand view.  Reuses `CostSuperRobust.demand_amplifies_ratio`. -/
theorem growth_amplifies (T : TowerDemand) (h : MultiplicativeGrowth T) :
    ∃ p q : ℕ, 1 ≤ q ∧ q < p ∧ ∀ d, p ^ d * T.D 0 ≤ q ^ d * T.D d := by
  cases h with
  | intro p hp =>
    cases hp with
    | intro q hq2 =>
      exact ⟨p, q, hq2.1, hq2.2.1, fun d => demand_amplifies_ratio T p q hq2.2.2 d⟩

/-- **The flat demand does not grow (proved) — the collapse.**  `D ≡ 1` cannot sustain any ratio
`> 1` (`p·1 ≤ q·1` forces `p ≤ q`, contradicting `q < p`).  This is the demand-side of the
`P = NP`-like world in `GodMoveBridgeRFT.budget_diff_consistent_with_equiv`: where the demand
collapses, the observers coincide. -/
theorem flat_no_growth : ¬ MultiplicativeGrowth flatDemand := by
  intro h
  cases h with
  | intro p hp =>
    cases hp with
    | intro q hq2 =>
      have hpq : q < p := hq2.2.1
      have hgrow := hq2.2.2 0
      rw [flatDemand_eq, flatDemand_eq, Nat.mul_one, Nat.mul_one] at hgrow
      omega

/-! ### The wiring -/

/-- **The material boundary difference IS multiplicative growth (proved).**  Through the bridge
`separation_iff_growth` (`SAT ∉ P ⟺ the tower demand grows` — the `cost_super` identification), the
RFT non-equivalence of the two observers is exactly multiplicative growth of SAT's tower demand.
The observers have different reachable sets on SAT **iff** the demand sustains a ratio `> 1`. -/
theorem observers_differ_iff_growth {Problem : Type} (P G : Observer Problem) (sat : Problem)
    (T : TowerDemand)
    (hPG : ∀ x, P x → G x) (hGsat : G sat) (complete : P sat → ∀ x, G x → P x)
    (separation_iff_growth : ¬ P sat ↔ MultiplicativeGrowth T) :
    ¬ ObsEquiv P G ↔ MultiplicativeGrowth T :=
  Iff.trans (nonequiv_iff_separation P G sat hPG hGsat complete) separation_iff_growth

/-- **The collapse world: flat demand ⟹ the observers coincide (proved).**  In a world where SAT's
tower demand is flat (no growth), the two observers are equivalent — the RFT `P = NP` collapse,
identified with the demand collapse.  Combines `observers_differ_iff_growth` with `flat_no_growth`. -/
theorem flat_world_observers_equiv {Problem : Type} (P G : Observer Problem) (sat : Problem)
    (hPG : ∀ x, P x → G x) (hGsat : G sat) (complete : P sat → ∀ x, G x → P x)
    (separation_iff_growth : ¬ P sat ↔ MultiplicativeGrowth flatDemand) :
    ObsEquiv P G := by
  have hdiff := observers_differ_iff_growth P G sat flatDemand hPG hGsat complete separation_iff_growth
  exact Classical.not_not.mp (fun hne => flat_no_growth (hdiff.mp hne))

end PallLean.Paper93.DeepMath.PathB.RFTCostSuperBridge

#print axioms PallLean.Paper93.DeepMath.PathB.RFTCostSuperBridge.growth_amplifies
#print axioms PallLean.Paper93.DeepMath.PathB.RFTCostSuperBridge.flat_no_growth
#print axioms PallLean.Paper93.DeepMath.PathB.RFTCostSuperBridge.observers_differ_iff_growth
#print axioms PallLean.Paper93.DeepMath.PathB.RFTCostSuperBridge.flat_world_observers_equiv
