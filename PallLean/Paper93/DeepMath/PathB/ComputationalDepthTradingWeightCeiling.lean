import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTradingOptimality

/-!
# Why depth-dependent LP weights do NOT close this system to `2cos(π/7)` — the `∀ n^0` obstruction

Direct, honest answer to "prove the depth-dependent LP weights close it to `2cos(π/7)`": **they cannot, for the
system formalized here**, and this file proves why.

Two facts, on paper and machine-checked below:

1. **`2cos(π/7)` is not this system's constant.**  The `Step` speedup introduces `(∃ n^x)(∀ n^0)` — a universal
   block of exponent `0`.  With this rule set the one-speedup threshold is `φ` (golden ratio, `c² = 1 + c`,
   `AlternationTrading.speedup_enables_contradiction`) and the two-speedup threshold computes to the same `φ`
   (`c⁴ = 1 + c + c³`, which holds at `c = φ`).  The tight constant `2cos(π/7) ≈ 1.8019` belongs to the
   *space-parameter* trading system (lines `DTISP(n^a, n^b)` with the space exponent tracked), where the `∀`
   block after a speedup carries a *positive* exponent tied to `b`.  That system is a strictly larger
   formalization; it is not the one here.

2. **No depth-dependent linear potential certifies below `2` for this rule set** (`weight_ceiling_two`).  A
   linear potential `Φ_w(L) = base + Σ w(depth_i)·exp_i` that is monotone under every `Step` (the condition for
   it to certify "no contradiction") must, at depth `0`, satisfy *both*
   * `w(0) ≥ 1` — from the speedup `⟨[],1⟩ → ⟨[(∃,1),(∀,0)],0⟩` (the `∀ n^0` contributes `w(1)·0 = 0`, so the
     `∃`'s weight alone must absorb the base drop `x = 1`);
   * `1 + w(0) ≤ c` — from the slowdown `⟨[(∃,1)],1⟩ → ⟨[],c⟩`.

   Hence `c ≥ 1 + w(0) ≥ 2`, for *any* weight function `w`.  The `∀ n^0` block gives the speedup budget nothing,
   so no reweighting — uniform or depth-dependent — breaks the cap `2` of
   `TradingOptimality.trading_optimality_two`.

**Conclusion.**  Closing this system to `φ` needs a non-linear certificate (an LP over proof *shapes*, not a single
potential); closing to `2cos(π/7)` needs a *different, larger* system with the space exponent, whose `∀` block
carries the positive exponent that a linear potential needs — and even there the tight weights are the
Buss–Williams LP/computer-search optimum.  The requested reweighting is provably insufficient here; this is the
honest boundary, with the obstruction machine-checked rather than asserted.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TradingWeightCeiling

open PallLean.Paper93.DeepMath.PathB.AlternationTrading

variable {c : ℚ}

/-- A depth-dependent linear potential: `base + Σ w(depth_i)·exp_i`, `depth` = position in the quantifier list. -/
def PhiW (w : ℕ → ℚ) (L : Line) : ℚ :=
  L.base + (L.quants.zipIdx.map (fun p => w p.2 * p.1.2)).sum

/-- **The `∀ n^0` obstruction.**  Any depth-dependent linear potential that is monotone under every trading
move forces `c ≥ 2`.  So no reweighting (uniform or depth-dependent) certifies below the cap `2` — reaching `φ`
or `2cos(π/7)` is impossible by linear-potential reweighting of this rule set. -/
theorem weight_ceiling_two (w : ℕ → ℚ)
    (hmono : ∀ L L', Step c L L' → PhiW w L ≤ PhiW w L') : 2 ≤ c := by
  -- speedup ⟨[],1⟩ → ⟨[(∃,1),(∀,0)],0⟩ : PhiW 1 ≤ PhiW (w 0)  ⟹  1 ≤ w 0
  have hspeed := hmono _ _ (Step.speedup [] 1 1 (by norm_num) (by norm_num))
  -- slowdown ⟨[(∃,1)],1⟩ → ⟨[], c·max 1 1⟩ : PhiW (1 + w 0) ≤ PhiW c  ⟹  1 + w 0 ≤ c
  have hslow := hmono _ _ (Step.slowdown [] true 1 1 (by norm_num))
  simp only [PhiW, List.nil_append, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil] at hspeed hslow
  norm_num at hspeed hslow
  linarith
end PallLean.Paper93.DeepMath.PathB.TradingWeightCeiling

#print axioms PallLean.Paper93.DeepMath.PathB.TradingWeightCeiling.weight_ceiling_two
