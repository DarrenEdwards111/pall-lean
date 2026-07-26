import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDynamicRestriction

/-!
# The directed dynamic rank: boundary shape, thermodynamic cost, Lagrangian direction

Darren's dynamic rank: it evolves with the **boundary shape** of the observer, its **thermodynamic
cost**, and is **directed by the N-Frame Lagrangian**.  The `dynamic_bound` engine is already proved; this
is about *how the restriction sequence is chosen*.  The three ingredients each attach to the engine — and
each lands on a wall we've already met.

* **boundary shape** = the rank measure `crank` itself (the observer's cut / cbudget).
* **thermodynamic cost** = a Landauer/Bekenstein budget: each restriction erases variables at a cost, so
  the number of restrictions `k` is bounded by the observer's budget.
* **Lagrangian direction** = the action that *chooses* the restriction sequence to extremize the
  shrinkage — the adaptive, non-random restrictions.

## What is proved

* **`directed_bound` (proved)** — the engine cashes out the directed sequence: whatever shrinkage rate `s`
  the Lagrangian-directed restrictions achieve, `s^k · H ≤ crank 0`.  Direction chooses `s`; the engine
  converts it.
* **`thermodynamic_caps_reach` (proved)** — the thermodynamic budget bounds the reach: if `k ≤ B` (the
  observer can afford at most `B` restrictions, Landauer), then `s^k · H ≤ s^B · H`.  The observer's
  thermodynamic cost caps the sequence length.

## Where the three ingredients land

The directed engine works **iff** `s^k` is superpolynomial — and each ingredient hits a known wall:

1. **shrinkage rate `s`** (what direction can achieve): capped for formulas (`Γ ≤ 2 → n³`); whether SPDP's
   rate breaks the depth chasm is `cost_super` (`DynamicRestriction`).
2. **thermodynamic budget** on `k` (`thermodynamic_caps_reach`): the Bekenstein/Landauer cost is a
   **counting** bound — an efficient thermodynamic detector is a natural property, barriered
   (`HolographicIncompressibility`).
3. **Lagrangian direction** (choosing the extremal restrictions): computing it efficiently is `L_eff`,
   barriered (natural proofs); via `L_H` it is hypercomputational, outside the model
   (`LagrangianDilemma`, `NFrameChargeNoether`).

So the directed dynamic rank is the *right architecture* — the engine is built, and the direction is
exactly what would aim it — but its three drivers (shrinkage rate, thermodynamic budget, Lagrangian
direction) are the three walls already on the map: `cost_super`, the counting/incompressibility barrier,
and the `L_eff`/`L_H` dilemma.

**Honest scope.**  Proved: the engine cashes out any directed rate, and the thermodynamic budget caps the
reach.  The rate that would make it superpoly, the counting budget, and the direction are each a known
wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DirectedShrinkage

open PallLean.Paper93.DeepMath.PathB.DynamicRestriction

/-- **The engine cashes out the directed rate (proved).**  Whatever shrinkage rate `s` the
Lagrangian-directed restriction sequence achieves, the bound follows: `s^k · H ≤ crank 0`.  Direction
picks `s`; the engine (`dynamic_bound`) converts it to a circuit lower bound. -/
theorem directed_bound (crank : ℕ → ℕ) (s : ℕ)
    (shrink : ∀ d, s * crank (d + 1) ≤ crank d) (k H : ℕ) (hHard : H ≤ crank k) :
    s ^ k * H ≤ crank 0 :=
  dynamic_bound crank s shrink k H hHard

/-- **The thermodynamic budget caps the reach (proved).**  If the observer can afford at most `B`
restrictions (`k ≤ B`, a Landauer/Bekenstein budget), the reach is capped: `s^k · H ≤ s^B · H`.  The
observer's thermodynamic cost limits the restriction sequence — and that budget is a counting bound. -/
theorem thermodynamic_caps_reach (s H k B : ℕ) (hs : 1 ≤ s) (hk : k ≤ B) :
    s ^ k * H ≤ s ^ B * H :=
  Nat.mul_le_mul (Nat.pow_le_pow_right hs hk) (Nat.le_refl H)

end PallLean.Paper93.DeepMath.PathB.DirectedShrinkage

#print axioms PallLean.Paper93.DeepMath.PathB.DirectedShrinkage.directed_bound
#print axioms PallLean.Paper93.DeepMath.PathB.DirectedShrinkage.thermodynamic_caps_reach
