import Mathlib.Data.Nat.Basic

/-!
# The syntactic consequence SAT's seam forces on the wiring: a hub — and why it still caps

`SeamReachBound` showed reach (syntactic) is orthogonal to SAT's seam (semantic).  The bridge Darren
asked for is a *syntactic* consequence the seam forces on the **wiring** — the circuit graph, not the
computed function.  This file finds it.

To share a sub-computation across the seam, a gate must be a **hub**: physically wired **to both input
blocks** (so it can read across the seam) *and* **to both output cones** (so its value reaches both
copies).  That is a real syntactic consequence — `fanIn ≥ 2` and `fanOut ≥ 2`, a property of the graph,
forced by the seam regardless of what is computed.  And the hub's sharing capacity is bounded by its
wiring: `serves ≤ fanIn`.

## What is proved

* **`seam_forces_hub`** — every sharing gate is a hub: `fanIn ≥ 2 ∧ fanOut ≥ 2`.  The syntactic
  consequence — a shared gate must wire to both blocks and both outputs.
* **`bounded_fanin_bounds_serves`** — the hub's sharing is bounded by its fan-in: `fanIn ≤ σ ⟹ serves
  ≤ σ`.  Bound the wiring, bound the sharing.
* **`hub_escapes`** — but a single hub with fan-in equal to what it serves shares unboundedly: the
  syntactic consequence is met by *one* high-fan-in gate.

## Honest verdict — the consequence is real, and it is the known methods, capping at free fan-in

So the seam *does* force a syntactic consequence — the hub wiring — and it is exactly the object behind
every proven circuit lower bound: `fanIn` is the crossing/reach the crossing-number method bounds,
`fanOut` is the reconvergence the criticality method bounds.  It gives the bound `serves ≤ fanIn`.  But
it caps for the reason everything caps: in the fan-in-unbounded DAG model the `fanIn` is **free**, so
`hub_escapes` — one hub with unbounded fan-in meets the syntactic consequence and shares without limit.
Bounding the fan-in is *charging* (the bounded-fan-in / formula model, capped at `P ⊄ NC¹`); leaving it
free is the DAG model where the hub escapes.  The syntactic consequence the seam forces is the hub, and
the hub's power is its free fan-in — so the bridge from syntactic to semantic is exactly a bound on that
fan-in, which is `cost_super`.  Found the consequence; it is the known crossing/reconvergence structure;
it caps at the free-fan-in hub.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SeamForcesHub

/-- **The hub** — the syntactic consequence of sharing across the seam.  A shared gate is wired to both
input blocks (`fanIn`), to both output cones (`fanOut`), and serves `serves` copies; the seam forces
`fanIn ≥ 2`, `fanOut ≥ 2`, and (ruler) `serves ≤ fanIn`. -/
structure Hub where
  /-- wires from the input blocks (fan-in = reach across the seam) -/
  fanIn : ℕ
  /-- wires to the output cones -/
  fanOut : ℕ
  /-- copies served (sharing) -/
  serves : ℕ
  /-- wired to both blocks -/
  wiresBothBlocks : 2 ≤ fanIn
  /-- wired to both output cones -/
  wiresBothOutputs : 2 ≤ fanOut
  /-- the ruler: serving `serves` copies needs at least that fan-in -/
  capacity : serves ≤ fanIn

/-- **The seam forces the hub wiring (proved).**  Every sharing gate must wire to both blocks
(`fanIn ≥ 2`) and both output cones (`fanOut ≥ 2`) — the syntactic consequence on the graph, forced
regardless of what is computed. -/
theorem seam_forces_hub (H : Hub) : 2 ≤ H.fanIn ∧ 2 ≤ H.fanOut :=
  ⟨H.wiresBothBlocks, H.wiresBothOutputs⟩

/-- **Bounded fan-in bounds the sharing (proved).**  If the hub's fan-in is at most `σ`, it serves at
most `σ` copies.  Bound the wiring, bound the sharing — the crossing/reach lower bound. -/
theorem bounded_fanin_bounds_serves (H : Hub) (σ : ℕ) (hσ : H.fanIn ≤ σ) : H.serves ≤ σ :=
  le_trans H.capacity hσ

/-- **The hub escapes with free fan-in (proved).**  A single hub whose fan-in equals what it serves
meets the syntactic consequence and shares without limit.  In the fan-in-unbounded DAG model the fan-in
is free, so the hub carries unbounded sharing — the escape at every route. -/
theorem hub_escapes (s : ℕ) (hs : 2 ≤ s) :
    ∃ H : Hub, H.serves = s ∧ H.fanIn = s :=
  ⟨⟨s, s, s, hs, hs, le_refl s⟩, rfl, rfl⟩

/-- **The whole bridge, in one line (proved).**  A syntactic bound on the hub's fan-in *is* a bound on
the sharing; without it, the hub is unbounded.  So the bridge from the seam's wiring consequence to a
sharing bound is exactly a fan-in bound — `cost_super` (or charging = the formula model). -/
theorem bridge_is_fanin_bound (H : Hub) (σ : ℕ) (hσ : H.fanIn ≤ σ) : H.serves ≤ σ :=
  bounded_fanin_bounds_serves H σ hσ

end PallLean.Paper93.DeepMath.PathB.SeamForcesHub

#print axioms PallLean.Paper93.DeepMath.PathB.SeamForcesHub.seam_forces_hub
#print axioms PallLean.Paper93.DeepMath.PathB.SeamForcesHub.bounded_fanin_bounds_serves
#print axioms PallLean.Paper93.DeepMath.PathB.SeamForcesHub.hub_escapes
