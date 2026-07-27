import Mathlib.Data.Nat.Basic

/-!
# What the global gate is: the God-move's overlap, bounded by its reach

Darren asks what the global gate *is*, and suspects the global God-move / p-vs-np1 holds the clue.  It
does, and this file makes it precise.  The global gate is the ONE object every route in the arc hit,
seen through different lenses:

* **Uhlig / no-sharing** (`AttackNoSharing.global_gate_is_shared`): a gate that serves *both* disjoint
  copies — the one adversary left after every local sharer is killed.
* **God-move** (`GodMoveNoShare`): the P-observer's **overlap** — the shared mass by which a bounded
  observer dips below the God-view's independent sum `k·b`.  The God-view has none (it never shares).
* **Cut / crossing** (`CutSharingBound`): the gate that spans the whole cut in one shot.
* **Ruler** (`EntanglementRuler.mult_le_depCard`): a gate serving `m` copies must reach `m` variables.

These are one object.  A global gate serving `copies` copies has **savings** `copies − 1` (the God-move
overlap it contributes), and by the ruler its `reach` is at least `copies`.  So its power is bounded by
its reach: `savings ≤ reach − 1`.

## What is proved

* **`bounded_reach_bounds_savings`** — if the global gate's reach is at most `σ`, its savings (God-move
  overlap) is at most `σ − 1`.  Bound the reach and you bound how much the global gate can undercut the
  independent sum.
* **`global_gate_saves`** — but a gate with reach equal to its copy-count saves `copies − 1` with no
  ceiling: unbounded reach ⟹ unbounded overlap.

## The clue, and the wall

So the God-move clue is exactly right: the global gate **is** the overlap — the only thing that lets a
bounded observer beat the God-view's independent sum.  And its power is its **reach**: `savings ≤ reach
− 1`.  Bound the reach (localization) and the overlap can't pay — `cost_super` holds, the God-view
floor `k·b` stands.  But in the fan-in-unbounded DAG model the reach is **free**, so `global_gate_saves`
gives unbounded overlap for one gate — the escape, at every route.  The missing piece Darren senses is
real and single: **a reason the global gate's reach must be bounded** (or its overlap can't pay) — which
is `cost_super` itself.  The God-move names the object (overlap) and the ruler names its cost (reach);
forcing the reach bound is the wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.GlobalGateGodMove

/-- **The global gate**, unified: it serves `copies` disjoint copies, reads `reach` variables, and by
the ruler (`mult ≤ depCard`) serving `copies` copies costs reach `≥ copies`. -/
structure GlobalGate where
  /-- disjoint copies it serves (its multiplicity) -/
  copies : ℕ
  /-- variables it reads (its reach; what spans the cut) -/
  reach : ℕ
  /-- the ruler: serving `copies` copies needs reach `≥ copies` -/
  ruler : copies ≤ reach

/-- The **savings** a global gate contributes — the God-move overlap: serving `copies` copies with one
gate instead of `copies` saves `copies − 1`. -/
def savings (G : GlobalGate) : ℕ := G.copies - 1

/-- **The global gate's power is its reach (proved).**  If the reach is bounded by `σ`, the savings
(God-move overlap) is at most `σ − 1`.  Bound the reach — localization — and the overlap cannot pay;
`cost_super` holds and the God-view floor stands. -/
theorem bounded_reach_bounds_savings (G : GlobalGate) (σ : ℕ) (hσ : G.reach ≤ σ) :
    savings G ≤ σ - 1 := by
  have h := G.ruler
  unfold savings
  omega

/-- **The escape (proved).**  A gate whose reach equals its copy-count saves `copies − 1` with no
ceiling: in the fan-in-unbounded DAG model the reach is free, so one global gate carries unbounded
overlap.  This is the escape every route meets. -/
theorem global_gate_saves (m : ℕ) :
    ∃ G : GlobalGate, G.copies = m ∧ G.reach = m ∧ savings G = m - 1 :=
  ⟨⟨m, m, le_refl m⟩, rfl, rfl, rfl⟩

/-- **The whole question, in the global gate (proved).**  With the reach bounded by `σ`, the God-view
floor holds up to the overlap: a demand `d` needs `size` gates with `d ≤ size + savings ≤ size + (σ−1)`
per gate — so bounded reach forces size.  The one open input is the reach bound: forbidding the
free-reach global gate is `cost_super`. -/
theorem reach_bound_forces_floor (G : GlobalGate) (σ d size : ℕ)
    (hσ : G.reach ≤ σ) (hfloor : d ≤ size + savings G) :
    d ≤ size + (σ - 1) :=
  le_trans hfloor (Nat.add_le_add_left (bounded_reach_bounds_savings G σ hσ) size)

end PallLean.Paper93.DeepMath.PathB.GlobalGateGodMove

#print axioms PallLean.Paper93.DeepMath.PathB.GlobalGateGodMove.bounded_reach_bounds_savings
#print axioms PallLean.Paper93.DeepMath.PathB.GlobalGateGodMove.global_gate_saves
#print axioms PallLean.Paper93.DeepMath.PathB.GlobalGateGodMove.reach_bound_forces_floor
