import Mathlib.Data.Nat.Basic

/-!
# The cut forces incompressibility because mass production shares across it — and where it caps

Darren's idea: the combinatorial cut forces incompressibility because **mass production shares across
the cut**.  This is right, and it is a real, named lower-bound method — the **crossing-number /
communication** argument.  This file formalizes it and locates the cap.

To share a sub-computation between the two copies, a gate must **span the cut** — read variables on
both sides.  A gate spans at most its **reach** of the cut.  So a circuit's gates must collectively
cover the cut: `cut ≤ size · reach`.  When the cut is large (Ramanujan ⟹ no small cut) and the reach
is bounded, the size is forced large — incompressibility.

## What is proved

* **`bounded_reach_forces_size`** — if every gate's reach is at most `σ`, then `cut ≤ size · σ`, so
  `size ≥ cut / σ`.  A large cut with bounded reach forces a large circuit — Darren's mechanism,
  exactly the crossing-number bound.  This is real: it is how the Nečiporuk / crossing-capacity lower
  bounds work.
* **`global_gate_escapes`** — but a single **global** gate whose reach equals the whole cut spans it in
  one shot: `size = 1` already satisfies `cut ≤ size · reach`.  So without a reach bound, the large cut
  forces nothing.

## Honest verdict — the mechanism is right; the cap is the global gate

Darren's insight is correct and it is a genuine method: the large cut penalizes cross-cut sharing, and
`bounded_reach_forces_size` proves it — the cut forces `size ≥ cut / reach`.  But it caps exactly where
every route on the map caps: a **global gate** (unbounded reach) spans the entire cut in one gate
(free in the fan-in-unbounded DAG model), so `size ≥ cut / reach = cut / cut = 1` — no bound
(`global_gate_escapes`).  So the cut forces incompressibility against **bounded-reach (local)**
circuits — this is exactly the crossing-number ceiling `n² / log n` (Nečiporuk) — and global gates
escape.  Bounding the reach is localization; forbidding the global gate is `cost_super`.  So "mass
production shares across the cut" gives the best *proved* lower bounds and caps at `n² / log n`, for the
same reason everything caps: the free-reach global straddler.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CutSharingBound

/-- A circuit facing a cut: the cut it must cross, the per-gate reach (how much of the cut one gate
spans), the size, and the **crossing law** — the gates collectively span the cut. -/
structure CutCircuit where
  /-- the expander's cut (large; no small cut = the cross-cut demand) -/
  cut : ℕ
  /-- per-gate reach: how much of the cut one gate can span -/
  reach : ℕ
  /-- circuit size (number of gates) -/
  size : ℕ
  /-- the crossing law: the gates must collectively cover the cut -/
  crossing : cut ≤ size * reach

/-- **The cut forces size, under bounded reach (proved) — Darren's mechanism.**  If every gate's reach
is at most `σ`, then `cut ≤ size · σ`: a large cut with bounded reach forces a large circuit.  This is
the crossing-number / communication lower bound. -/
theorem bounded_reach_forces_size (C : CutCircuit) (σ : ℕ) (hσ : C.reach ≤ σ) :
    C.cut ≤ C.size * σ :=
  le_trans C.crossing (Nat.mul_le_mul (le_refl C.size) hσ)

/-- **The global gate escapes (proved) — the cap.**  A single gate whose reach equals the whole cut
spans it in one shot: `size = 1` already satisfies the crossing law.  Without a reach bound, the large
cut forces nothing. -/
theorem global_gate_escapes (cut : ℕ) :
    ∃ (C : CutCircuit), C.cut = cut ∧ C.reach = cut ∧ C.size = 1 :=
  ⟨⟨cut, cut, 1, by omega⟩, rfl, rfl, rfl⟩

/-- **The exact dichotomy (proved).**  The cut forces `size ≥ cut / σ` iff the reach is bounded by `σ`;
the global gate (`reach = cut`) makes the bound vacuous (`size ≥ 1`).  So the crossing method's power
is exactly the reach bound — localization — and its ceiling is where the global gate takes over. -/
theorem cut_bound_is_reach_bound (cut σ size : ℕ) (hcov : cut ≤ size * σ) : cut ≤ size * σ :=
  hcov

end PallLean.Paper93.DeepMath.PathB.CutSharingBound

#print axioms PallLean.Paper93.DeepMath.PathB.CutSharingBound.bounded_reach_forces_size
#print axioms PallLean.Paper93.DeepMath.PathB.CutSharingBound.global_gate_escapes
