import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGlobalGateGodMove

/-!
# Attempting to bound the global gate's reach through SAT's seam — and the honest result

The whole problem, from `GlobalGateGodMove`: the global gate's power is its **reach** (`savings ≤
reach − 1`), so bounding the reach forces the God-view floor and gives `cost_super`.  The ask: bound
that reach through SAT's **seam structure** — the two disjoint copies the tower composes.

This file makes the honest attempt and reports what the seam actually gives.  It gives a **lower**
bound (a straddler across the seam must reach at least one variable per disjoint block, so `reach ≥ 2`)
— but it gives **no upper bound**: for any proposed ceiling `σ`, a seam-consistent global gate reaching
more than `σ` exists.  So SAT's seam structure does **not** bound the global gate's reach.

## What is proved

* **`seam_forces_reach_lower`** — a straddler serving the two disjoint copies (`2 ≤ copies`) must reach
  `≥ 2` (ruler): the seam's *lower* bound.
* **`seam_admits_reach_above`** — for every `σ`, there is a seam-consistent global gate (serving `2`
  copies) with `reach > σ`.  The seam admits arbitrarily large reach — **no upper bound**.

## Honest verdict — the seam does not bound the reach

Reach is a *syntactic* quantity — how many variables a gate reads — and in the fan-in-unbounded DAG
model a gate may read any subset, whatever the circuit computes.  SAT's seam is *semantic* structure
(two disjoint copies of a specific function); it constrains what must be computed, not how many
variables one gate may read.  So the seam forces `reach ≥ 2` (a straddler is nonlocal) but leaves the
reach unbounded above (`seam_admits_reach_above`): a global gate can read *all* of both blocks and
straddle via downstream cancellation (Uhlig mass production), which the disjointness does not forbid.

Bounding the reach from above — the one thing that would make the overlap unable to pay — is therefore
**not** given by the seam.  It is either a model restriction (bounded fan-in = the formula model,
capped at `P ⊄ NC¹`) or a bound on the *specific* SAT circuit ruling out the high-reach straddler,
which is `cost_super`.  I attempted the bound through the seam and it is not there; the seam gives the
lower half, the upper half is the wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SeamReachBound

open PallLean.Paper93.DeepMath.PathB.GlobalGateGodMove

/-- **The seam's lower bound (proved).**  A straddler serving the two disjoint copies of the seam
(`2 ≤ copies`) must reach at least two variables — one per block.  This is all the seam forces on the
reach: a lower bound, the nonlocality of a straddler. -/
theorem seam_forces_reach_lower (G : GlobalGate) (h2 : 2 ≤ G.copies) : 2 ≤ G.reach :=
  le_trans h2 G.ruler

/-- **The seam admits arbitrarily large reach (proved) — no upper bound.**  For every proposed ceiling
`σ`, there is a seam-consistent global gate (serving `2` copies) whose reach exceeds `σ`.  So SAT's
seam structure does NOT bound the global gate's reach from above. -/
theorem seam_admits_reach_above (σ : ℕ) :
    ∃ G : GlobalGate, σ < G.reach ∧ 2 ≤ G.copies := by
  refine ⟨⟨2, σ + 2, by omega⟩, ?_, ?_⟩
  · show σ < σ + 2
    omega
  · show 2 ≤ 2
    omega

/-- **No reach bound follows from the seam (proved).**  There is no `σ` bounding the reach of every
seam-consistent global gate: `seam_admits_reach_above` exceeds any candidate.  The upper bound — the
half that would force `cost_super` — is exactly what the seam does not supply. -/
theorem seam_gives_no_reach_bound :
    ¬ ∃ σ : ℕ, ∀ G : GlobalGate, 2 ≤ G.copies → G.reach ≤ σ := by
  intro h
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨G, hgt, h2⟩ := seam_admits_reach_above σ
  have := hσ G h2
  omega

end PallLean.Paper93.DeepMath.PathB.SeamReachBound

#print axioms PallLean.Paper93.DeepMath.PathB.SeamReachBound.seam_forces_reach_lower
#print axioms PallLean.Paper93.DeepMath.PathB.SeamReachBound.seam_admits_reach_above
#print axioms PallLean.Paper93.DeepMath.PathB.SeamReachBound.seam_gives_no_reach_bound
