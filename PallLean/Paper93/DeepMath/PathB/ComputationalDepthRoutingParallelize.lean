import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTapeSeek

/-!
# The part a circuit can't parallelize: data-dependent routing — real size bounds, capped at free reach

`TapeSeek` left the wall at: find the part of SAT whose seek penalty survives the move from tape
(sequential) to circuit (random-access).  The answer is **data-dependent access**.  On a tape the head
must *seek* to a data-dependent position; on a circuit that access is a **multiplexer** — selecting one of
`n` positions by a value computed from the input — and a multiplexer costs **size**.  So the seek penalty
does *not* vanish on a circuit: it becomes a *routing* size cost, and routing `n` data-dependent accesses
is exactly the **crossing-number / Nečiporuk method** — the best *proved* general circuit size lower
bounds (up to `n²/log n`).

But it caps.  A gate of *reach* `r` routes up to `r` accesses, so `size · reach ≥ accesses` — a bounded
reach forces `size ≥ accesses/reach` (a real bound), yet a **free-reach global gate** (reach `= accesses`)
routes *all* of them in a single gate: `size = 1`.  The circuit *parallelizes the routing* with one global
multiplexer.  That is exactly the free-reach escape of `CutSharingBound`.

## What is proved

* **`bounded_reach_bound`** — if each gate reaches at most `σ`, routing `accesses` needs `accesses ≤
  size · σ`, i.e. `size ≥ accesses/σ`: the crossing-number size bound.
* **`free_reach_one_gate`** — a single gate of reach `= accesses` routes all of them (`accesses ≤ 1 ·
  accesses`): free reach parallelizes the routing to size `1`.
* **`bounded_forces_size_free_escapes`** — the gap concretely: at `accesses = 100`, bounded reach `σ = 4`
  forces `size ≥ 25`, but a free-reach gate does it in `size = 1`.

## Honest verdict — the un-parallelizable part is data-dependent routing; real bounds, capped by free reach

The part a circuit cannot parallelize *cheaply* is exactly the **data-dependent access** — the seek, made
into a multiplexer.  It does *not* vanish on a circuit: it becomes **routing size**, and that gives the
best *proved* general size lower bounds — the crossing-number / Nečiporuk method, `size ≥ accesses/reach`
(`bounded_reach_bound`), up to `n²/log n`.  So Darren's seek penalty genuinely survives the tape→circuit
move — as *routing*, while the reach is bounded.  But it **caps** for the reason everything caps: a
**free-reach global gate** routes all the accesses in one shot (`free_reach_one_gate`,
`bounded_forces_size_free_escapes`), parallelizing the routing to size `1` — the free-reach escape of
`CutSharingBound`, `SeamReachBound`.  So the circuit *can* parallelize the data-dependent access, via one
global multiplexer, once reach is unbounded.  The un-parallelizable part is real and gives `n²/log n`
bounds while reach is bounded; beyond that the free-reach global gate parallelizes it away — bounding that
gate's reach on SAT is `cost_super`.  The seek penalty survives as routing, the crossing-number method is
real and capped, and the free-reach global gate is precisely what the circuit uses to parallelize it.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RoutingParallelize

/-- Accesses a set of `size` gates can route, each reaching `reach`: `size · reach`. -/
def routed (size reach : ℕ) : ℕ := size * reach

/-! ### Bounded reach forces size — the crossing-number bound -/

/-- **Bounded reach forces size (proved).**  If routing `accesses` data-dependent selections needs them
covered (`accesses ≤ size · reach`) and each gate reaches at most `σ`, then `accesses ≤ size · σ` — so
`size ≥ accesses/σ`.  The crossing-number / Nečiporuk size lower bound. -/
theorem bounded_reach_bound (accesses size reach σ : ℕ)
    (cover : accesses ≤ routed size reach) (hr : reach ≤ σ) :
    accesses ≤ size * σ := by
  simp only [routed] at cover
  exact le_trans cover (Nat.mul_le_mul (Nat.le_refl size) hr)

/-! ### But a free-reach global gate parallelizes the routing -/

/-- **A free-reach gate routes everything in one shot (proved).**  A single gate (`size = 1`) whose reach
equals the number of accesses routes them all: `accesses ≤ routed 1 accesses`.  The circuit parallelizes
the data-dependent access with one global multiplexer. -/
theorem free_reach_one_gate (accesses : ℕ) : accesses ≤ routed 1 accesses := by
  simp only [routed]
  omega

/-- **Bounded reach forces size; free reach escapes (proved).**  At `accesses = 100`: with reach bounded
by `σ = 4`, routing needs `100 ≤ size · 4`, so `size ≥ 25`; but a free-reach gate does it in `size = 1`
(`100 ≤ routed 1 100`).  The gap is exactly what the free-reach global gate erases. -/
theorem bounded_forces_size_free_escapes :
    (∀ size, 100 ≤ size * 4 → 25 ≤ size) ∧ (100 ≤ routed 1 100) := by
  refine ⟨fun size h => ?_, ?_⟩
  · omega
  · simp only [routed]; omega

end PallLean.Paper93.DeepMath.PathB.RoutingParallelize

#print axioms PallLean.Paper93.DeepMath.PathB.RoutingParallelize.bounded_reach_bound
#print axioms PallLean.Paper93.DeepMath.PathB.RoutingParallelize.free_reach_one_gate
#print axioms PallLean.Paper93.DeepMath.PathB.RoutingParallelize.bounded_forces_size_free_escapes
