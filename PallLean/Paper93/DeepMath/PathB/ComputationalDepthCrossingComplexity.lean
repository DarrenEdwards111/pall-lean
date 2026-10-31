import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHennieDrift

/-!
# A candidate inside the corridor: crossing complexity

The corridor demands an observer invariant that is **sound** (size-dominated), **time-sensitive**
(not space-bounded), and **not a function-complexity measure** (poly on P-languages).  The
principled candidate is **crossing complexity** — the trace measure behind the classical one-tape
`Ω(n log n)` time lower bounds (Hennie).  Unlike tableau rank (`≤ space`, too weak) and `distinctRows`
(polynomially equal to time, no structural handle), crossing complexity carries a genuine
lower-bound *technique*: the crossing-sequence cut-and-paste, whose core pumping step is exactly
`no_rightward_repeat`.

For a boundary `b` (between cells `b` and `b+1`), `crossingCount M c b T` counts how many of the
first `T` steps move the head across `b`.

## Corridor membership

* **Sound** (`crossingCount_le_time`): `crossingCount ≤ T` — one crossing of a fixed boundary per
  step.  So it is size-dominated and, being a trace property bounded by time, is poly on every
  poly-time decider — *not* a function-complexity measure like `subfunProfile` (which is superpoly
  on the P-language `dIndexLang`).  This clears both the upper wall (unlike function complexity, it
  stays sound) and the "not function-complexity" requirement.
* **Time-sensitive, not space-bounded**: a *single* boundary can be crossed `Θ(T)` times by a head
  oscillating in `O(1)` space, so `crossingCount` is not bounded by space — unlike `traceRank ≤
  rowMax`.  (The general statement is `#moves ≤ (maxHead+1)·maxCrossing`, i.e. `maxCrossing ≥
  moves/space`; here we record the sound direction and the pumping handle, the two facts that make
  it a live candidate.)

## The handle

* `crossing_state_repeat`: if a boundary is crossed more than `|State|` times, two of those crossings
  occur in the **same control state** — the entry point for the crossing-sequence pumping/cut-and-
  paste argument.  `no_rightward_repeat` is precisely the instance of that pumping that forbids an
  infinite rightward drift.  This is a real technique; `distinctRows` had none.

## Honest ceiling

The crossing-sequence technique proves `Ω(n log n)` one-tape time lower bounds and no more: crossings
can be traded for space (multi-tape), and cut-and-paste saves only a logarithmic factor.  So crossing
complexity is a genuine corridor candidate with a real *but capped* handle — making it
superpolynomial on SAT is, like every sound-and-hard invariant, equivalent to the separation.  What
this file provides is the concrete candidate and its technique's entry point, and it names the exact
barrier a stronger handle must beat: the crossing-for-space tradeoff.

Nothing here proves a separation or that any invariant is hard.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

attribute [local instance] Classical.propDecidable

variable {M : Machine}

/-- Head position at time `t`. -/
def headAt (M : Machine) (c : Cfg M) (t : ℕ) : ℕ := (run M t c).hd

/-- Control state at time `t`. -/
def stateAt (M : Machine) (c : Cfg M) (t : ℕ) : M.State := (run M t c).st

/-- Step `t` moves the head across boundary `b` (between cells `b` and `b+1`). -/
def crossesAt (M : Machine) (c : Cfg M) (b t : ℕ) : Prop :=
  (headAt M c t ≤ b ∧ b < headAt M c (t + 1)) ∨ (headAt M c (t + 1) ≤ b ∧ b < headAt M c t)

/-- The steps in `[0,T)` that cross boundary `b`. -/
noncomputable def crossingTimes (M : Machine) (c : Cfg M) (b T : ℕ) : Finset ℕ :=
  (Finset.range T).filter (fun t => crossesAt M c b t)

/-- How many of the first `T` steps cross boundary `b`. -/
noncomputable def crossingCount (M : Machine) (c : Cfg M) (b T : ℕ) : ℕ :=
  (crossingTimes M c b T).card

/-- **Sound / size-dominated.**  A fixed boundary is crossed at most once per step. -/
theorem crossingCount_le_time (c : Cfg M) (b T : ℕ) : crossingCount M c b T ≤ T := by
  unfold crossingCount crossingTimes
  calc ((Finset.range T).filter (fun t => crossesAt M c b t)).card
        ≤ (Finset.range T).card := Finset.card_filter_le _ _
    _ = T := Finset.card_range T

/-- **The pumping handle.**  If boundary `b` is crossed more than `|State|` times, two crossings
occur in the same control state — the entry point for crossing-sequence cut-and-paste (of which
`no_rightward_repeat` is the rightward-drift instance). -/
theorem crossing_state_repeat (c : Cfg M) (b T : ℕ)
    (h : Fintype.card M.State < crossingCount M c b T) :
    ∃ t1 ∈ crossingTimes M c b T, ∃ t2 ∈ crossingTimes M c b T,
      t1 ≠ t2 ∧ stateAt M c t1 = stateAt M c t2 := by
  apply Finset.exists_ne_map_eq_of_card_lt_of_maps_to (t := (Finset.univ : Finset M.State))
    (f := stateAt M c)
  · rw [Finset.card_univ]; exact h
  · intro a _; exact Finset.mem_univ _

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
