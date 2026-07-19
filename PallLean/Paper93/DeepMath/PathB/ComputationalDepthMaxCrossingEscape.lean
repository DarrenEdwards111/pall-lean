import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingEnergyTimeFloor

/-!
# A measure that escapes the time tie — `maxCrossing`, and what the escape does (and doesn't) buy

`crossingEnergy = Σ_b crossingCount(b)²` is tied to time (`Ω(time)`) because it *sums* over
boundaries: reaching space `P` alone forces energy `≥ P`.  The **peak** `maxCrossing = max_b
crossingCount(b)` is different — it is still `≤ time` (sound, `maxCrossing_le_time`) but does **not**
sum, so it can stay bounded while time grows.  This file proves the escape with a concrete witness.

## The escape (proved)

`driftM` is the one-state machine that moves right every step (a single rightward sweep).  Its head
is at position `t` after `t` steps, so each boundary `b < T` is crossed *exactly once*:

* `driftM_headAt` — `headAt driftM t = t`.
* `driftM_crossingCount_le` — every boundary is crossed at most once.
* `driftM_maxCrossing_le_one` — `maxCrossing ≤ 1`, **for every `T`**.
* `driftM_crossingEnergy_ge` — yet `crossingEnergy ≥ T`, and time `= T`.

So on this family `maxCrossing ≤ 1` while `crossingEnergy` and time grow without bound: `maxCrossing`
escapes the `Ω(time)` tie that `crossingEnergy` cannot.

## What the escape buys — and what it does not (honest)

Escaping the pointwise time tie does **not** hand back a discount:

* `maxCrossing` is still sound (`maxCrossing_le_time`), so `InvHard(maxCrossing) → separation` via the
  bridge, exactly as before.
* Because a machine *can* drive `maxCrossing` down (this file: `driftM` holds it at `1`),
  `InvHard(maxCrossing)` — every SAT decider having *superpolynomial* peak crossings — is a genuinely
  strong requirement (it must rule out every low-peak decider), and by schema-completeness it is still
  equivalent to the separation.  The escape moves the difficulty; it does not remove it.
* The one real gain: `maxCrossing` is *exactly* the quantity the crossing-sequence technique bounds
  (`crossing_state_repeat` is its pumping entry point) — a combinatorial handle that raw time lacks.
  But that technique is documented to top out at `Ω(n log n)` one-tape time (crossing-for-space
  tradeoff), far short of superpolynomial.

Verdict: `maxCrossing` genuinely escapes `crossingEnergy`'s time tie and carries a combinatorial
handle, but its `InvHard` remains separation-strength and beyond the known crossing ceiling — the
escape relocates the difficulty into crossing-sequence lower bounds rather than eliminating it.

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

attribute [local instance] Classical.propDecidable

/-- The one-state rightward-drift machine: never halts, moves right every step, never writes. -/
def driftM : Machine where
  State := Unit
  fin := inferInstance
  dec := inferInstance
  start := ()
  halt := fun _ => false
  δ := fun _ _ => ((), none, 1)
  accept := fun _ => false

/-- One drift step advances the head by one. -/
theorem driftM_step_hd (c : Cfg driftM) : (step driftM c).hd = c.hd + 1 := by
  unfold step moveHead
  rfl

/-- After `t` steps the drift head is at position `t`. -/
theorem driftM_headAt (x : List Bool) (t : ℕ) : headAt driftM (init driftM x) t = t := by
  unfold headAt
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, driftM_step_hd, ih]

/-- The drift machine crosses boundary `b` exactly at step `b`. -/
theorem driftM_crossesAt (x : List Bool) (b t : ℕ) :
    crossesAt driftM (init driftM x) b t ↔ b = t := by
  unfold crossesAt
  simp only [driftM_headAt]
  omega

/-- The drift machine crosses each boundary at most once. -/
theorem driftM_crossingCount_le (x : List Bool) (b T : ℕ) :
    crossingCount driftM (init driftM x) b T ≤ 1 := by
  unfold crossingCount crossingTimes
  have hsub : (Finset.range T).filter (fun t => crossesAt driftM (init driftM x) b t) ⊆ {b} := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_range, driftM_crossesAt] at ht
    rw [Finset.mem_singleton]
    omega
  calc ((Finset.range T).filter (fun t => crossesAt driftM (init driftM x) b t)).card
      ≤ ({b} : Finset ℕ).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton b

/-- **Bounded peak.**  `maxCrossing ≤ 1` for the drift machine, for every clock `T`. -/
theorem driftM_maxCrossing_le_one (x : List Bool) (S T : ℕ) :
    maxCrossing driftM (init driftM x) S T ≤ 1 := by
  unfold maxCrossing
  apply Finset.sup_le
  intro b _
  exact driftM_crossingCount_le x b T

/-- **Unbounded energy / time.**  `crossingEnergy ≥ T` for the drift machine run for `T` steps —
the head reaches position `T`, forcing energy at least `T`.  Together with the bounded peak, this is
the escape: `maxCrossing ≤ 1` while energy and time grow. -/
theorem driftM_crossingEnergy_ge (x : List Bool) (T : ℕ) :
    T ≤ crossingEnergy driftM (init driftM x) T T :=
  crossingEnergy_ge_reached (init driftM x) T T T T
    (driftM_headAt x 0) (le_refl T) (driftM_headAt x T) (le_refl T)

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
