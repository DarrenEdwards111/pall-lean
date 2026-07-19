import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingDeterminismIterate

/-!
# Crossing-time extraction: the `Nat.find` primitives and the base case

`sync_iterate` reduces the determinism to *supplying* the entry configs and their `CycleStep`s.  This
file provides the extraction primitives that read those off a real computation, and discharges the
**base case** (first entry).

* `exists_first_entry` — from existence of *some* time with head `> b`, the *least* such time `ts`
  has head `≤ b` at every earlier step: exactly the `hbefore`/`hcross` data `entry_frozen_and_head`
  needs.  (This is reused for every re-entry, not just the first.)
* `exists_first_exit` — dually, from existence of some time with head `≤ b`, the least such time has
  head `> b` before it: the `hright`/`hexit` data of a right-excursion.
* `first_entry_synced` — **the base case.**  Two computations with equal initial right tapes, each at
  its first entry (via the data above), with equal first-entry states, are `RightSynced` there: both
  heads are `b+1` (entry geometry) and both right tapes are frozen-equal to the common initial one.

## What still remains (NOT here)

The per-cycle extraction is intertwined with the induction, not separable into `sync_iterate`'s
up-front `CycleStep`s: a cycle's *shared* right-excursion length `d` is only valid because the two
computations are already `RightSynced` (their excursions run in lockstep, `run_local_right`), so each
`CycleStep` can only be extracted *after* `RightSynced` is known at that cycle.  The full determinism
is therefore a combined induction: `RightSynced` at cycle `k` ⇒ (extract exit `d` via
`exists_first_exit`; comp 2 exits at the same `d` by lockstep; extract re-entries `ℓ₁,ℓ₂` via
`exists_first_entry`; apply `cycle_preserves_sync`) ⇒ `RightSynced` at cycle `k+1`, with crossing
existence threaded as hypotheses and the palindrome fooling supplying the state equalities.  That
combined induction + fooling/counting is the remaining work; this file does **not** claim the
determinism theorem or the `Ω(n²)` bound.

Ceiling unchanged: even finished, an unconditional *restricted* bound (`crossingCount ≤ time` caps the
technique at polynomial; one-tape P `=` P), not `SAT ∉ P`.

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- **First-entry extraction.**  The least time with head `> b` has head `≤ b` at every earlier step —
the `entry_frozen_and_head` input.  Reused for every re-entry. -/
theorem exists_first_entry (M : Machine) (b : ℕ) (c : Cfg M)
    (hex : ∃ t, b < (run M t c).hd) :
    ∃ ts, (∀ j, j < ts → (run M j c).hd ≤ b) ∧ b < (run M ts c).hd := by
  refine ⟨Nat.find hex, fun j hj => ?_, Nat.find_spec hex⟩
  have := Nat.find_min hex hj
  omega

/-- **First-exit extraction.**  The least time with head `≤ b` has head `> b` at every earlier step —
the right-excursion `hright`/`hexit` data. -/
theorem exists_first_exit (M : Machine) (b : ℕ) (c : Cfg M)
    (hex : ∃ t, (run M t c).hd ≤ b) :
    ∃ ts, (∀ j, j < ts → b < (run M j c).hd) ∧ (run M ts c).hd ≤ b := by
  refine ⟨Nat.find hex, fun j hj => ?_, Nat.find_spec hex⟩
  have := Nat.find_min hex hj
  omega

/-- **Base case of the determinism.**  Two computations with equal initial right tapes, each run to
its first entry `ts₁, ts₂` (head `≤ b` before, `> b` at it), with equal first-entry states, are
`RightSynced` at those entries. -/
theorem first_entry_synced (M : Machine) (b : ℕ) (c₁ c₂ : Cfg M) (ts₁ ts₂ : ℕ)
    (hstart1 : c₁.hd ≤ b) (hstart2 : c₂.hd ≤ b)
    (hagree0 : ∀ p, b < p → c₁.tp.getD p false = c₂.tp.getD p false)
    (hbefore1 : ∀ j, j < ts₁ → (run M j c₁).hd ≤ b) (hcross1 : b < (run M ts₁ c₁).hd)
    (hbefore2 : ∀ j, j < ts₂ → (run M j c₂).hd ≤ b) (hcross2 : b < (run M ts₂ c₂).hd)
    (hstate : (run M ts₁ c₁).st = (run M ts₂ c₂).st) :
    RightSynced M b (run M ts₁ c₁) (run M ts₂ c₂) := by
  obtain ⟨hh1, hfroz1⟩ := entry_frozen_and_head M b c₁ ts₁ hstart1 hbefore1 hcross1
  obtain ⟨hh2, hfroz2⟩ := entry_frozen_and_head M b c₂ ts₂ hstart2 hbefore2 hcross2
  refine ⟨hh1, hh2, hstate, fun p hp => ?_⟩
  rw [hfroz1 p hp, hfroz2 p hp]
  exact hagree0 p hp

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
