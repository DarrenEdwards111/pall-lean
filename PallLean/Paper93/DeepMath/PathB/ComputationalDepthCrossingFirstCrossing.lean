import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingRecursive

/-!
# First-crossing identification (brick of connection A)

Connection (A) — relating `crossingSeq` (states at the *sorted* crossing times) to the splice's
`SpliceData` (states from the *recursive* `firstEntry`/`firstExit` chain) — begins by identifying the
first crossing.  From a head starting at `≤ b`, the first crossing is the *rightward* crossing at step
`firstEntryTime - 1`, and there is no crossing before it.

* `firstEntry_isCrossing` — step `firstEntryTime - 1` crosses `b` (head `≤ b → > b`).
* `no_crossing_before_firstEntry` — no step `t` with `t + 1 < firstEntryTime` crosses `b`.

Together: `firstEntryTime - 1` is the least element of `crossingTimes`, so it is the first entry of the
sorted crossing sequence.

## Honest scope

This is one brick.  The full connection (A) is substantial: it must identify **every** crossing time
with the recursive `firstEntry`/`firstExit` chain (base case here, plus the alternating inductive
step), reconcile the state timing (`crossingSeq` records the state *at* the crossing step; the splice
`SpliceData` uses the state *after*, at the landing), and relate the single-computation chain to the
three-way `nextSplice` triple.  Those remain, as does connection (B) (splice ⇒ acceptance) and the
`Ω(n)`-cut summation.  This file does **not** claim the `Ω(n²)` bound (restricted: `crossingCount ≤
time` caps the technique at polynomial, one-tape P `=` P, not `SAT ∉ P`).

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- **The first crossing is at `firstEntryTime - 1`.**  From head `≤ b`, the step that first takes the
head past `b` crosses `b` (a rightward crossing). -/
theorem firstEntry_isCrossing (M : Machine) (b : ℕ) (c : Cfg M)
    (hstart : c.hd ≤ b) (hex : ∃ t, b < (run M t c).hd) :
    crossesAt M c b (firstEntryTime M b c - 1) := by
  obtain ⟨hbefore, hentry⟩ := firstEntryTime_spec M b c hex
  have hpos : 1 ≤ firstEntryTime M b c := by
    rcases Nat.eq_zero_or_pos (firstEntryTime M b c) with h0 | hp
    · rw [h0, run_zero] at hentry; omega
    · exact hp
  have heq : firstEntryTime M b c - 1 + 1 = firstEntryTime M b c := by omega
  unfold crossesAt headAt
  refine Or.inl ⟨hbefore _ (by omega), ?_⟩
  rw [heq]; exact hentry

/-- **No crossing before the first entry.**  No step `t` with `t + 1 < firstEntryTime` crosses `b`
(the head stays at `≤ b` throughout). -/
theorem no_crossing_before_firstEntry (M : Machine) (b : ℕ) (c : Cfg M)
    (hex : ∃ t, b < (run M t c).hd) (t : ℕ) (ht : t + 1 < firstEntryTime M b c) :
    ¬ crossesAt M c b t := by
  obtain ⟨hbefore, _⟩ := firstEntryTime_spec M b c hex
  unfold crossesAt headAt
  rintro (⟨_, h2⟩ | ⟨_, h2⟩)
  · have := hbefore (t + 1) ht; omega
  · have := hbefore t (by omega); omega

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
