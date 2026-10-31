import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingLocalityLeft

/-!
# Left-side run-level gluing (mirror of `CrossingGluing`)

Lifts the left step-locality facts to whole excursions, mirroring `CrossingGluing` with region `≤ b`.

* `run_local_left` — **left-excursion lockstep.**  Two configurations sharing state, head, and left
  tape stay synchronized for as many steps as the head stays at `≤ b`.  (Iterated `step_local_left`.)
* `run_left_frozen` — **right-excursion freeze (for the left region).**  While the head stays at
  `> b`, the tape `≤ b` is unchanged after any number of steps.  (Iterated `step_left_frozen`.)

These are the two motions the *splice* alternates on the left side.  Scope unchanged: the chaining,
cycle, and recursive layers must still be mirrored, then the three-way splice, the palindrome family,
and the summation built.  This file does **not** claim the `Ω(n²)` bound, which stays a restricted
result (`crossingCount ≤ time` caps the technique at polynomial; one-tape P `=` P) not bearing on
`SAT ∉ P`.

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- **Left-excursion lockstep.**  If two configurations share state and head and agree on cells `≤ b`,
and the head of the first stays at `≤ b` for the first `k` steps, then after `k` steps the two still
share state and head and agree on `≤ b`. -/
theorem run_local_left (M : Machine) (b : ℕ) (c₁ c₂ : Cfg M) (k : ℕ)
    (hst : c₁.st = c₂.st) (hhd : c₁.hd = c₂.hd)
    (hagree : ∀ p, p ≤ b → c₁.tp.getD p false = c₂.tp.getD p false)
    (hstay : ∀ j, j < k → (run M j c₁).hd ≤ b) :
    (run M k c₁).st = (run M k c₂).st ∧ (run M k c₁).hd = (run M k c₂).hd ∧
      (∀ p, p ≤ b → (run M k c₁).tp.getD p false = (run M k c₂).tp.getD p false) := by
  revert hstay
  induction k with
  | zero => intro _; exact ⟨hst, hhd, hagree⟩
  | succ k ih =>
    intro hstay
    obtain ⟨ihst, ihhd, ihag⟩ := ih (fun j hj => hstay j (by omega))
    rw [run_succ, run_succ]
    exact step_local_left M b (run M k c₁) (run M k c₂) ihst ihhd (hstay k (by omega)) ihag

/-- **Frozen left region across a right-excursion.**  If the head stays at `> b` for the first `k`
steps, then the tape `≤ b` is unchanged after `k` steps. -/
theorem run_left_frozen (M : Machine) (b : ℕ) (c : Cfg M) (k : ℕ)
    (hstay : ∀ j, j < k → b < (run M j c).hd) (p : ℕ) (hp : p ≤ b) :
    (run M k c).tp.getD p false = c.tp.getD p false := by
  revert hstay
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hstay
    rw [run_succ, step_left_frozen M b (run M k c) (hstay k (by omega)) p hp]
    exact ih (fun j hj => hstay j (by omega))

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
