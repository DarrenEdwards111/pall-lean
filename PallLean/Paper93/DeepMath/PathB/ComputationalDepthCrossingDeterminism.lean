import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingChaining

/-!
# The determinism induction: the one-cycle preservation step

The cut-and-paste determinism is an induction over crossing cycles.  This file proves its **inductive
step** — the single lemma that carries the "synchronized at entry" invariant across one full
`(right-excursion, left-excursion)` cycle — by composing everything below it in the tower.

The invariant, at a rightward crossing: both computations are at head `b+1`, in the same control
state, with equal tapes right of `b` (`RightSynced`).  One cycle:

1. **Right-excursion lockstep** (`run_local_right`): the excursion of length `d` runs both
   computations identically; comp 2 exits at the same `d`, with equal right tape.
2. **Left-excursion freeze, independently** (`entry_frozen_and_head`): each computation's left
   excursion (lengths `ℓ₁ ≠ ℓ₂` in general) leaves its right tape frozen and re-enters at head `b+1`.
3. **Re-establish the invariant**: at re-entry both heads are `b+1`; both right tapes equal the
   (equal) exit right tapes; and the states agree by the crossing-sequence hypothesis `hnextstate`.

`cycle_preserves_sync` packages exactly this.  It is the heart of the determinism induction: given the
per-cycle excursion structure and the crossing-sequence state-equality, `RightSynced` at entry `k`
gives `RightSynced` at entry `k+1`.

## What still remains for the full determinism theorem (NOT here)

Iterating `cycle_preserves_sync` needs the crossing bookkeeping: define the `k`-th entry/exit times
(`Nat.find` of the next crossing) so the excursion lengths `d, ℓ₁, ℓ₂` and the state-equality
hypotheses are *supplied* by the crossing sequences rather than assumed, plus the base case (first
entry, via `entry_frozen_and_head`) and the tail (both halt / no more crossings).  That top-level
recursive-time induction is the remaining assembly; the palindrome fooling/counting is further work.
This file does **not** claim the determinism theorem or the `Ω(n²)` bound.

Ceiling unchanged: even finished, an unconditional *restricted* bound (`crossingCount ≤ time` caps the
technique at polynomial; one-tape P `=` P), not `SAT ∉ P`.

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- **One-cycle preservation — the inductive step of the determinism.**  Two computations
`RightSynced` at a rightward crossing (both at head `b+1`, same state, equal right tape) are again
`RightSynced` at the next crossing, given the per-cycle excursion structure and that the next entry
states agree (the crossing-sequence hypothesis). -/
theorem cycle_preserves_sync (M : Machine) (b : ℕ) (c₁ c₂ : Cfg M) (d ℓ₁ ℓ₂ : ℕ)
    (hst : c₁.st = c₂.st) (hhd1 : c₁.hd = b + 1) (hhd2 : c₂.hd = b + 1)
    (hagree : ∀ p, b < p → c₁.tp.getD p false = c₂.tp.getD p false)
    (hright : ∀ j, j < d → b < (run M j c₁).hd)
    (hexit : (run M d c₁).hd ≤ b)
    (hleft1 : ∀ j, j < ℓ₁ → (run M (d + j) c₁).hd ≤ b)
    (hleft2 : ∀ j, j < ℓ₂ → (run M (d + j) c₂).hd ≤ b)
    (hentry1 : b < (run M (d + ℓ₁) c₁).hd)
    (hentry2 : b < (run M (d + ℓ₂) c₂).hd)
    (hnextstate : (run M (d + ℓ₁) c₁).st = (run M (d + ℓ₂) c₂).st) :
    (run M (d + ℓ₁) c₁).hd = b + 1 ∧ (run M (d + ℓ₂) c₂).hd = b + 1 ∧
      (run M (d + ℓ₁) c₁).st = (run M (d + ℓ₂) c₂).st ∧
      (∀ p, b < p → (run M (d + ℓ₁) c₁).tp.getD p false = (run M (d + ℓ₂) c₂).tp.getD p false) := by
  -- 1. right-excursion lockstep: comp 1 and comp 2 exit at the same d with equal right tape
  have hhd : c₁.hd = c₂.hd := by rw [hhd1, hhd2]
  obtain ⟨_, hexit_hd, hexit_tp⟩ := run_local_right M b c₁ c₂ d hst hhd hagree hright
  have hexit2 : (run M d c₂).hd ≤ b := by rw [← hexit_hd]; exact hexit
  -- 2a. comp 1 left excursion re-enters at b+1 with frozen right tape
  have hleft1' : ∀ j, j < ℓ₁ → (run M j (run M d c₁)).hd ≤ b := by
    intro j hj; rw [← run_add M d j c₁]; exact hleft1 j hj
  have hcross1 : b < (run M ℓ₁ (run M d c₁)).hd := by rw [← run_add M d ℓ₁ c₁]; exact hentry1
  obtain ⟨hh1, hfroz1⟩ := entry_frozen_and_head M b (run M d c₁) ℓ₁ hexit hleft1' hcross1
  -- 2b. comp 2 left excursion re-enters at b+1 with frozen right tape
  have hleft2' : ∀ j, j < ℓ₂ → (run M j (run M d c₂)).hd ≤ b := by
    intro j hj; rw [← run_add M d j c₂]; exact hleft2 j hj
  have hcross2 : b < (run M ℓ₂ (run M d c₂)).hd := by rw [← run_add M d ℓ₂ c₂]; exact hentry2
  obtain ⟨hh2, hfroz2⟩ := entry_frozen_and_head M b (run M d c₂) ℓ₂ hexit2 hleft2' hcross2
  -- 3. re-establish the invariant at the next entry
  refine ⟨?_, ?_, hnextstate, ?_⟩
  · rw [run_add M d ℓ₁ c₁]; exact hh1
  · rw [run_add M d ℓ₂ c₂]; exact hh2
  · intro p hp
    rw [run_add M d ℓ₁ c₁, run_add M d ℓ₂ c₂, hfroz1 p hp, hfroz2 p hp]
    exact hexit_tp p hp

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
