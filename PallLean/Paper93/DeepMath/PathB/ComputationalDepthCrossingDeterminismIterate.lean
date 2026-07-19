import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingDeterminism

/-!
# The top-level determinism induction: iterating the cycle step

`cycle_preserves_sync` is the inductive *step*.  This file does the induction: it packages the
per-cycle excursion structure into a `CycleStep` relation, restates the step against a `RightSynced`
predicate, and iterates it `k` times.  The result: two computations that are `RightSynced` at their
first crossing and take `k` matching crossing cycles are `RightSynced` at their `k`-th crossing — the
right-of-`b` tape and the control state stay in lockstep across all `k` cycles.

* `RightSynced` — both configs at head `b+1`, same state, equal tape right of `b`.
* `CycleStep` — the per-cycle excursion structure (`∃ d ℓ₁ ℓ₂ …`) that advances entry configs to the
  next entry configs, with the next entry states agreeing.
* `cycleStep_preserves` — `RightSynced` + `CycleStep` ⇒ `RightSynced` at the next entry (a restatement
  of `cycle_preserves_sync`).
* `sync_iterate` — **the top-level induction.**  Given entry-config pairs `γ 0, …, γ k` with
  `RightSynced (γ 0)` and a `CycleStep` between each consecutive pair, `RightSynced (γ k)`.

## What still remains (NOT here)

`sync_iterate` reduces the full determinism to *supplying* `γ` and the `CycleStep`s.  That extraction —
reading the actual `k`-th entry configs off a computation via `Nat.find` of successive crossings, and
discharging each `CycleStep` from the real crossing times (with the next-entry state equality coming
from the assumed equal crossing sequences) — is the remaining bookkeeping, plus the base case (first
entry, `entry_frozen_and_head`).  On top of that determinism sits the palindrome fooling/counting.
This file does **not** claim the determinism theorem or the `Ω(n²)` bound.

Ceiling unchanged: even finished, an unconditional *restricted* bound (`crossingCount ≤ time` caps the
technique at polynomial; one-tape P `=` P), not `SAT ∉ P`.

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- Two configurations are right-synchronized at a crossing: both at head `b+1`, in the same control
state, agreeing on every tape cell right of `b`. -/
def RightSynced (M : Machine) (b : ℕ) (a₁ a₂ : Cfg M) : Prop :=
  a₁.hd = b + 1 ∧ a₂.hd = b + 1 ∧ a₁.st = a₂.st ∧
    (∀ p, b < p → a₁.tp.getD p false = a₂.tp.getD p false)

/-- One crossing cycle relating entry configs `a₁,a₂` to the next entry configs `a₁',a₂'`: a shared
right-excursion of length `d`, then left excursions of lengths `ℓ₁,ℓ₂` re-entering the right region,
with the next entry states equal (the crossing-sequence datum). -/
def CycleStep (M : Machine) (b : ℕ) (a₁ a₂ a₁' a₂' : Cfg M) : Prop :=
  ∃ d ℓ₁ ℓ₂,
    a₁' = run M (d + ℓ₁) a₁ ∧ a₂' = run M (d + ℓ₂) a₂ ∧
    (∀ j, j < d → b < (run M j a₁).hd) ∧ (run M d a₁).hd ≤ b ∧
    (∀ j, j < ℓ₁ → (run M (d + j) a₁).hd ≤ b) ∧
    (∀ j, j < ℓ₂ → (run M (d + j) a₂).hd ≤ b) ∧
    b < (run M (d + ℓ₁) a₁).hd ∧ b < (run M (d + ℓ₂) a₂).hd ∧
    (run M (d + ℓ₁) a₁).st = (run M (d + ℓ₂) a₂).st

/-- The inductive step, against the predicates: `RightSynced` is preserved across one `CycleStep`. -/
theorem cycleStep_preserves (M : Machine) (b : ℕ) (a₁ a₂ a₁' a₂' : Cfg M)
    (h : RightSynced M b a₁ a₂) (hc : CycleStep M b a₁ a₂ a₁' a₂') :
    RightSynced M b a₁' a₂' := by
  obtain ⟨hhd1, hhd2, hst, hagree⟩ := h
  obtain ⟨d, ℓ₁, ℓ₂, hnext1, hnext2, hright, hexit, hleft1, hleft2, hentry1, hentry2, hnextstate⟩ := hc
  subst hnext1 hnext2
  exact cycle_preserves_sync M b a₁ a₂ d ℓ₁ ℓ₂ hst hhd1 hhd2 hagree hright hexit hleft1 hleft2
    hentry1 hentry2 hnextstate

/-- **Top-level induction.**  Entry-config pairs `γ 0, …, γ k` that are `RightSynced` at `γ 0` and
joined by a `CycleStep` at each consecutive pair are `RightSynced` at `γ k`. -/
theorem sync_iterate (M : Machine) (b : ℕ) (k : ℕ) (γ : ℕ → Cfg M × Cfg M)
    (h0 : RightSynced M b (γ 0).1 (γ 0).2)
    (hstep : ∀ j, j < k → CycleStep M b (γ j).1 (γ j).2 (γ (j + 1)).1 (γ (j + 1)).2) :
    RightSynced M b (γ k).1 (γ k).2 := by
  revert hstep
  induction k with
  | zero => intro _; exact h0
  | succ k ih =>
    intro hstep
    exact cycleStep_preserves M b (γ k).1 (γ k).2 (γ (k + 1)).1 (γ (k + 1)).2
      (ih (fun j hj => hstep j (by omega))) (hstep k (by omega))

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
