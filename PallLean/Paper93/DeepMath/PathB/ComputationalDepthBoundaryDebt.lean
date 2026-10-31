import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Boundary debt: the "merge now ⇒ pay later" conservation law (proved), and the open SAT-debt input

The new-maths target at the all-decompositions wall: stop treating decompositions as arbitrary and track a
**conserved boundary quantity** an adaptive observer cannot escape.  The quantity is **distinguishability
debt** — pairs of must-be-separated continuations that the observer has currently *merged* (given the same
boundary state).  This file builds the debt framework and proves its accounting heart, isolating exactly the
open input.

## The four steps (HAL's plan) — proved vs named

1. **merging distinguishable continuations creates debt** — `merge_creates_debt`, `correct_view_zero_debt`:
   debt counts merged must-separate pairs; a *correct* observer (separating all such pairs) has debt `0`, and
   merging a must-separate pair contributes debt.  **Proved (definitional).**
2. **expansion prevents debt from disappearing locally** — the per-step servicing bound `rate` (debt can drop
   by `≤ rate` per step) is the expander/amplification content.  **Named** as the hypothesis `hservice` (its
   tightness is the expander input, §VI of the capstone).
3. **bounded boundary services `O(B)` debt per step** — `rate` is the boundary's per-step servicing capacity.
   **Named** (model-specific; `rate ≤` boundary capacity).
4. **SAT-like witness geometry creates super-log total debt** — `initial debt = ω(log n)` for SAT under every
   decomposition.  **This is the open quantifier** (`= CookLevinFrontierHyp` in debt form); **not proved.**

## The proved conservation (the accounting heart)

* `debt_conservation` — telescoping: `debt 0 ≤ debt T + T · rate`.  **Proved.**
* `merge_pay` — **"merge now ⇒ pay later"**: if the observer is *correct by time `T`* (`debt T = 0`), then
  `debt 0 ≤ T · rate` — the initial (merge) debt is fully paid over `T` steps at servicing rate `rate`.
* `debt_forces_time` — the tradeoff: clearing debt `≥ D` needs `D ≤ T · rate`, i.e. `T ≥ D / rate`.

So **"merge now ⇒ pay later" is a theorem** (conservation).  What it does **not** give is the lower bound:
that requires step 4 — that SAT's *initial* debt `D` is super-polynomial under *every* adaptive decomposition,
with `rate = O(B)` — which is exactly the open all-decompositions quantifier, restated in debt form.  Nothing
here asserts it.

## Honest status

A genuine new reformulation: the all-decompositions wall becomes "SAT generates super-log conserved debt".
The conservation accounting is proved; the debt grounding is proved; **the SAT-super-debt and the expander
servicing-tightness are the named open/hard inputs** — `P ≠ NP` is not touched.
-/

namespace PallLean.Paper93.DeepMath.PathB.BoundaryDebt

open scoped BigOperators

/-! ## The conservation accounting (proved) -/

/-- **Debt conservation (telescoping, proved).**  If the debt drops by at most `rate` per step
(`debt t ≤ debt (t+1) + rate`), then the initial debt is bounded by the final debt plus `T · rate`. -/
theorem debt_conservation (debt : ℕ → ℕ) (rate : ℕ)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + rate) (T : ℕ) :
    debt 0 ≤ debt T + T * rate := by
  induction T with
  | zero => simp
  | succ k ih =>
      calc debt 0 ≤ debt k + k * rate := ih
        _ ≤ (debt (k + 1) + rate) + k * rate := by have := hservice k; omega
        _ = debt (k + 1) + (k + 1) * rate := by ring

/-- **"Merge now ⇒ pay later" (proved).**  If the observer is correct by time `T` (all debt cleared,
`debt T = 0`), then the initial (merge) debt is paid over `T` steps at servicing rate `rate`:
`debt 0 ≤ T · rate`. -/
theorem merge_pay (debt : ℕ → ℕ) (rate : ℕ)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + rate) (T : ℕ) (hcleared : debt T = 0) :
    debt 0 ≤ T * rate := by
  have h := debt_conservation debt rate hservice T
  omega

/-- **The debt–time tradeoff (proved).**  Clearing an initial debt of at least `D` (by time `T`, at servicing
rate `rate`) forces `D ≤ T · rate` — i.e. `T ≥ D / rate`: more merged debt now costs more time later. -/
theorem debt_forces_time (debt : ℕ → ℕ) (rate : ℕ)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + rate) (T : ℕ) (hcleared : debt T = 0)
    {D : ℕ} (hD : D ≤ debt 0) :
    D ≤ T * rate :=
  le_trans hD (merge_pay debt rate hservice T hcleared)

/-! ## Grounding: debt counts merged must-separate pairs (proved) -/

variable {X S : Type*} [DecidableEq S]

/-- **Distinguishability debt** of a view: the number of must-separate pairs (`F`) the view currently
**merges** (assigns the same boundary state). -/
def debtCount (F : Finset (X × X)) (view : X → S) : ℕ :=
  (F.filter (fun p => view p.1 = view p.2)).card

/-- **A correct observer has zero debt.**  If `view` separates every must-separate pair, its debt is `0`. -/
theorem correct_view_zero_debt (F : Finset (X × X)) (view : X → S)
    (hsep : ∀ p ∈ F, view p.1 ≠ view p.2) :
    debtCount F view = 0 := by
  rw [debtCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact hsep

/-- **Merging creates debt.**  If a sub-collection `G ⊆ F` of must-separate pairs is entirely merged by the
view, the debt is at least `|G|` — merging `K` distinguishable pairs incurs debt `≥ K`. -/
theorem merge_creates_debt (F : Finset (X × X)) (view : X → S) {G : Finset (X × X)}
    (hGF : G ⊆ F) (hmerged : ∀ p ∈ G, view p.1 = view p.2) :
    G.card ≤ debtCount F view := by
  rw [debtCount]
  apply Finset.card_le_card
  intro p hp
  exact Finset.mem_filter.mpr ⟨hGF hp, hmerged p hp⟩

end PallLean.Paper93.DeepMath.PathB.BoundaryDebt

#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.merge_pay
#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.correct_view_zero_debt
#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.merge_creates_debt
