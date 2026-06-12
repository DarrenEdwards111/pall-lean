import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingBound

/-!
# Route F — the `O(log n)`-crossings claim for an oblivious TM (Hennie pigeonhole, proved)

The crossing-sequence reduction (`CrossingBound`) reduced the P-side rank bound to: *the head crosses the
cut `O(log n)` times*.  Here we **prove** that claim — for an **oblivious** Turing machine (head trajectory
independent of the input) satisfying a width condition — via the classical **Hennie pigeonhole**:

> Over `T` steps a head moving `≤ 1` cell/step crosses *all* `W` cuts a total of `≤ T` times, so **some**
> cut is crossed `≤ T/W` times.

## Proved

* `totalCrossings_le` — `∑_{k<W} crossings(k) ≤ T` (each step crosses ≤ 1 cut).
* `exists_fewCrossings` — `∃ k < W`, `crossings(k) ≤ T / W`.
* `oblivious_fixed_cut_few_crossings` — for an oblivious trajectory `pos` (a *fixed* function of the input
  *length*, not its contents), under the width condition `T ≤ (c·log₂ n)·W`, **there is a fixed cut crossed
  `≤ c·log₂ n` times** — the same cut for every input.

Composed with `CrossingBound.spaceCut_rank_poly_of_fewCrossings`, this gives **`poly(n)` space-cut rank for
an oblivious, wide computation** — `CookLevinLaneClassified` becomes a *theorem* in that regime.

## The honest residual

The width condition `T ≤ (c·log₂ n)·W`, i.e. `W ≥ T/(c·log₂ n)`, is real and not free:

* It holds when the machine uses space `W` comparable to its time `T` (e.g. `W ≥ T/log n`) — then the best
  cut has `O(log n)` crossings and the rank is `poly(n)`.  **For that class the claim is now proved.**
* It **fails** for *small-space* poly-time machines (`W ≪ T/log n`): the best cut still has `≫ log n`
  crossings, and a non-oblivious machine can cross `Θ(T)` times.  Also, *making* an arbitrary machine
  oblivious inflates `T` (oblivious simulation costs `T → Õ(T)` or more), which can break the width
  condition.

So this proves the `O(log n)`-crossings claim **exactly for oblivious, wide (space ≳ time/log) machines**,
and pins the remaining gap to a precise statement: *the Cook–Levin compilation is oblivious and uses space
`≥ time/log n`* (or the SPDP partition is chosen so the effective crossing count is `O(log n)`).  That is
the genuine open content; nothing here asserts it for an arbitrary poly-time machine.
-/

namespace PallLean.Paper93.DeepMath.PathB.Crossings

open Finset

/-- Number of times the head crosses cut `k` (between cells `k`, `k+1`) over `T` steps. -/
def crossings (pos : ℕ → ℕ) (k T : ℕ) : ℕ :=
  ((Finset.range T).filter (fun t =>
    min (pos t) (pos (t + 1)) ≤ k ∧ k < max (pos t) (pos (t + 1)))).card

/-- **Total crossings `≤ T`.**  A head moving `≤ 1` cell per step crosses `≤ 1` cut per step, so the total
over all `W` cuts is `≤` the number of steps. -/
theorem totalCrossings_le (pos : ℕ → ℕ) (W T : ℕ)
    (hmove : ∀ t, max (pos t) (pos (t + 1)) - min (pos t) (pos (t + 1)) ≤ 1) :
    ∑ k ∈ Finset.range W, crossings pos k T ≤ T := by
  have hcr : ∀ k, crossings pos k T =
      ∑ t ∈ Finset.range T,
        (if min (pos t) (pos (t + 1)) ≤ k ∧ k < max (pos t) (pos (t + 1)) then 1 else 0) := by
    intro k; rw [crossings, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [hcr]
  rw [Finset.sum_comm]
  have hinner : ∀ t, (∑ k ∈ Finset.range W,
      (if min (pos t) (pos (t + 1)) ≤ k ∧ k < max (pos t) (pos (t + 1)) then 1 else 0)) ≤ 1 := by
    intro t
    rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
    calc ((Finset.range W).filter
            (fun k => min (pos t) (pos (t + 1)) ≤ k ∧ k < max (pos t) (pos (t + 1)))).card
        ≤ (Finset.Ico (min (pos t) (pos (t + 1))) (max (pos t) (pos (t + 1)))).card :=
          Finset.card_le_card (by intro k hk; rw [mem_filter] at hk; rw [mem_Ico]; exact hk.2)
      _ = max (pos t) (pos (t + 1)) - min (pos t) (pos (t + 1)) := Nat.card_Ico _ _
      _ ≤ 1 := hmove t
  calc ∑ t ∈ Finset.range T, ∑ k ∈ Finset.range W,
          (if min (pos t) (pos (t + 1)) ≤ k ∧ k < max (pos t) (pos (t + 1)) then 1 else 0)
      ≤ ∑ _t ∈ Finset.range T, 1 := Finset.sum_le_sum (fun t _ => hinner t)
    _ = T := by rw [← Finset.card_eq_sum_ones, Finset.card_range]

/-- **Hennie pigeonhole: some cut is crossed `≤ T/W` times.** -/
theorem exists_fewCrossings (pos : ℕ → ℕ) (W T : ℕ) (hW : 0 < W)
    (hmove : ∀ t, max (pos t) (pos (t + 1)) - min (pos t) (pos (t + 1)) ≤ 1) :
    ∃ k, k < W ∧ crossings pos k T ≤ T / W := by
  by_contra h
  push_neg at h
  have hge : ∀ k ∈ Finset.range W, T / W + 1 ≤ crossings pos k T :=
    fun k hk => h k (Finset.mem_range.mp hk)
  have hsum : W * (T / W + 1) ≤ ∑ k ∈ Finset.range W, crossings pos k T := by
    have h1 := Finset.card_nsmul_le_sum (Finset.range W) _ (T / W + 1) hge
    simpa [Finset.card_range, smul_eq_mul] using h1
  have htot := totalCrossings_le pos W T hmove
  have hdm := Nat.div_add_mod T W
  have hmod := Nat.mod_lt T hW
  have hexp : W * (T / W + 1) = W * (T / W) + W := by ring
  omega

/-- **`O(log n)` crossings for an oblivious TM (under the width condition).**  If the head trajectory `pos`
is fixed (oblivious) and `T ≤ (c·log₂ n)·W`, then there is a single cut — the same for every input —
crossed `≤ c·log₂ n` times. -/
theorem oblivious_fixed_cut_few_crossings (pos : ℕ → ℕ) (W T c n : ℕ) (hW : 0 < W)
    (hmove : ∀ t, max (pos t) (pos (t + 1)) - min (pos t) (pos (t + 1)) ≤ 1)
    (hwidth : T ≤ c * Nat.log 2 n * W) :
    ∃ k, k < W ∧ crossings pos k T ≤ c * Nat.log 2 n := by
  obtain ⟨k, hk, hcr⟩ := exists_fewCrossings pos W T hW hmove
  refine ⟨k, hk, le_trans hcr ?_⟩
  calc T / W ≤ (c * Nat.log 2 n * W) / W := Nat.div_le_div_right hwidth
    _ = c * Nat.log 2 n := Nat.mul_div_cancel _ hW

end PallLean.Paper93.DeepMath.PathB.Crossings

#print axioms PallLean.Paper93.DeepMath.PathB.Crossings.oblivious_fixed_cut_few_crossings
