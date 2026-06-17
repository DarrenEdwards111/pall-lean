import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ChernoffBound

/-!
# The fiber-count reduction — bad approximant-tuples bounded by the binomial tail (proved)

Entry 209 proved the combinatorial Chernoff bound (`binomial_tail_le` / `term_mono`) and corrected entry 208: the
per-input concentration must be over a **supply** of approximants, with `a` correct and `b` wrong at the fixed input.
This file proves the **fiber-count reduction** connecting the two: the number of `k`-tuples of supply approximants whose
*majority errs* at the input is `≤ 2^k · a^m · b^{k−m}` — exactly the Chernoff bound.

The reduction.  Map each tuple `g : Fin k → α` to its **correctness pattern** `pat g := fun i => pred (g i) : Fin k →
Bool`.  Whether the majority errs depends only on `pat g` (the number of correct coordinates is `#{i | pat g i}`).  So
the bad tuples partition into pattern-fibers (`Finset.card_eq_sum_card_fiberwise`); each fiber `{g | pat g = p}` has
cardinality `a^{#trues p} · b^{#falses p}` (`fiber_card`, via `Fintype.card_piFinset`), which for a *bad* pattern
(`#trues ≤ m`) is `≤ a^m · b^{k−m}` (entry-209 `term_mono`); and there are `≤ 2^k` patterns.

## What is proved (clean axioms, no `sorry`)

* **`fiber_card`** — the pattern-fiber cardinality: `#{g : Fin k → α | ∀ i, pred (g i) = p i} = a^{#trues p} ·
  b^{#falses p}` (`Fintype.card_piFinset` + `Finset.prod_ite` + `Finset.prod_const`), with `a = #{pred}`, `b = #{¬pred}`.
* **`bad_tuple_count_le`** — the reduction: `#{g : Fin k → α | #{i | pred (g i)} ≤ m} ≤ 2^k · a^m · b^{k−m}` (for
  `b ≤ a`, `m ≤ k`) — the per-input concentration bound, via the pattern-fiberwise sum, `term_mono`, and `≤ 2^k`
  patterns.

## Honest scope

This proves the **fiber-count reduction** completely — that the number of bad approximant-tuples at a fixed input is
`≤ 2^k · a^m · b^{k−m}` (the Chernoff bound), via genuine `Finset`/`Fintype` counting (`card_piFinset`, fiberwise
partition) reusing entry-209's `term_mono`.  Combined with entry 209 this is the per-input bound over a supply with `a`
correct, `b` wrong.  What remains to reach the corrected `ChernoffPerInput`-over-supply is the **decay arithmetic**:
that for a `≥3/4` supply (`a ≥ 3b`) and `k = Ω(n)`, this bound times `2^n` is below `#tuples = (a+b)^k` (the
`exp(−Ω(k))` step) — and the construction of an actual supply with the `≥3/4` property at every input (from the
existing `acc0_approx_by_lowRankPredictor` at `3/4`).  This proves the counting reduction, not the decay arithmetic.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0FiberCount

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0ChernoffBound (term_mono)

variable {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}

/-- **The pattern-fiber cardinality (PROVED).**  The tuples `g` whose correctness pattern is exactly `p`
(`pred (g i) = p i` for all `i`) number `a^{#trues p} · b^{#falses p}`, where `a = #{x | pred x}` and `b = #{x | ¬pred x}`.
Each coordinate with `p i = true` must land in the `a`-element correct set, each with `p i = false` in the `b`-element
wrong set (`Fintype.card_piFinset`), giving the product `∏_i (if p i then a else b) = a^{#trues}·b^{#falses}`. -/
theorem fiber_card (pred : α → Bool) (p : Fin k → Bool) :
    (Finset.univ.filter (fun g : Fin k → α => (fun i => pred (g i)) = p)).card
      = (Finset.univ.filter (fun x => pred x = true)).card
          ^ (Finset.univ.filter (fun i => p i = true)).card
        * (Finset.univ.filter (fun x => pred x = false)).card
          ^ (Finset.univ.filter (fun i => ¬ p i = true)).card := by
  rw [show (Finset.univ.filter (fun g : Fin k → α => (fun i => pred (g i)) = p))
        = Fintype.piFinset (fun i => Finset.univ.filter (fun x => pred x = p i)) by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, funext_iff]]
  rw [Fintype.card_piFinset]
  rw [show (∏ i : Fin k, (Finset.univ.filter (fun x => pred x = p i)).card)
        = ∏ i : Fin k, (if p i = true then (Finset.univ.filter (fun x => pred x = true)).card
            else (Finset.univ.filter (fun x => pred x = false)).card) by
      refine Finset.prod_congr rfl (fun i _ => ?_)
      cases hpi : p i <;> simp]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]

/-- **The fiber-count reduction (PROVED).**  The number of `k`-tuples of supply approximants whose majority errs at the
input (`#{i | pred (g i)} ≤ m`) is `≤ 2^k · a^m · b^{k−m}` — the per-input Chernoff bound.  Proof: partition the bad
tuples by correctness pattern (`Finset.card_eq_sum_card_fiberwise`); each fiber is `≤ a^m·b^{k−m}` (`fiber_card`, then
`term_mono` since a bad pattern has `#trues ≤ m`); and there are `≤ 2^k` patterns. -/
theorem bad_tuple_count_le (pred : α → Bool) {m : ℕ}
    (hba : (Finset.univ.filter (fun x => pred x = false)).card
            ≤ (Finset.univ.filter (fun x => pred x = true)).card)
    (hmk : m ≤ k) :
    (Finset.univ.filter (fun g : Fin k → α =>
        (Finset.univ.filter (fun i => pred (g i) = true)).card ≤ m)).card
      ≤ 2 ^ k * ((Finset.univ.filter (fun x => pred x = true)).card ^ m
          * (Finset.univ.filter (fun x => pred x = false)).card ^ (k - m)) := by
  set a := (Finset.univ.filter (fun x => pred x = true)).card
  set b := (Finset.univ.filter (fun x => pred x = false)).card
  set t := Finset.univ.filter (fun p : Fin k → Bool =>
      (Finset.univ.filter (fun i => p i = true)).card ≤ m) with ht
  -- partition the bad tuples by their correctness pattern
  rw [Finset.card_eq_sum_card_fiberwise
      (f := fun g : Fin k → α => (fun i => pred (g i))) (t := t)
      (by intro g hg
          simp only [ht, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
          simpa using hg)]
  calc ∑ p ∈ t, (Finset.univ.filter (fun g : Fin k → α =>
          (Finset.univ.filter (fun i => pred (g i) = true)).card ≤ m) |>.filter
            (fun g => (fun i => pred (g i)) = p)).card
      ≤ ∑ _p ∈ t, (a ^ m * b ^ (k - m)) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        rw [ht, Finset.mem_filter] at hp
        have hft : (Finset.univ.filter (fun i => ¬ p i = true)).card
            = k - (Finset.univ.filter (fun i => p i = true)).card := by
          have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
            (p := fun i => p i = true)
          rw [Finset.card_univ, Fintype.card_fin] at this; omega
        calc (Finset.univ.filter (fun g : Fin k → α =>
                (Finset.univ.filter (fun i => pred (g i) = true)).card ≤ m) |>.filter
                (fun g => (fun i => pred (g i)) = p)).card
            ≤ (Finset.univ.filter (fun g : Fin k → α => (fun i => pred (g i)) = p)).card :=
              Finset.card_le_card (fun g hg =>
                Finset.mem_filter.mpr ⟨Finset.mem_univ g, (Finset.mem_filter.mp hg).2⟩)
          _ = a ^ (Finset.univ.filter (fun i => p i = true)).card
                * b ^ (Finset.univ.filter (fun i => ¬ p i = true)).card := fiber_card pred p
          _ ≤ a ^ m * b ^ (k - m) := by rw [hft]; exact term_mono hba hp.2 hmk
    _ = t.card * (a ^ m * b ^ (k - m)) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 ^ k * (a ^ m * b ^ (k - m)) := by
        refine Nat.mul_le_mul_right _ (le_trans (Finset.card_filter_le _ _) ?_)
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

end PallLean.Paper93.DeepMath.PathB.ACC0FiberCount

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FiberCount.fiber_card
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FiberCount.bad_tuple_count_le
