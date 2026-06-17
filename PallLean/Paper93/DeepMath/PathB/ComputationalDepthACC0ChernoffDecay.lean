import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0FiberCount

/-!
# The decay arithmetic — the per-input concentration over a `3/4` supply, fully assembled (proved)

Entry 210 proved the fiber-count reduction: over a supply with `a` correct and `b` wrong approximants at a fixed input,
the bad-tuple count is `≤ 2^k·a^m·b^{k−m}`.  This file proves the **decay arithmetic** that drives that bound below the
`2^{-n}` fraction needed for the union bound, and *assembles the full per-input concentration*: for a `3/4` supply
(`a = 3b`) and `k = 2j` with `j = Ω(n)`, `2^n · #{bad tuples} < #tuples`.

The decay reduces (cancelling the common `b` and `4^j` factors) to the clean `Nat` inequality `2^n·3^j < 4^j` for
`j ≥ 3n+1` — proved by splitting at `j = 3n`: `2^n·3^{3n} = 54^n ≤ 64^n = 4^{3n}` and `3^{j−3n} < 4^{j−3n}` (the strict
factor).  So `2^n · 12^j < 16^j`, i.e. `2^n · (2^{2j}·(3b)^j·b^j) < (4b)^{2j}` — exactly `#inputs · M < #tuples`.

## What is proved (clean axioms, no `sorry`)

* **`decay_core`** — the heart: `2^n · 3^j < 4^j` for `j ≥ 3n+1`.
* **`decay_full`** — the per-input decay bound: `2^n · (2^{2j}·(3b)^j·b^{2j−j}) < (3b+b)^{2j}` for `b ≥ 1`, `j ≥ 3n+1` —
  i.e. `#inputs · (the entry-210 bound) < #tuples`.
* **`chernoff_per_input`** — the full assembly: for a `3/4` supply (`#correct = 3·#wrong`, `#wrong ≥ 1`) and `k = 2j`,
  `j ≥ 3n+1`, the bad-tuple count satisfies `2^n · #{g | majority errs} < #tuples` — the per-input concentration,
  combining entry-210's `bad_tuple_count_le` with `decay_full`.

## Honest scope

This proves the **decay arithmetic** and **assembles the full per-input concentration** `2^n · #{bad tuples} < #tuples`
over a `3/4` supply at `k = 2j = Θ(n)` (`j ≥ 3n+1`) — completely, in pure `Nat` arithmetic, combining entries 209
(`term_mono`), 210 (`bad_tuple_count_le`), and this decay.  This is exactly the per-input bound the (corrected,
supply-restricted) `ChernoffPerInput` socket of entry 208 requires.  What remains — the *last* residual of the entire
BT depth-collapse — is the **construction of a `3/4` supply**: that the RS approximants (`acc0_approx_by_lowRankPredictor`,
which gives `3/4` agreement *globally*) can be arranged as a supply with `≥3/4` correct *at every input* (the
per-input vs. global agreement, and pooling enough approximants).  This proves the concentration over an *assumed* `3/4`
supply, not the existence of the supply.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ChernoffDecay

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0FiberCount (bad_tuple_count_le)

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The decay heart (PROVED).**  `2^n · 3^j < 4^j` for `j ≥ 3n+1`.  Split at `j = 3n`: `2^n·3^{3n} = 54^n ≤ 64^n =
4^{3n}` (`Nat.pow_le_pow_left`, `54 ≤ 64`) and `3^{j−3n} < 4^{j−3n}` (`Nat.pow_lt_pow_left`, the strict factor since
`j−3n ≥ 1`). -/
theorem decay_core (n j : ℕ) (hj : 3 * n + 1 ≤ j) : 2 ^ n * 3 ^ j < 4 ^ j := by
  have e3 : (3 : ℕ) ^ j = 3 ^ (3 * n) * 3 ^ (j - 3 * n) := by rw [← pow_add]; congr 1; omega
  have e4 : (4 : ℕ) ^ j = 4 ^ (3 * n) * 4 ^ (j - 3 * n) := by rw [← pow_add]; congr 1; omega
  rw [e3, e4, show (3 : ℕ) ^ (3 * n) = 27 ^ n by rw [pow_mul]; norm_num,
      show (4 : ℕ) ^ (3 * n) = 64 ^ n by rw [pow_mul]; norm_num,
      show 2 ^ n * (27 ^ n * 3 ^ (j - 3 * n)) = (2 * 27) ^ n * 3 ^ (j - 3 * n) by rw [mul_pow]; ring]
  calc (2 * 27) ^ n * 3 ^ (j - 3 * n)
      ≤ 64 ^ n * 3 ^ (j - 3 * n) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) n)
    _ < 64 ^ n * 4 ^ (j - 3 * n) :=
        (Nat.mul_lt_mul_left (pow_pos (by norm_num : (0 : ℕ) < 64) n)).mpr
          (Nat.pow_lt_pow_left (by norm_num) (by omega))

/-- **The per-input decay bound (PROVED).**  `2^n · (2^{2j}·(3b)^j·b^{2j−j}) < (3b+b)^{2j}` for `b ≥ 1`, `j ≥ 3n+1` —
i.e. `#inputs · (the entry-210 per-input bound, at `a = 3b`, `k = 2j`, `m = j`) < #tuples`.  Reduces to `decay_core` by
factoring out the common `4^j·b^{2j}` and cancelling it (`Nat.mul_lt_mul_right`). -/
theorem decay_full (n j b : ℕ) (hb : 1 ≤ b) (hj : 3 * n + 1 ≤ j) :
    2 ^ n * (2 ^ (2 * j) * (3 * b) ^ j * b ^ (2 * j - j)) < (3 * b + b) ^ (2 * j) := by
  have hkm : 2 * j - j = j := by omega
  rw [hkm]
  have hX : 0 < 4 ^ j * b ^ (2 * j) := Nat.mul_pos (pow_pos (by norm_num) j) (pow_pos (by omega) _)
  rw [show 2 ^ n * (2 ^ (2 * j) * (3 * b) ^ j * b ^ j)
        = (2 ^ n * 3 ^ j) * (4 ^ j * b ^ (2 * j)) by
        rw [show (2 : ℕ) ^ (2 * j) = 4 ^ j by rw [pow_mul]; norm_num, mul_pow,
            show (2 : ℕ) * j = j + j by ring, pow_add]; ring,
      show (3 * b + b) ^ (2 * j) = 4 ^ j * (4 ^ j * b ^ (2 * j)) by
        rw [show 3 * b + b = 4 * b by ring, mul_pow,
            show (4 : ℕ) ^ (2 * j) = 4 ^ j * 4 ^ j by rw [← pow_add]; congr 1; ring]; ring]
  exact (Nat.mul_lt_mul_right hX).mpr (decay_core n j hj)

/-- **The full per-input concentration over a `3/4` supply (PROVED).**  For a supply where `#correct = 3·#wrong`
(`≥3/4` correct) with `#wrong ≥ 1`, and `k = 2j` with `j ≥ 3n+1`, the number of `k`-tuples whose majority errs
(`#correct ≤ j`) satisfies `2^n · #{bad} < #tuples = (#correct+#wrong)^{2j}` — the per-input concentration (`#inputs ·
#{bad} < #tuples`).  Assembles entry-210's `bad_tuple_count_le` (`#{bad} ≤ 2^{2j}·(3b)^j·b^j`) with `decay_full`. -/
theorem chernoff_per_input (pred : α → Bool) (n j : ℕ)
    (h34 : (Finset.univ.filter (fun x => pred x = true)).card
            = 3 * (Finset.univ.filter (fun x => pred x = false)).card)
    (hb : 1 ≤ (Finset.univ.filter (fun x => pred x = false)).card)
    (hj : 3 * n + 1 ≤ j) :
    2 ^ n * (Finset.univ.filter (fun g : Fin (2 * j) → α =>
        (Finset.univ.filter (fun i => pred (g i) = true)).card ≤ j)).card
      < ((Finset.univ.filter (fun x => pred x = true)).card
          + (Finset.univ.filter (fun x => pred x = false)).card) ^ (2 * j) := by
  set b := (Finset.univ.filter (fun x => pred x = false)).card
  have hbound := bad_tuple_count_le (k := 2 * j) pred (m := j)
    (by rw [h34]; omega) (by omega)
  rw [h34, ← mul_assoc] at hbound
  rw [h34]
  calc 2 ^ n * (Finset.univ.filter (fun g : Fin (2 * j) → α =>
          (Finset.univ.filter (fun i => pred (g i) = true)).card ≤ j)).card
      ≤ 2 ^ n * (2 ^ (2 * j) * (3 * b) ^ j * b ^ (2 * j - j)) := Nat.mul_le_mul_left _ hbound
    _ < (3 * b + b) ^ (2 * j) := decay_full n j b hb hj

end PallLean.Paper93.DeepMath.PathB.ACC0ChernoffDecay

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ChernoffDecay.decay_core
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ChernoffDecay.decay_full
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ChernoffDecay.chernoff_per_input
