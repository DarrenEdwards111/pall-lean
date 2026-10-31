import Mathlib

/-!
# The combinatorial Chernoff bound — the binomial-tail inequality (proved)

Entry 208 reduced `MajorityGoodFamily` to a per-input concentration socket `ChernoffPerInput`.  **Correction (honest):**
entry 208 stated that socket over *all* `k`-tuples of *all* Boolean functions, where it is in fact **false** — over the
uniform all-functions space each approximant is correct with probability exactly `1/2`, so the majority errs with
probability `≈ 1/2`, not `< 2^{-n}`.  The genuine concentration must be taken over a **supply of `≥3/4`-correct
approximants** (the RS-distribution support).  This file proves the genuine analytic heart of that concentration — the
**combinatorial Chernoff bound** (the binomial-tail inequality) — *directly, without measure theory*.

The bound.  For a draw of `k` independent coordinates, each landing in the "correct" part (size `a`) versus the "wrong"
part (size `b`) with `b ≤ a`, the number of outcomes with at most `m` correct coordinates is the binomial tail
`∑_{j≤m} C(k,j)·a^j·b^{k−j}`, and this is `≤ 2^k·a^m·b^{k−m}` (`binomial_tail_le`).  In the `3/4` regime (`a ≥ 3b`, the
threshold `m ≈ k/2`) this is `exp(−Ω(k))` of the total `(a+b)^k` — the Chernoff decay — so for `k = Ω(n)` the per-input
bad fraction drops below `2^{-n}`.

## What is proved (clean axioms, no `sorry`)

* **`term_mono`** — the term monotonicity: for `j ≤ m ≤ k` and `b ≤ a`, `a^j·b^{k−j} ≤ a^m·b^{k−m}` (the heaviest tail
  term dominates).
* **`binomial_tail_le`** — the combinatorial Chernoff bound: `∑_{j≤m} C(k,j)·a^j·b^{k−j} ≤ 2^k·a^m·b^{k−m}` (every tail
  term `≤` the top term, and `∑_{j≤m} C(k,j) ≤ ∑_{j≤k} C(k,j) = 2^k`).

## Honest scope

This proves the genuine **combinatorial Chernoff bound** — the binomial-tail inequality that is the analytic heart of
the per-input concentration — completely and *without any probability/measure infrastructure* (pure `Nat` arithmetic +
`Nat.sum_range_choose`).  It also documents the **correction** to entry 208: the concentration holds over a `≥3/4`
*supply*, not all functions.  What this file does **not** do: (i) the *fiber-counting reduction* — that the number of
bad approximant-tuples at a fixed input equals the binomial tail `∑ C(k,j)·a^j·b^{k−j}` (a standard but unformalised
multinomial count); (ii) the *decay-to-`2^{-n}`* step — choosing `k = Ω(n)` so `2^k·a^m·b^{k−m} · 2^n < (a+b)^k` (the
`exp(−Ω(k))` arithmetic in the `3/4` regime).  These remain the plumbing connecting this bound to the corrected
`ChernoffPerInput`-over-supply.  This proves the Chernoff *inequality*, not the full per-input concentration statement.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ChernoffBound

open Finset

/-- **Tail-term monotonicity (PROVED).**  For `j ≤ m ≤ k` and `b ≤ a`, `a^j·b^{k−j} ≤ a^m·b^{k−m}`: moving weight from
the (smaller) `b`-part to the (larger) `a`-part increases the term, so among `j ≤ m` the term at `m` is heaviest.
Proof: `b^{k−j} = b^{k−m}·b^{m−j}` (as `k−j = (k−m)+(m−j)`), and `b^{m−j} ≤ a^{m−j}` (`Nat.pow_le_pow_left`). -/
theorem term_mono {a b j m k : ℕ} (hba : b ≤ a) (hjm : j ≤ m) (hmk : m ≤ k) :
    a ^ j * b ^ (k - j) ≤ a ^ m * b ^ (k - m) := by
  have e1 : k - j = (k - m) + (m - j) := by omega
  calc a ^ j * b ^ (k - j)
      = a ^ j * (b ^ (k - m) * b ^ (m - j)) := by rw [e1, pow_add]
    _ ≤ a ^ j * (b ^ (k - m) * a ^ (m - j)) := by
        apply Nat.mul_le_mul_left
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_left hba _
    _ = a ^ m * b ^ (k - m) := by
        rw [show a ^ j * (b ^ (k - m) * a ^ (m - j)) = a ^ (j + (m - j)) * b ^ (k - m) by
              rw [pow_add]; ring,
            show j + (m - j) = m from by omega]

/-- **The combinatorial Chernoff bound (PROVED).**  The binomial tail `∑_{j≤m} C(k,j)·a^j·b^{k−j}` is `≤
2^k·a^m·b^{k−m}`: each tail term is `≤` the top term (`term_mono`), and `∑_{j≤m} C(k,j) ≤ ∑_{j≤k} C(k,j) = 2^k`
(`Nat.sum_range_choose`).  In the `3/4` regime (`a ≥ 3b`, `m ≈ k/2`) the right side is `exp(−Ω(k))` of the total
`(a+b)^k` — the Chernoff concentration. -/
theorem binomial_tail_le {a b m k : ℕ} (hba : b ≤ a) (hmk : m ≤ k) :
    ∑ j ∈ Finset.range (m + 1), k.choose j * (a ^ j * b ^ (k - j))
      ≤ 2 ^ k * (a ^ m * b ^ (k - m)) := by
  calc ∑ j ∈ Finset.range (m + 1), k.choose j * (a ^ j * b ^ (k - j))
      ≤ ∑ j ∈ Finset.range (m + 1), k.choose j * (a ^ m * b ^ (k - m)) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.mem_range, Nat.lt_succ_iff] at hj
        exact Nat.mul_le_mul_left _ (term_mono hba hj hmk)
    _ = (∑ j ∈ Finset.range (m + 1), k.choose j) * (a ^ m * b ^ (k - m)) := by rw [Finset.sum_mul]
    _ ≤ 2 ^ k * (a ^ m * b ^ (k - m)) := by
        apply Nat.mul_le_mul_right
        calc ∑ j ∈ Finset.range (m + 1), k.choose j
            ≤ ∑ j ∈ Finset.range (k + 1), k.choose j :=
              Finset.sum_le_sum_of_subset (by intro j hj; rw [Finset.mem_range] at *; omega)
          _ = 2 ^ k := by rw [← Nat.sum_range_choose]

end PallLean.Paper93.DeepMath.PathB.ACC0ChernoffBound

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ChernoffBound.term_mono
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ChernoffBound.binomial_tail_le
