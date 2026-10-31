import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CarrySparseTheory

/-!
# Route 1 — the count carry is symmetric: `⌊s/p⌋` as a sum of threshold gates

The carry structure theory (`…ACC0CarrySparseTheory`) showed the general carry `⌊(a+b)/p⌋` is *not* a function of the
down-shifts `⌊a/p⌋, ⌊b/p⌋` — it needs the low residues.  But in the `ACC⁰` setting the argument of every `MOD` gate is a
single **count** `s = ∑ᵢ xᵢ`, and the tower it is down-shifted along (`s, ⌊s/p⌋, ⌊s/p²⌋, …`) consists of functions of
that *one* `s`.  So the residue-coupling obstruction of the general `a+b` carry is an artifact of summing two
independently-varying parts; for a single count it dissolves.  This file proves the resulting **symmetric structure** of
the count carry.

* **The count carry is symmetric.**  `⌊s/p^i⌋` depends only on the count `s = ∑ᵢ xᵢ` — equal-weight inputs give equal
  carries.  Every level of the `p`-adic tower is a symmetric Boolean function, and (via the down-shift decomposition of
  `…ACC0ValuationSparseTheory`) so is `MOD_{p^e}` itself.

* **The count carry is a sum of threshold gates.**  `⌊s/p⌋ = ∑_{j=1}^{N} [s ≥ j·p]` (for `N ≥ ⌊s/p⌋`): the carry is
  the count of multiples of `p` that fit below `s`, i.e. a sum of `⌊n/p⌋` threshold (Majority-flavoured) indicators
  `[s ≥ j·p]`.  This is exactly a `SYM` structure — the carry is a symmetric function expressed as a sum of thresholds.

* **The count carry has small range.**  `⌊s/p⌋ ≤ ⌊n/p⌋` for `s ≤ n`: the carry takes only `⌊n/p⌋+1` values, far fewer
  than the count itself — a low-range symmetric function.

## What is proved (clean axioms, no `sorry`)

* **`count_carry_threshold_card`** — `#{j ∈ [1,N] : j·p ≤ s} = min N ⌊s/p⌋` (the threshold count).
* **`count_carry_eq_sum_thresholds`** — `⌊s/p⌋ = ∑_{j∈[1,N]} [j·p ≤ s]` when `⌊s/p⌋ ≤ N` (carry = sum of thresholds).
* **`count_carry_range_le`** — `⌊s/p⌋ ≤ ⌊n/p⌋` for `s ≤ n` (small range).
* **`count_carry_symmetric`** — equal-weight inputs give equal carry `⌊(∑xₖ)/p^i⌋` (the count carry is symmetric).

## Honest scope

This is the structural *gain* the count gives over the general `a+b` carry: the count carry is genuinely symmetric (a
function of `s` alone), a sum of `⌊n/p⌋` threshold gates of small range — so the `SYM` top-structure the
Beigel–Tarui route wants is present.  But the gain re-localises the difficulty rather than removing it: the thresholds
`[s ≥ j·p]` are Majority-flavoured symmetric functions, and a *low-degree* (polynomial-method) handle on such thresholds
of the count is exactly the hard part — we do **not** prove the thresholds are low-degree (that, composed across the
tower, would be the open `ACC⁰[composite]` representation) nor that they are not.  What is established: the count carry's
symmetric structure is a sum of bounded-range thresholds, isolating the open question to the *degree of a threshold on
the count*.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CountCarrySymmetric

open Finset

/-- **The count carry is a threshold count (proved): `#{j ∈ [1,N] : j·p ≤ s} = min N ⌊s/p⌋`.**  Counting the multiples
`j·p` of `p` that fit below `s` gives the carry `⌊s/p⌋` (capped at `N`), since `j·p ≤ s ↔ j ≤ ⌊s/p⌋`. -/
theorem count_carry_threshold_card (p s N : ℕ) (hp : 0 < p) :
    ((Finset.Icc 1 N).filter (fun j => j * p ≤ s)).card = min N (s / p) := by
  have hset : (Finset.Icc 1 N).filter (fun j => j * p ≤ s) = Finset.Icc 1 (min N (s / p)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, (Nat.le_div_iff_mul_le hp).mpr h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, (Nat.le_div_iff_mul_le hp).mp h3⟩
  rw [hset, Nat.card_Icc, Nat.add_sub_cancel]

/-- **The count carry is a sum of threshold gates (proved): `⌊s/p⌋ = ∑_{j∈[1,N]} [j·p ≤ s]` for `⌊s/p⌋ ≤ N`.**  The
symmetric structure: the carry is a sum of `⌊n/p⌋`-many threshold (Majority-flavoured) indicators `[s ≥ j·p]` — a `SYM`
form, exactly what the Beigel–Tarui route targets. -/
theorem count_carry_eq_sum_thresholds (p s N : ℕ) (hp : 0 < p) (hN : s / p ≤ N) :
    s / p = ∑ j ∈ Finset.Icc 1 N, (if j * p ≤ s then 1 else 0) := by
  rw [Finset.sum_boole, count_carry_threshold_card p s N hp, min_eq_right hN, Nat.cast_id]

/-- **The count carry has small range (proved): `⌊s/p⌋ ≤ ⌊n/p⌋` for `s ≤ n`.**  The carry takes only `⌊n/p⌋+1`
values — a low-range symmetric function, far coarser than the count itself. -/
theorem count_carry_range_le (p s n : ℕ) (h : s ≤ n) : s / p ≤ n / p :=
  Nat.div_le_div_right h

/-- **The count carry is symmetric (proved): it depends only on the count.**  Equal-weight inputs `∑ xₖ = ∑ yₖ` give
equal carries `⌊(∑xₖ)/p^i⌋ = ⌊(∑yₖ)/p^i⌋` at every tower level `i`.  Unlike the general `a+b` carry (which needs the low
residues, `…ACC0CarrySparseTheory.carry_not_function_of_downshifts`), the count carry is a function of the single count
`s` — the residue-coupling obstruction dissolves for one count. -/
theorem count_carry_symmetric {n : ℕ} (x y : Fin n → ℕ) (p i : ℕ)
    (h : ∑ k, x k = ∑ k, y k) : (∑ k, x k) / p ^ i = (∑ k, y k) / p ^ i := by
  rw [h]

end PallLean.Paper93.DeepMath.PathB.ACC0CountCarrySymmetric

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CountCarrySymmetric.count_carry_threshold_card
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CountCarrySymmetric.count_carry_eq_sum_thresholds
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CountCarrySymmetric.count_carry_range_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CountCarrySymmetric.count_carry_symmetric
