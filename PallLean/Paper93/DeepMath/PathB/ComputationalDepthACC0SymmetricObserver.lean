import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ResidueObserver

/-!
# The symmetric-top count observer: the tractable heart of the Yao–Beigel–Tarui normal form

Yao–Beigel–Tarui says every `ACC⁰` circuit equals a depth-2 **`SYM ∘ AND`** circuit — a *symmetric* output gate over
(quasipolynomially many) bounded-fan-in `AND` gates.  The full reduction is the deep structural theorem and is **not**
proved here (it is the open `ACC⁰` wall, socketed as `MixedACCDepthReductionSocket`).  What this file proves is the
**reason the `SYM` top is cheap**: a symmetric function of `m` sub-gates depends only on the *count* of accepting
sub-gates, so it is `ObservedBy` that count — a statistic with `≤ m+1` cells, instead of the `2^m` of an arbitrary top.

So a `SYM ∘ (m gates)` circuit is SAT-searchable in `≤ m+1` cells (`< 2^n` whenever `m+1 < 2^n`).  Instantiated at the
YBT normal form (`m = 2^{polylog n}` gates), `m+1 < 2^n` — the count boundary is what makes the YBT target tractable in
the cell/observer model.  This holds for *arbitrary* sub-gates `g`; the YBT-specific content (the `g` are bounded `AND`s
and `m` is quasipolynomial) only fixes the value of `m`.

## What is proved (clean axioms, no `sorry`)

* `gateCount` / `symEval` — the count of accepting sub-gates, and a symmetric (count-)function of them.
* `gateCount_le` — the count is `≤ m`, so its image lies in `{0,…,m}`.
* `sym_observed` — `symEval g h` is `ObservedBy` the count statistic.
* `sym_count_card_le` — the count statistic has `≤ m+1` cells.
* `sym_searchable` — `SYM ∘ (m gates)` is SAT-searchable in `< 2^n` cells once `m+1 < 2^n`.

## Honest scope

This is the `SYM`-top **observer** (the cheap, count-boundary half of YBT), valid for any sub-gates.  The deep
direction — that an *arbitrary* `ACC⁰` circuit actually reduces to a `SYM ∘ AND` form with `m` quasipolynomial — is the
Yao–Beigel–Tarui reduction itself, which I do **not** formalize: it remains the open structural wall.  And, as
throughout, a small cell count is not a uniform poly-time algorithm.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver

variable {n m : ℕ}

/-- The number of sub-gates accepting the input. -/
def gateCount (g : Fin m → (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  ∑ j : Fin m, (if g j x then 1 else 0)

/-- A **symmetric** function of `m` sub-gates: it depends only on the count of accepting sub-gates. -/
def symEval (g : Fin m → (Fin n → Bool) → Bool) (h : ℕ → Bool) (x : Fin n → Bool) : Bool :=
  h (gateCount g x)

/-- **The accepting-sub-gate count is `≤ m` (proved).** -/
theorem gateCount_le (g : Fin m → (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    gateCount g x ≤ m := by
  unfold gateCount
  calc ∑ j : Fin m, (if g j x then 1 else 0)
      ≤ ∑ _j : Fin m, 1 := Finset.sum_le_sum (fun j _ => by split <;> simp)
    _ = m := by simp

/-- **A symmetric function is observed by the accepting-sub-gate count (proved).** -/
theorem sym_observed (g : Fin m → (Fin n → Bool) → Bool) (h : ℕ → Bool) :
    ObservedBy (symEval g h) (gateCount g) :=
  ⟨h, fun _ => rfl⟩

/-- **The count statistic has `≤ m+1` cells (proved): the symmetric top collapses the boundary from `2^m` to `m+1`.** -/
theorem sym_count_card_le (g : Fin m → (Fin n → Bool) → Bool) :
    (Finset.univ.image (gateCount g)).card ≤ m + 1 := by
  calc (Finset.univ.image (gateCount g)).card
      ≤ (Finset.range (m + 1)).card := by
        apply Finset.card_le_card
        rw [Finset.image_subset_iff]
        intro x _
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le (gateCount_le g x)
    _ = m + 1 := Finset.card_range (m + 1)

/-- **A `SYM ∘ (m gates)` circuit is SAT-searchable below brute force (proved): its count boundary has `≤ m+1` cells,
`< 2^n` once `m+1 < 2^n`.**  Instantiated at the YBT normal form (`m` quasipolynomial), this is `< 2^n` — the count
boundary is the tractable heart of the YBT target.  (The YBT *reduction* itself is not proved; see the scope note.) -/
theorem sym_searchable (g : Fin m → (Fin n → Bool) → Bool) (h : ℕ → Bool) (hreg : m + 1 < 2 ^ n) :
    (Satisfiable (symEval g h) ↔ ∃ c ∈ Finset.univ.image (gateCount g), h c = true)
      ∧ (Finset.univ.image (gateCount g)).card < 2 ^ n := by
  refine ⟨observed_sat_iff h (fun _ => rfl), ?_⟩
  exact lt_of_le_of_lt (sym_count_card_le g) hreg

end PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver.sym_observed
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver.sym_searchable
