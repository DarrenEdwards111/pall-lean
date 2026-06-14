import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SymmetricObserver

/-!
# The symmetric-count exact trick: `AND`/`OR` are *exactly* symmetric, no approximation

The Razborov–Smolensky polynomial only *approximates* an `AND`/`OR` gate (`1-ε` agreement).  The Beigel–Tarui exact
trick replaces approximation by the observation that an `AND`/`OR` gate is **exactly** a symmetric (count) function of
its inputs:

```
AND of m gates  =  [ count of accepting gates = m ]        (exact)
OR  of m gates  =  [ count of accepting gates ≥ 1 ]        (exact)
```

No error term: the exactness comes from the `SYM` top reading the **exact** count (`gateCount`).  So a single
unbounded-fan-in `AND`/`OR` gate *is* a `SYM` gate over its inputs, observed by the count, searchable in `≤ m+1` cells —
**exactly**, closing the approximate/exact gap at the gate level.

## What is proved (clean axioms, no `sorry`)

* `gateCount_eq_card_iff` — `gateCount g x = m ↔ ∀ j, gⱼ x` (the count hits `m` iff every gate accepts: `AND`).
* `gateCount_pos_iff` — `1 ≤ gateCount g x ↔ ∃ j, gⱼ x` (the count is positive iff some gate accepts: `OR`).
* `and_exact_sym` / `or_exact_sym` — `AND`/`OR` over `m` gates equal `symEval` with `h = [·=m]` / `[1≤·]` (EXACT).
* `and_exact_searchable` / `or_exact_searchable` — hence SAT-searchable in `≤ m+1` cells, exactly.

## Honest scope

This is the exact trick at the **single-gate** level: `AND`/`OR`/`MOD` need *no* approximation — they are exactly
symmetric count functions.  What remains for full YBT is composing these exact symmetric representations **across
constant depth** while keeping the gate count quasipolynomial (the structural composition).  This file removes the
approximation from the *gates*; the depth composition is the remaining structural step.  Still the cell/observer model;
nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SymmetricExact

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver

variable {n m : ℕ}

/-- **`AND` is exactly the count hitting `m` (proved): `gateCount g x = m ↔ every gate accepts`.** -/
theorem gateCount_eq_card_iff (g : Fin m → (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    gateCount g x = m ↔ ∀ j, g j x = true := by
  unfold gateCount
  constructor
  · intro h j
    by_contra hj
    have hjf : g j x = false := by simpa using hj
    have hlt : (∑ k : Fin m, (if g k x then 1 else 0)) < ∑ _k : Fin m, (1 : ℕ) :=
      Finset.sum_lt_sum (fun k _ => by split <;> simp) ⟨j, Finset.mem_univ j, by rw [hjf]; simp⟩
    rw [h] at hlt
    simp at hlt
  · intro h
    simp [h]

/-- **`OR` is exactly the count being positive (proved): `1 ≤ gateCount g x ↔ some gate accepts`.** -/
theorem gateCount_pos_iff (g : Fin m → (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    1 ≤ gateCount g x ↔ ∃ j, g j x = true := by
  rw [Nat.one_le_iff_ne_zero]
  unfold gateCount
  rw [ne_eq, Finset.sum_eq_zero_iff]
  push_neg
  refine exists_congr (fun j => ?_)
  simp only [Finset.mem_univ, true_and]
  cases hg : g j x <;> simp

/-- **`AND` over `m` gates is *exactly* a `SYM` (count) gate (proved): `[∀ j, gⱼ] = symEval g [·=m]`.** -/
theorem and_exact_sym (g : Fin m → (Fin n → Bool) → Bool) :
    (fun x => decide (∀ j, g j x = true)) = symEval g (fun k => decide (k = m)) := by
  funext x
  show decide (∀ j, g j x = true) = decide (gateCount g x = m)
  rw [decide_eq_decide]
  exact (gateCount_eq_card_iff g x).symm

/-- **`OR` over `m` gates is *exactly* a `SYM` (count) gate (proved): `[∃ j, gⱼ] = symEval g [1≤·]`.** -/
theorem or_exact_sym (g : Fin m → (Fin n → Bool) → Bool) :
    (fun x => decide (∃ j, g j x = true)) = symEval g (fun k => decide (1 ≤ k)) := by
  funext x
  show decide (∃ j, g j x = true) = decide (1 ≤ gateCount g x)
  rw [decide_eq_decide]
  exact (gateCount_pos_iff g x).symm

/-- **An `AND` over `m` gates is SAT-searchable in `< 2^n`, exactly (proved).** -/
theorem and_exact_searchable (g : Fin m → (Fin n → Bool) → Bool) (hreg : m + 1 < 2 ^ n) :
    (Satisfiable (fun x => decide (∀ j, g j x = true)) ↔
        ∃ c ∈ Finset.univ.image (gateCount g), decide (c = m) = true)
      ∧ (Finset.univ.image (gateCount g)).card < 2 ^ n := by
  rw [and_exact_sym]
  exact sym_searchable g (fun k => decide (k = m)) hreg

/-- **An `OR` over `m` gates is SAT-searchable in `< 2^n`, exactly (proved).** -/
theorem or_exact_searchable (g : Fin m → (Fin n → Bool) → Bool) (hreg : m + 1 < 2 ^ n) :
    (Satisfiable (fun x => decide (∃ j, g j x = true)) ↔
        ∃ c ∈ Finset.univ.image (gateCount g), decide (1 ≤ c) = true)
      ∧ (Finset.univ.image (gateCount g)).card < 2 ^ n := by
  rw [or_exact_sym]
  exact sym_searchable g (fun k => decide (1 ≤ k)) hreg

end PallLean.Paper93.DeepMath.PathB.ACC0SymmetricExact

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymmetricExact.and_exact_sym
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymmetricExact.or_exact_sym
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymmetricExact.and_exact_searchable
