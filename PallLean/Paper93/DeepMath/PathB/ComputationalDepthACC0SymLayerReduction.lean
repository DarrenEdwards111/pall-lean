import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SparseCounting

/-!
# The SYM-layer reduction — SYM∘AND SAT/count reduces to the `k+1` AND-layer level-counts

The sparse-counting kernel (`…ACC0SparseCounting`) gives the cube-*sum* of a sparse monomial-`AND` combination.  The
remaining half of Williams' counting socket is the **symmetric top layer**: a `SYM∘AND` circuit is
`sym(∑_j AND_j(x))`, and we must turn the count into a SAT *decision*.

This file proves that reduction.  The AND-layer fires between `0` and `k` gates, so the cube partitions into the `k+1`
**levels** `N_t = #{x : exactly t AND-gates fire}`, and:

```
#SAT(sym ∘ AND)  =  Σ_{t=0}^{k}  [sym t] · N_t,          SAT ⟺ ∃ t ≤ k,  sym t  ∧  N_t ≠ 0.
```

So deciding / counting a `SYM∘AND` over `k` `AND`-gates reduces from the `2ⁿ` cube to the **`k+1` level-counts** —
the symmetric layer collapses the search to `k+1` values.  (Computing each `N_t` is the remaining counting work, fed by
the sparse kernel; the *reduction through the symmetric layer* is what is proved here.)

## What is proved (clean axioms, no `sorry`)

* `andCount` / `symAndEval` / `levelCount` — the firing count, the `SYM∘AND` value, and the level-counts.
* **`andCount_le`** — at most `k` `AND`-gates fire.
* **`symAnd_satCount_eq_sum_levels`** — `#SAT = Σ_{t ≤ k} [sym t] · N_t`.
* **`symAnd_sat_iff`** — `∃x` accepting `⟺ ∃ t ≤ k, sym t ∧ N_t ≠ 0` (the decision over `k+1` levels).

## Honest scope

This is the *reduction* through the symmetric layer — proved.  It collapses `SYM∘AND` SAT to `k+1` level-counts, but
computing the level-counts `N_t` themselves is the remaining counting work (the sparse kernel computes weighted
cube-sums; extracting individual `N_t` and the Beigel–Tarui quasipolynomial `#monomials` bound are the open
algorithmic inputs).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SymLayerReduction

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd

variable {n k : ℕ}

/-- The number of `AND`-gates that fire on `x`. -/
def andCount (gates : Fin k → Finset (Fin n)) (x : Fin n → Bool) : ℕ :=
  ∑ j, (if monoAND (gates j) x = true then 1 else 0)

/-- A `SYM∘AND` circuit: a symmetric top `sym : ℕ → Bool` applied to the `AND`-firing count. -/
def symAndEval (sym : ℕ → Bool) (gates : Fin k → Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  sym (andCount gates x)

/-- The `t`-th level-count: the number of inputs firing exactly `t` `AND`-gates. -/
def levelCount (gates : Fin k → Finset (Fin n)) (t : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Bool => andCount gates x = t)).card

/-- **At most `k` `AND`-gates fire (proved).** -/
theorem andCount_le (gates : Fin k → Finset (Fin n)) (x : Fin n → Bool) : andCount gates x ≤ k := by
  calc andCount gates x ≤ ∑ _j : Fin k, 1 := by
        apply Finset.sum_le_sum
        intro j _
        split <;> simp
    _ = k := by simp

/-- **The SYM-layer count decomposition (proved): `#SAT = Σ_{t ≤ k} [sym t] · N_t`.** -/
theorem symAnd_satCount_eq_sum_levels (sym : ℕ → Bool) (gates : Fin k → Finset (Fin n)) :
    (Finset.univ.filter (fun x : Fin n → Bool => symAndEval sym gates x = true)).card
      = ∑ t ∈ Finset.range (k + 1), (if sym t = true then levelCount gates t else 0) := by
  rw [Finset.card_eq_sum_card_fiberwise
      (f := andCount gates) (t := Finset.range (k + 1))
      (fun x _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (andCount_le gates x)))]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hsym : sym t = true
  · rw [if_pos hsym]
    unfold levelCount
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, symAndEval]
    constructor
    · rintro ⟨_, hc⟩; exact hc
    · intro hc; exact ⟨by rw [hc]; exact hsym, hc⟩
  · rw [if_neg hsym, Finset.card_eq_zero]
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, symAndEval, Finset.notMem_empty,
      iff_false, not_and]
    intro hs hc
    rw [hc] at hs
    exact hsym hs

/-- **The SYM-layer SAT decision (proved): `∃x` accepting `⟺ ∃ t ≤ k, sym t ∧ N_t ≠ 0`.**  Satisfiability of a
`SYM∘AND` over `k` `AND`-gates is decided by the `k+1` level-counts, not the `2ⁿ` cube. -/
theorem symAnd_sat_iff (sym : ℕ → Bool) (gates : Fin k → Finset (Fin n)) :
    (∃ x, symAndEval sym gates x = true)
      ↔ ∃ t ∈ Finset.range (k + 1), sym t = true ∧ levelCount gates t ≠ 0 := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨andCount gates x, Finset.mem_range.mpr (Nat.lt_succ_of_le (andCount_le gates x)), hx, ?_⟩
    intro hzero
    rw [levelCount, Finset.card_eq_zero] at hzero
    have hxmem : x ∈ Finset.univ.filter (fun y : Fin n → Bool => andCount gates y = andCount gates x) := by
      simp
    rw [hzero] at hxmem
    exact absurd hxmem (Finset.notMem_empty x)
  · rintro ⟨t, _, hsym, hlevel⟩
    rw [levelCount, Finset.card_ne_zero] at hlevel
    obtain ⟨x, hx⟩ := hlevel
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact ⟨x, by rw [symAndEval, hx]; exact hsym⟩

end PallLean.Paper93.DeepMath.PathB.ACC0SymLayerReduction

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymLayerReduction.andCount_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymLayerReduction.symAnd_satCount_eq_sum_levels
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymLayerReduction.symAnd_sat_iff
