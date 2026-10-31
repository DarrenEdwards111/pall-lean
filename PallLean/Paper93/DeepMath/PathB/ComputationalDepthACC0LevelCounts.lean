import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SymLayerReduction

/-!
# Per-level counts from binomial moments — the bridge from computable sums to the `N_t`

The SYM-layer reduction (`…ACC0SymLayerReduction`) collapses `SYM∘AND` SAT/count to the `k+1` level-counts
`N_t = #{x : exactly t AND-gates fire}`.  This file connects those `N_t` to the *computable* sums of the sparse kernel
via the **binomial moments** `B_d = ∑_x C(andCount x, d)`:

```
B_d  =  ∑_{t=0}^{k} N_t · C(t, d)            (the binomial-moment ↔ level-count relation),
∑_{t=0}^{k} N_t  =  2ⁿ                        (the levels partition the cube).
```

The matrix `C(t,d)` is **upper-triangular with unit diagonal** (`C(t,d) = 0` for `t < d`, `C(d,d) = 1`), so the `k+1`
moments `B_0,…,B_k` **determine** the `k+1` level-counts `N_t` by back-substitution / inclusion–exclusion.  And each
`B_d` is a sparse cube-sum (`C(∑_j w_j, d)` is the elementary symmetric `e_d` of the `AND`-indicators, a sum over
`d`-subsets), so the moments are computable by the sparse kernel — hence so are the `N_t`.

## What is proved (clean axioms, no `sorry`)

* **`levelCount_sum`** — `∑_{t≤k} N_t = 2ⁿ` (the levels partition the cube).
* **`binomial_moment_eq_sum_levels`** — `∑_x C(andCount x, d) = ∑_{t≤k} N_t · C(t, d)`: the moment is a triangular
  combination of the level-counts.

## Honest scope

This is the *bridge*: it expresses each (kernel-computable) binomial moment as the triangular combination
`∑_t N_t·C(t,d)` of the level-counts, so the `N_t` are recoverable from the moments by the standard inclusion–exclusion
inversion of a unit-triangular system.  The explicit inversion `N_t = ∑_d (-1)^{d-t} C(d,t) B_d` and the
`e_d`-as-sparse-cube-sum identity (`C(∑ w_j, d) = ∑_{|T|=d} ∏_{j∈T} w_j`) are the remaining algebraic steps; together
with the Beigel–Tarui quasipolynomial `#monomials` bound they would close the counting socket.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0LevelCounts

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0SymLayerReduction

variable {n k : ℕ}

/-- **The levels partition the cube (proved): `∑_{t≤k} N_t = 2ⁿ`.** -/
theorem levelCount_sum (gates : Fin k → Finset (Fin n)) :
    ∑ t ∈ Finset.range (k + 1), levelCount gates t = 2 ^ n := by
  unfold levelCount
  rw [← Finset.card_eq_sum_card_fiberwise
      (fun x (_ : x ∈ (Finset.univ : Finset (Fin n → Bool))) =>
        Finset.mem_range.mpr (Nat.lt_succ_of_le (andCount_le gates x)))]
  rw [Finset.card_univ, Fintype.card_pi]
  simp

/-- **The binomial-moment ↔ level-count relation (proved): `∑_x C(andCount x, d) = ∑_{t≤k} N_t · C(t, d)`.**  The
moment is the triangular combination of the level-counts; since `C(t,d)` is unit-upper-triangular in `(t,d)`, the `k+1`
moments determine the `k+1` level-counts. -/
theorem binomial_moment_eq_sum_levels (gates : Fin k → Finset (Fin n)) (d : ℕ) :
    (∑ x : Fin n → Bool, (andCount gates x).choose d)
      = ∑ t ∈ Finset.range (k + 1), levelCount gates t * t.choose d := by
  rw [← Finset.sum_fiberwise_of_maps_to
      (g := andCount gates) (t := Finset.range (k + 1))
      (fun x (_ : x ∈ (Finset.univ : Finset (Fin n → Bool))) =>
        Finset.mem_range.mpr (Nat.lt_succ_of_le (andCount_le gates x)))
      (fun x => (andCount gates x).choose d)]
  apply Finset.sum_congr rfl
  intro t _
  have hconst : ∀ x ∈ Finset.univ.filter (fun x : Fin n → Bool => andCount gates x = t),
      (andCount gates x).choose d = t.choose d :=
    fun x hx => by rw [(Finset.mem_filter.mp hx).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
  rfl

end PallLean.Paper93.DeepMath.PathB.ACC0LevelCounts

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LevelCounts.levelCount_sum
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LevelCounts.binomial_moment_eq_sum_levels
