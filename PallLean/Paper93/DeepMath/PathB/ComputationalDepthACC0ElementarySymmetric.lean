import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SymLayerReduction

/-!
# The `e_d`-sparsity identity — each binomial moment is a sparse sum over `d`-subsets

The binomial-moment ↔ level-count bridge (`…ACC0LevelCounts`) reduces the level-counts `N_t` to the moments
`B_d = ∑_x C(andCount x, d)`.  This file proves the last link making each `B_d` a *sparse cube-sum* the kernel computes:
for `0/1` values the binomial coefficient of the sum is the elementary symmetric polynomial,

```
C(∑_j b_j, d)  =  Σ_{T : |T| = d}  ∏_{j ∈ T} b_j          (b_j ∈ {0,1}).
```

Applied to the `AND`-indicators `b_j = [AND_j(x)]`, the moment integrand `C(andCount x, d)` is a sum over the `d`-subsets
`T` of the products `∏_{j∈T} [AND_j(x)]` — and each such product is itself a monomial-`AND` indicator (of the union of
supports), so the sparse-counting kernel computes it.

## What is proved (clean axioms, no `sorry`)

* **`boolean_esymm`** — `C(∑_j b_j, d) = Σ_{|T|=d} ∏_{j∈T} b_j` for `b : Fin k → ℕ` with every `b_j ≤ 1`.
* **`andCount_choose_eq`** — the moment integrand as a sparse `d`-subset sum:
  `C(andCount gates x, d) = Σ_{|T|=d} ∏_{j∈T} [AND_j(x)]`.

## Honest scope

This is the elementary-symmetric identity that turns each binomial moment into a sum over `d`-subsets — making the
moments literally kernel-computable.  Combined with `…ACC0LevelCounts` it reduces the `N_t` to computable data; the
explicit binomial inversion and the Beigel–Tarui `#monomials` bound remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ElementarySymmetric

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0SymLayerReduction

variable {k n : ℕ}

/-- **The `0/1` elementary-symmetric identity (proved): `C(∑_j b_j, d) = Σ_{|T|=d} ∏_{j∈T} b_j`.** -/
theorem boolean_esymm (b : Fin k → ℕ) (hb : ∀ j, b j ≤ 1) (d : ℕ) :
    (∑ j, b j).choose d = ∑ T ∈ Finset.powersetCard d Finset.univ, ∏ j ∈ T, b j := by
  set S : Finset (Fin k) := Finset.univ.filter (fun j => b j = 1) with hS
  have hsum : (∑ j, b j) = S.card := by
    rw [hS, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : b j = 1
    · rw [if_pos h]; exact h
    · have hbj := hb j; rw [if_neg h]; omega
  have hprod : ∀ T : Finset (Fin k), (∏ j ∈ T, b j) = if T ⊆ S then 1 else 0 := by
    intro T
    by_cases hT : T ⊆ S
    · rw [if_pos hT]
      apply Finset.prod_eq_one
      intro j hj
      have hjS : j ∈ S := hT hj
      rw [hS, Finset.mem_filter] at hjS
      exact hjS.2
    · rw [if_neg hT]
      rw [Finset.not_subset] at hT
      obtain ⟨j, hjT, hjS⟩ := hT
      apply Finset.prod_eq_zero hjT
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hjS
      have := hb j
      omega
  have hfilter : (Finset.powersetCard d Finset.univ).filter (· ⊆ S) = Finset.powersetCard d S := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    tauto
  rw [hsum, Finset.sum_congr rfl (fun T _ => hprod T), ← Finset.card_filter, hfilter,
    Finset.card_powersetCard]

/-- **The moment integrand as a sparse `d`-subset sum (proved).** -/
theorem andCount_choose_eq (gates : Fin k → Finset (Fin n)) (x : Fin n → Bool) (d : ℕ) :
    (andCount gates x).choose d
      = ∑ T ∈ Finset.powersetCard d Finset.univ,
          ∏ j ∈ T, (if monoAND (gates j) x = true then 1 else 0) :=
  boolean_esymm (fun j => if monoAND (gates j) x = true then 1 else 0)
    (fun j => by by_cases h : monoAND (gates j) x = true <;> simp [h]) d

end PallLean.Paper93.DeepMath.PathB.ACC0ElementarySymmetric

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ElementarySymmetric.boolean_esymm
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ElementarySymmetric.andCount_choose_eq
