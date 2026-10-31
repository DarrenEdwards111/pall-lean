import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBoosting
import Mathlib

/-!
# The `{-1,+1}` monomial product law (PROVED) — the degree engine of the boosting surjection

Constructing the boosting surjection (every function on `G` realised at degree `≤ n/2 + d`) needs the product of
two monomials to stay low degree.  Over the `{-1,+1}ⁿ` cube (each `xᵢ² = 1`), monomials multiply by **symmetric
difference**:

  `prod_mul_prod_symmDiff` — `(∏_{i∈A} xᵢ)·(∏_{i∈B} xᵢ) = ∏_{i∈A∆B} xᵢ`  (the `A∩B` factors square to `1`).
  `card_symmDiff_le` — `|A ∆ B| ≤ |A| + |B|`  (the product's degree is at most the sum of degrees).

Together these are the engine: if the approximator `a = Σ_R a_R χ_R` has degree `≤ d` (all `|R| ≤ d`), then
`a · χ_T = Σ_R a_R χ_{R∆T}` has every term of degree `|R∆T| ≤ |R| + |T| ≤ d + |T|`.  Folding a high-degree
monomial `χ_S = χ_univ · χ_{Sᶜ}` and replacing `χ_univ` by `a` thus lands in degree `≤ d + |Sᶜ| ≤ d + n/2` — the
degree bound the dimension count consumes.  This file proves that algebraic engine.
-/

open scoped symmDiff

namespace PallLean.Paper93.DeepMath.PathB.Boosting

variable {R : Type*} [CommMonoid R] {n : ℕ}

/-- **The monomial product law over `{-1,+1}`.**  When every coordinate squares to `1`, the product of the
monomials over `A` and `B` is the monomial over their symmetric difference: the `A ∩ B` coordinates appear twice
and square to `1`. -/
theorem prod_mul_prod_symmDiff (x : Fin n → R) (hx : ∀ i, x i ^ 2 = 1) (A B : Finset (Fin n)) :
    (∏ i ∈ A, x i) * (∏ i ∈ B, x i) = ∏ i ∈ A ∆ B, x i := by
  rw [← Finset.prod_union_inter]
  have hdisj : Disjoint (A ∆ B) (A ∩ B) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_symmDiff, Finset.mem_inter] at hi hi'
    tauto
  have hsplit : ∏ i ∈ A ∪ B, x i = (∏ i ∈ A ∆ B, x i) * ∏ i ∈ A ∩ B, x i := by
    rw [← Finset.prod_union hdisj]
    congr 1
    ext i
    simp only [Finset.mem_union, Finset.mem_symmDiff, Finset.mem_inter]
    tauto
  rw [hsplit, mul_assoc, ← pow_two, ← Finset.prod_pow]
  simp only [hx, Finset.prod_const_one, mul_one]

/-- **Degree of a monomial product.**  The symmetric difference has size at most the sum: multiplying a
degree-`|A|` monomial by a degree-`|B|` monomial yields a monomial of degree `≤ |A| + |B|`. -/
theorem card_symmDiff_le (A B : Finset (Fin n)) : (A ∆ B).card ≤ A.card + B.card := by
  have hsub : A ∆ B ⊆ A ∪ B := by
    intro a ha
    simp only [Finset.mem_symmDiff, Finset.mem_union] at ha ⊢
    tauto
  exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le A B)

end PallLean.Paper93.DeepMath.PathB.Boosting

#print axioms PallLean.Paper93.DeepMath.PathB.Boosting.prod_mul_prod_symmDiff
#print axioms PallLean.Paper93.DeepMath.PathB.Boosting.card_symmDiff_le
