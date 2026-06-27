import Mathlib

/-!
# The Smolensky boosting step (PROVED core) — the folding identity

The Razborov–Smolensky lower bound is closed by the *dimension argument* (see `ComputationalDepthDimension`): if
`MOD_q` were approximated on a large set `G ⊆ {-1,+1}ⁿ` by a degree-`d` `𝔽_p`-polynomial, then **every** function
`G → 𝔽_p` would be realised by a polynomial of degree `≤ n/2 + d`, forcing `|G| ≤ Σ_{i ≤ n/2+d} C(n,i) < 2ⁿ`.

The **boosting** step — "every function on `G` is low degree" — turns on a single algebraic identity.  Over
`{-1,+1}ⁿ` each coordinate satisfies `xᵢ² = 1`, and then a high-degree monomial *folds*:

  `prod_eq_full_mul_prod_compl` — `∏_{i∈S} xᵢ = (∏ᵢ xᵢ) · ∏_{i∉S} xᵢ`.

The complementary monomial has degree `|Sᶜ| = n - |S|`, which is `< |S|` once `|S| > n/2`
(`card_compl_lt`).  Replacing the *full product* `∏ᵢ xᵢ` (degree `n`) by the low-degree approximator `a`
(`monomial_boost`) thus drops every degree-`>n/2` monomial to degree `(deg a) + (n - |S|) < (deg a) + n/2`.
Summing over a function's multilinear expansion gives the `n/2 + d` degree bound the dimension count consumes.

This file proves that algebraic core; the assembly into the full degree bound on `G` and the choice of
approximator (the OR/`MOD` approximation of `ComputationalDepthOrApprox`) remain the targets.
-/

namespace PallLean.Paper93.DeepMath.PathB.Boosting

variable {R : Type*} [CommMonoid R] {n : ℕ}

/-- **The folding identity (heart of Smolensky boosting).**  When every coordinate squares to `1` (the
`{-1,+1}ⁿ` cube), the product over `S` equals the *full* product times the product over the complement.  So a
degree-`|S|` monomial folds into `(full product) · (degree-(n-|S|) monomial)`. -/
theorem prod_eq_full_mul_prod_compl (x : Fin n → R) (hx : ∀ i, x i ^ 2 = 1) (S : Finset (Fin n)) :
    ∏ i ∈ S, x i = (∏ i, x i) * ∏ i ∈ Sᶜ, x i := by
  rw [← Finset.prod_mul_prod_compl S x, mul_assoc, ← pow_two, ← Finset.prod_pow]
  simp only [hx, Finset.prod_const_one, mul_one]

/-- Folding a *high-degree* monomial (`|S| > n/2`) yields a strictly *lower-degree* complementary monomial:
`|Sᶜ| = n - |S| < |S|`. -/
theorem card_compl_lt (S : Finset (Fin n)) (hS : n < 2 * S.card) : Sᶜ.card < S.card := by
  rw [Finset.card_compl, Fintype.card_fin]
  omega

/-- **Boosting substitution.**  If `a` agrees with the full product at the point `x` (the rôle of the low-degree
approximator on `G`), then the monomial `∏_{i∈S} xᵢ` equals `a · ∏_{i∉S} xᵢ`.  Replacing the degree-`n` full
product by a degree-`d` approximator drops the degree-`|S|` monomial to degree `d + (n - |S|)`, which is
`< d + n/2` whenever `|S| > n/2` (`card_compl_lt`). -/
theorem monomial_boost (x : Fin n → R) (hx : ∀ i, x i ^ 2 = 1) (S : Finset (Fin n)) (a : R)
    (ha : a = ∏ i, x i) : ∏ i ∈ S, x i = a * ∏ i ∈ Sᶜ, x i := by
  rw [ha]; exact prod_eq_full_mul_prod_compl x hx S

/-- The `{-1,+1}ⁿ` cube concretely satisfies the squares-to-one hypothesis: a sign vector
`xᵢ = (-1)^{bᵢ}` has `xᵢ² = 1`. -/
theorem sign_sq_one {F : Type*} [Ring F] (b : Fin n → Bool) (i : Fin n) :
    (fun j => if b j then (-1 : F) else 1) i ^ 2 = 1 := by
  by_cases h : b i <;> simp [h]

end PallLean.Paper93.DeepMath.PathB.Boosting

#print axioms PallLean.Paper93.DeepMath.PathB.Boosting.prod_eq_full_mul_prod_compl
#print axioms PallLean.Paper93.DeepMath.PathB.Boosting.monomial_boost
#print axioms PallLean.Paper93.DeepMath.PathB.Boosting.sign_sq_one
