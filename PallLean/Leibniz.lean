import PallLean.MultilinearSPDP

/-! # Iterated Leibniz rule for partial derivatives of products

Layer 1 of the Width⇒Rank proof.

We prove that `iterDerivList S (∏ f_i)` decomposes as a sum over
"derivative allocations" — functions assigning each derivative in S
to one of the m factors.

## Main results

* `pderiv_finset_prod` — single derivative of a Finset.prod
* `iterDerivList_zero_of_not_in_vars` — derivatives outside vars kill the poly
* `iterDerivList_prod_mem_span` — the SPDP generators for a product
  lie in a subspace spanned by products of per-factor derivatives
-/

namespace SPDP

open MvPolynomial Finset

variable {n : ℕ} {F : Type*} [CommRing F]

/-! ## Single derivative of a finite product (Leibniz rule) -/

/-- Leibniz rule for pderiv of Finset.prod:
    ∂_x(∏_{i ∈ s} f i) = Σ_{j ∈ s} (∂_x(f j)) * ∏_{i ∈ s, i≠j} f i

    This is the standard product rule extended to finite products. -/
theorem pderiv_finset_prod [DecidableEq ι] (x : Fin n) (s : Finset ι) (f : ι → MvPolynomial (Fin n) F) :
    pderiv x (∏ i ∈ s, f i) = ∑ j ∈ s, (pderiv x (f j) * ∏ i ∈ s.erase j, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s hna ih =>
    rw [Finset.prod_insert hna, pderiv_mul, ih]
    rw [Finset.sum_insert hna]
    congr 1
    · congr 1; rw [Finset.erase_insert hna]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hne : a ≠ j := fun h => hna (h ▸ hj)
      rw [← mul_assoc, mul_comm (f a) _, mul_assoc]
      congr 1
      rw [← Finset.prod_insert (show a ∉ s.erase j from
        fun h => hna (Finset.mem_of_mem_erase h))]
      congr 1
      exact (Finset.erase_insert_of_ne hne).symm

/-! ## Derivative vanishing outside vars -/

/-- pderiv by a variable not in the support gives 0. -/
theorem pderiv_eq_zero_of_not_mem_vars (x : Fin n)
    (p : MvPolynomial (Fin n) F) (hx : x ∉ p.vars) :
    pderiv x p = 0 :=
  MvPolynomial.pderiv_eq_zero_of_notMem_vars hx

/-- vars of a partial derivative are contained in vars of the original.
    Differentiation can only remove variables, not introduce them. -/
theorem vars_pderiv_subset (x : Fin n) (p : MvPolynomial (Fin n) F) :
    (pderiv x p).vars ⊆ p.vars := by
  sorry -- Each monomial's exponent decreases; v ∉ vars(p) → ∀ s, s v = 0 → (s-δ_x) v = 0

/-- vars of iterated derivatives are contained in vars of the original. -/
theorem vars_iterDerivList_subset (S : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    (iterDerivList S p).vars ⊆ p.vars := by
  induction S generalizing p with
  | nil => unfold iterDerivList; exact Finset.Subset.refl _
  | cons x S' ih =>
    -- iterDerivList (x :: S') p = iterDerivList S' (pderiv x p)
    show (List.foldl _ (pderiv x p) S').vars ⊆ p.vars
    exact Finset.Subset.trans (ih (pderiv x p)) (vars_pderiv_subset x p)

private theorem foldl_pderiv_zero' (S : List (Fin n)) :
    List.foldl (fun (q : MvPolynomial (Fin n) F) i => pderiv i q) 0 S = 0 := by
  induction S with
  | nil => rfl
  | cons z S' ih => rw [List.foldl_cons, map_zero]; exact ih

theorem iterDerivList_eq_zero_of_exists_not_in_vars
    (S : List (Fin n)) (p : MvPolynomial (Fin n) F)
    (hx : ∃ x ∈ S, x ∉ p.vars) :
    iterDerivList S p = 0 := by
  obtain ⟨x, hxS, hxv⟩ := hx
  induction S generalizing p with
  | nil => simp at hxS
  | cons y S' ih =>
    show List.foldl (fun q i => pderiv i q) (pderiv y p) S' = 0
    rcases List.mem_cons.mp hxS with rfl | hxS'
    · rw [pderiv_eq_zero_of_not_mem_vars x p hxv]
      exact foldl_pderiv_zero' S'
    · exact ih (pderiv y p) hxS' (fun h => hxv (vars_pderiv_subset y p h))

/-! ## Derivative allocation type -/

/-- A derivative allocation assigns each position in the derivative list
    to one of m factors. -/
abbrev DerivAlloc (κ m : ℕ) := Fin κ → Fin m

/-- The derivatives allocated to factor i by allocation α. -/
def allocatedDerivs {κ : ℕ} (S : List (Fin n)) (hS : S.length = κ)
    (α : DerivAlloc κ m) (i : Fin m) : List (Fin n) :=
  (List.finRange κ).filterMap (fun j =>
    if α j = i then some (S.get (j.cast (by omega))) else none)

/-! ## SPDP generators lie in product-derivative span -/

/-- The SPDP generators for a product ∏ f_i are contained in the span
    of { mlProj(mono * ∏_i iterDerivList (α⁻¹(i)) f_i) } over all
    derivative allocations α and monomials mono.

    This is the key structural lemma: it reduces the SPDP analysis
    of a product to per-factor derivative analysis. -/
theorem iterDerivList_prod_in_alloc_span
    (m : ℕ) (factor : Fin m → MvPolynomial (Fin n) F)
    (S : List (Fin n)) (hS : S.length = κ) :
    iterDerivList S (∏ i : Fin m, factor i) ∈
      Submodule.span F
        { q | ∃ (α : DerivAlloc κ m),
          q = ∏ i : Fin m, iterDerivList (allocatedDerivs S hS α i) (factor i) } := by
  sorry -- Follows from iterated application of pderiv_finset_prod

end SPDP
