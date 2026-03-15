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
  intro v hv
  rw [MvPolynomial.mem_vars] at hv ⊢
  obtain ⟨d, hd_supp, hv_d⟩ := hv
  -- d ∈ (pderiv x p).support means (pderiv x p).coeff d ≠ 0
  rw [MvPolynomial.mem_support_iff] at hd_supp
  -- Write p = ∑ monomial s (coeff s p), then pderiv x p = ∑ monomial (s-δx) (coeff s p * s x)
  -- If coeff d ≠ 0, there must exist s ∈ p.support contributing to this coefficient
  -- Such s satisfies s - single x 1 = d (as Finsupp), so s.support ⊇ d.support ∋ v
  -- We find such s: s = d + single x 1 might work, but let's use contrapositive
  by_contra h_not
  -- h_not : ¬ ∃ d ∈ p.support, v ∈ d.support (already rewritten by line 64)
  have hv_zero : ∀ s ∈ p.support, s v = 0 := by
    intro s hs
    by_contra hsv
    exact absurd ⟨s, hs, Finsupp.mem_support_iff.mpr hsv⟩ h_not
  -- But v ∈ d.support means d v ≠ 0
  rw [Finsupp.mem_support_iff] at hv_d
  -- Show (pderiv x p).coeff d = 0, contradicting hd_supp
  apply hd_supp
  have : p = p.support.sum (fun s => monomial s (p.coeff s)) := MvPolynomial.as_sum p
  conv_lhs => rw [this]
  rw [map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro s hs
  rw [pderiv_monomial, MvPolynomial.coeff_monomial]
  split_ifs with heq
  · -- s - single x 1 = d, so d v = (s - single x 1) v = s v - (single x 1) v
    -- s v = 0 by hv_zero, and (single x 1) v ≥ 0, so d v = 0
    exfalso; apply hv_d
    rw [← heq]
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
    have := hv_zero s hs
    split_ifs <;> omega
  · rfl

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

/-! ## Linearity of iterDerivList over sums -/

theorem iterDerivList_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (S : List (Fin n))
    (f : ι → MvPolynomial (Fin n) F) :
    iterDerivList S (∑ i ∈ s, f i) = ∑ i ∈ s, iterDerivList S (f i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold iterDerivList; exact foldl_pderiv_zero S
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, iterDerivList_add, ih, Finset.sum_insert ha]

/-! ## Product decomposition into allocation sum -/

/-- Extend an allocation: given β on S' (length κ') and a target j for the new derivative,
    produce an allocation on (x :: S') (length κ'+1). -/
def extendAlloc {κ' m : ℕ} (β : DerivAlloc κ' m) (j : Fin m) : DerivAlloc (κ' + 1) m :=
  fun k => if h : k.val = 0 then j else β ⟨k.val - 1, by omega⟩

/-- Replace factor j with (pderiv x (factor j)) in the product. -/
noncomputable def replaceWithPderiv (x : Fin n) (factor : Fin m → MvPolynomial (Fin n) F) (j : Fin m) :
    Fin m → MvPolynomial (Fin n) F :=
  fun i => if i = j then pderiv x (factor j) else factor i

/-! ## Allocation lemmas -/

/-- allocatedDerivs for an empty list is empty. -/
theorem allocatedDerivs_nil (α : DerivAlloc 0 m) (i : Fin m) :
    allocatedDerivs (n := n) [] rfl α i = [] := by
  simp [allocatedDerivs, List.finRange]

/-- For extendAlloc β j, the allocated derivs to factor i from (x :: S') are:
    - if i = j: x :: allocatedDerivs S' β i
    - if i ≠ j: allocatedDerivs S' β i -/
theorem allocatedDerivs_cons_extendAlloc (x : Fin n) (S' : List (Fin n))
    (hS' : S'.length = κ') (β : DerivAlloc κ' m) (j i : Fin m) :
    allocatedDerivs (x :: S') (by simp [hS']) (extendAlloc β j) i =
      if i = j then x :: allocatedDerivs S' hS' β i
      else allocatedDerivs S' hS' β i := by
  subst hS'
  by_cases hij : j = i
  · subst hij
    simp only [allocatedDerivs, extendAlloc, List.finRange_succ, List.filterMap_cons,
      Fin.val_zero, dite_true, ite_true, List.filterMap_map, Function.comp]
    congr 1
  · have hne : ¬(i = j) := fun h => hij h.symm
    unfold allocatedDerivs
    rw [List.finRange_succ, List.filterMap_cons]
    simp only [extendAlloc, Fin.val_zero, dite_true, hij, hne, ite_false]
    rw [List.filterMap_map]
    congr 1

/-! ## Rewriting Leibniz summand as a product -/

/-- The j-th Leibniz summand (pderiv x (f j)) * ∏_{i ≠ j} f i
    equals ∏ i, (if i = j then pderiv x (f j) else f i). -/
theorem leibniz_summand_eq_prod [DecidableEq (Fin m)] (x : Fin n)
    (factor : Fin m → MvPolynomial (Fin n) F) (j : Fin m) :
    pderiv x (factor j) * ∏ i ∈ Finset.univ.erase j, factor i =
    ∏ i : Fin m, if i = j then pderiv x (factor j) else factor i := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_erase] at hi
    simp [hi.1]

/-! ## SPDP generators lie in product-derivative span -/

/-- The SPDP generators for a product ∏ f_i are contained in the span
    of { ∏_i iterDerivList (α⁻¹(i)) f_i } over all
    derivative allocations α.

    This is the key structural lemma: it reduces the SPDP analysis
    of a product to per-factor derivative analysis. -/
theorem iterDerivList_prod_in_alloc_span
    (m : ℕ) (factor : Fin m → MvPolynomial (Fin n) F)
    (S : List (Fin n)) (hS : S.length = κ) :
    iterDerivList S (∏ i : Fin m, factor i) ∈
      Submodule.span F
        { q | ∃ (α : DerivAlloc κ m),
          q = ∏ i : Fin m, iterDerivList (allocatedDerivs S hS α i) (factor i) } := by
  induction S generalizing κ factor with
  | nil =>
    subst hS
    apply Submodule.subset_span
    exact ⟨Fin.elim0, by congr 1⟩
  | cons x S' ih =>
    -- κ = S'.length + 1
    have hκ : κ = S'.length + 1 := by simp at hS; omega
    subst hκ
    have hS' : S'.length = S'.length := rfl
    -- iterDerivList (x :: S') (∏ f_i) = iterDerivList S' (pderiv x (∏ f_i))
    show iterDerivList S' (pderiv x (∏ i : Fin m, factor i)) ∈ _
    -- Apply Leibniz rule
    rw [pderiv_finset_prod x Finset.univ factor]
    -- = iterDerivList S' (∑ j, (pderiv x (f j)) * ∏_{i≠j} f i)
    rw [iterDerivList_sum]
    -- = ∑ j, iterDerivList S' ((pderiv x (f j)) * ∏_{i≠j} f i)
    -- Each summand is in the span by IH (with modified factors)
    apply Submodule.sum_mem
    intro j _
    -- Rewrite the j-th summand as a product
    rw [leibniz_summand_eq_prod]
    -- Apply IH with g_i = if i = j then pderiv x (f j) else f i
    set g := (fun i => if i = j then pderiv x (factor j) else factor i) with hg_def
    have h_ih := ih g rfl
    -- h_ih gives membership in span of allocations over S'
    -- We need to map this into the span of allocations over (x :: S')
    -- Show the IH span is ≤ our target span
    have h_le : Submodule.span F
        { q | ∃ (β : DerivAlloc S'.length m),
          q = ∏ i : Fin m, iterDerivList (allocatedDerivs S' rfl β i) (g i) } ≤
      Submodule.span F
        { q | ∃ (α : DerivAlloc (S'.length + 1) m),
          q = ∏ i : Fin m, iterDerivList (allocatedDerivs (x :: S') (by simp) α i) (factor i) } := by
      apply Submodule.span_le.mpr
      intro q ⟨β, hq⟩
      apply Submodule.subset_span
      refine ⟨extendAlloc β j, ?_⟩
      rw [hq]
      congr 1; ext i
      rw [allocatedDerivs_cons_extendAlloc x S' rfl β j i]
      simp only [hg_def]
      split_ifs with hij
      · -- i = j: iterDerivList (x :: stuff) (factor j) = iterDerivList stuff (pderiv x (factor j))
        subst hij; unfold iterDerivList; rfl
      · -- i ≠ j: unchanged
        rfl
    exact h_le h_ih

end SPDP
