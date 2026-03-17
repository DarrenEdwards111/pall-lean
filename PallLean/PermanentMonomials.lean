/-
  PermanentMonomials.lean — Prove perm_derivs_have_unique_monomials

  Proves that the m² first derivatives of perm_m have pairwise disjoint
  monomial supports, hence the unique monomial property.
-/
import PallLean.Permanent
import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Variables

namespace PermanentMonomials

open MvPolynomial Finset Permanent

/-! ## Leibniz rule for derivations on Finset.prod -/

theorem Derivation.leibniz_prod {R A M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
    (D : Derivation R A M)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → A) :
    D (∏ i ∈ s, f i) = ∑ k ∈ s, (∏ i ∈ s.erase k, f i) • D (f k) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s hna IH =>
    rw [Finset.prod_insert hna, D.leibniz, IH,
        Finset.sum_insert hna, Finset.erase_insert hna, add_comm]
    congr 1
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hka : k ≠ a := fun h => hna (h ▸ hk)
    have ha_not : a ∉ s.erase k := fun h => hna (Finset.mem_of_mem_erase h)
    rw [Finset.erase_insert_of_ne hka.symm, Finset.prod_insert ha_not, ← smul_smul]

/-! ## pderiv on product of X terms -/

theorem pderiv_prod_X {σ : Type*} [DecidableEq σ]
    {R : Type*} [CommRing R]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → σ) (x : σ) :
    pderiv x (∏ i ∈ s, (X (f i) : MvPolynomial σ R)) =
    ∑ k ∈ s, if f k = x then ∏ i ∈ s.erase k, X (f i) else 0 := by
  have := Derivation.leibniz_prod (pderiv x : Derivation R (MvPolynomial σ R) _) s
    (fun i => X (f i))
  convert this using 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [pderiv_X, Pi.single_apply, smul_eq_mul]
  split_ifs with h
  · simp
  · simp

/-! ## Derivative of permPoly -/

theorem pderiv_permPoly (m : ℕ) (R : Type*) [CommRing R]
    (i₀ j₀ : Fin m) :
    pderiv (i₀, j₀) (permPoly m R) =
    ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin m))).filter (fun σ => σ i₀ = j₀),
      ∏ i ∈ Finset.univ.erase i₀, (X (i, σ i) : MvPolynomial (MatVar m) R) := by
  unfold permPoly
  simp only [map_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro σ _
  rw [pderiv_prod_X Finset.univ (fun i => (i, σ i)) (i₀, j₀)]
  simp only [Prod.mk.injEq]
  by_cases hσ : σ i₀ = j₀
  · rw [if_pos hσ, Finset.sum_eq_single i₀]
    · simp [hσ]
    · intro k _ hk
      simp only [ite_eq_right_iff]
      intro ⟨h1, _⟩; exact absurd h1 hk
    · intro h; exact absurd (Finset.mem_univ i₀) h
  · rw [if_neg hσ]
    apply Finset.sum_eq_zero
    intro k _
    simp only [ite_eq_right_iff]
    intro ⟨h1, h2⟩; subst h1; exact absurd h2 hσ

/-! ## Product of X terms is a monomial -/

theorem prod_X_eq_monomial {σ : Type*} [DecidableEq σ]
    {R : Type*} [CommRing R]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → σ) :
    ∏ i ∈ s, (X (f i) : MvPolynomial σ R) =
    monomial (∑ i ∈ s, Finsupp.single (f i) 1) 1 := by
  induction s using Finset.induction with
  | empty => simp [monomial_zero']
  | insert a s hna IH =>
    rw [Finset.prod_insert hna, IH, X, monomial_mul, one_mul,
        Finset.sum_insert hna]

/-- Support of ∏ X(f i) is a singleton. -/
theorem support_prod_X {σ : Type*} [DecidableEq σ]
    {R : Type*} [CommRing R] [Nontrivial R]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → σ) :
    (∏ i ∈ s, (X (f i) : MvPolynomial σ R)).support =
    {∑ i ∈ s, Finsupp.single (f i) 1} := by
  classical
  rw [prod_X_eq_monomial, support_monomial, if_neg one_ne_zero]

/-! ## Variable support -/

/-- The derivative ∂_{(i₀,j₀)}(permPoly) only involves variables (i,j) with
    i ≠ i₀ ∧ j ≠ j₀. Proved via vars_prod and vars_X. -/
theorem pderiv_permPoly_vars_subset (m : ℕ) (i₀ j₀ : Fin m)
    (x : MatVar m)
    (hx : x ∈ (pderiv (i₀, j₀) (permPoly m ℚ)).vars) :
    x.1 ≠ i₀ ∧ x.2 ≠ j₀ := by
  rw [pderiv_permPoly] at hx
  rw [mem_vars] at hx
  obtain ⟨d, hd_supp, hx_d⟩ := hx
  -- d ∈ support of ∑_σ ∏_{i≠i₀} X(i, σ i)
  -- → d ∈ support of some summand
  rw [mem_support_iff] at hd_supp
  -- d must be in the support of some summand
  have hd_mem : d ∈ (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin m) => σ i₀ = j₀),
    ∏ i ∈ Finset.univ.erase i₀, (X (i, σ i) : MvPolynomial (MatVar m) ℚ)).support :=
    mem_support_iff.mpr hd_supp
  have hd_biunion := Finsupp.support_finset_sum hd_mem
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hd_biunion
  obtain ⟨σ, hσ, hd_σ⟩ := hd_biunion
  -- d ∈ support of ∏_{i≠i₀} X(i, σ i) = {∑ single (i, σ i) 1}
  have h_supp := support_prod_X (R := ℚ) (Finset.univ.erase i₀) (fun k : Fin m => ((k, σ k) : MatVar m))
  have hd_σ' : d ∈ ({∑ i ∈ Finset.univ.erase i₀,
    Finsupp.single ((i, σ i) : MatVar m) 1} : Finset _) := h_supp ▸ hd_σ
  simp only [Finset.mem_singleton] at hd_σ'
  subst hd_σ'
  -- x ∈ d.support = (∑ single (i, σ i) 1).support
  rw [Finsupp.mem_support_iff] at hx_d
  -- x = (k, σ k) for some k ≠ i₀ with σ k ≠ j₀
  simp only [Finsupp.finset_sum_apply, Finsupp.single_apply] at hx_d
  -- The sum ∑_{i≠i₀} (if (i, σ i) = x then 1 else 0) ≠ 0
  -- means some i ≠ i₀ has (i, σ i) = x
  have : ∃ k ∈ Finset.univ.erase i₀, (k, σ k) = x := by
    by_contra h
    push_neg at h
    apply hx_d
    apply Finset.sum_eq_zero
    intro k hk
    simp [h k hk]
  obtain ⟨k, hk, hkx⟩ := this
  subst hkx
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk
  refine ⟨hk, fun h => hk (σ.injective ?_)⟩
  exact h.trans hσ.symm

/-- Corollary: if coeff α ≠ 0, then α only uses rows ≠ i₀ and cols ≠ j₀. -/
theorem pderiv_permPoly_coeff_support (m : ℕ) (i₀ j₀ : Fin m)
    (α : MatVar m →₀ ℕ) (hα : coeff α (pderiv (i₀, j₀) (permPoly m ℚ)) ≠ 0)
    (x : MatVar m) (hx : α x ≠ 0) :
    x.1 ≠ i₀ ∧ x.2 ≠ j₀ := by
  exact pderiv_permPoly_vars_subset m i₀ j₀ x
    ((mem_vars x).mpr ⟨α, mem_support_iff.mpr hα, Finsupp.mem_support_iff.mpr hx⟩)

/-- Any monomial with nonzero coeff covers all rows ≠ i₀. -/
theorem pderiv_permPoly_covers_rows (m : ℕ) (i₀ j₀ : Fin m)
    (α : MatVar m →₀ ℕ) (hα : coeff α (pderiv (i₀, j₀) (permPoly m ℚ)) ≠ 0)
    (i : Fin m) (hi : i ≠ i₀) :
    ∃ j, α (i, j) > 0 := by
  rw [pderiv_permPoly] at hα
  -- α ∈ support of the sum
  rw [← mem_support_iff] at hα
  have hα_bi := Finsupp.support_finset_sum hα
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hα_bi
  obtain ⟨σ, hσ, hα_σ⟩ := hα_bi
  -- α ∈ support of ∏_{k≠i₀} X(k, σ k) = {∑ single (k, σ k) 1}
  have h_supp := support_prod_X (R := ℚ) (Finset.univ.erase i₀)
    (fun k : Fin m => ((k, σ k) : MatVar m))
  have hα_σ' : α ∈ ({∑ k ∈ Finset.univ.erase i₀,
    Finsupp.single ((k, σ k) : MatVar m) 1} : Finset _) := h_supp ▸ hα_σ
  simp only [Finset.mem_singleton] at hα_σ'
  subst hα_σ'
  -- α (i, σ i) = (∑ single (k, σ k) 1) (i, σ i) = 1 > 0
  refine ⟨σ i, ?_⟩
  simp only [Finsupp.finset_sum_apply, Finsupp.single_apply]
  have hi_mem : i ∈ Finset.univ.erase i₀ := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
  have h1 := Finset.single_le_sum
    (f := fun k => (Finsupp.single ((k, σ k) : MatVar m) (1 : ℕ)) (i, σ i))
    (fun _ _ => Nat.zero_le _) hi_mem
  simp only [Finsupp.single_apply, Prod.mk.injEq, ite_true, eq_self_iff_true,
    true_and] at h1
  -- h1 : 1 ≤ ∑ x ∈ univ.erase i₀, if x = i ∧ σ x = σ i then 1 else 0
  -- goal : ∑ x ∈ univ.erase i₀, if (x, σ x) = (i, σ i) then 1 else 0 > 0
  simp only [Prod.mk.injEq] at *
  linarith

/-! ## Main: different-row case is proved from the above -/

theorem pderiv_permPoly_disjoint_diff_row (m : ℕ)
    (i₀ j₀ i₀' j₀' : Fin m) (hi : i₀ ≠ i₀')
    (α : MatVar m →₀ ℕ)
    (hv : coeff α (pderiv (i₀, j₀) (permPoly m ℚ)) ≠ 0) :
    coeff α (pderiv (i₀', j₀') (permPoly m ℚ)) = 0 := by
  obtain ⟨j, hj⟩ := pderiv_permPoly_covers_rows m i₀ j₀ α hv i₀' hi.symm
  by_contra h
  have ⟨h1, _⟩ := pderiv_permPoly_coeff_support m i₀' j₀' α h (i₀', j) (by omega)
  exact h1 rfl

theorem pderiv_permPoly_disjoint_diff_col (m : ℕ)
    (i₀ j₀ j₀' : Fin m) (hj : j₀ ≠ j₀')
    (α : MatVar m →₀ ℕ)
    (hv : coeff α (pderiv (i₀, j₀) (permPoly m ℚ)) ≠ 0) :
    coeff α (pderiv (i₀, j₀') (permPoly m ℚ)) = 0 := by
  -- Extract the permutation σ from α's structure
  rw [pderiv_permPoly] at hv
  rw [← mem_support_iff] at hv
  have hα_bi := Finsupp.support_finset_sum hv
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hα_bi
  obtain ⟨σ, hσ, hα_σ⟩ := hα_bi
  have h_supp := support_prod_X (R := ℚ) (Finset.univ.erase i₀)
    (fun k : Fin m => ((k, σ k) : MatVar m))
  have hα_σ' : α ∈ ({∑ k ∈ Finset.univ.erase i₀,
    Finsupp.single ((k, σ k) : MatVar m) 1} : Finset _) := h_supp ▸ hα_σ
  simp only [Finset.mem_singleton] at hα_σ'
  subst hα_σ'
  -- α uses col j₀': since σ is a bijection and σ(i₀) = j₀ ≠ j₀',
  -- ∃ i ≠ i₀ with σ(i) = j₀'
  have ⟨i, hi⟩ := σ.surjective j₀'
  have hi_ne : i ≠ i₀ := by
    intro h; subst h; rw [hi] at hσ; exact hj hσ.symm
  -- α(i, j₀') = (∑ single (k, σ k) 1)(i, j₀') ≥ 1
  have hα_pos : (∑ k ∈ Finset.univ.erase i₀,
      Finsupp.single ((k, σ k) : MatVar m) 1) (i, j₀') > 0 := by
    simp only [Finsupp.finset_sum_apply, Finsupp.single_apply, Prod.mk.injEq]
    rw [← hi]
    have hi_mem : i ∈ Finset.univ.erase i₀ := Finset.mem_erase.mpr ⟨hi_ne, Finset.mem_univ i⟩
    -- Goal: (∑ x ∈ univ.erase i₀, if x = i ∧ σ x = σ i then 1 else 0) > 0
    have h_le : (if i = i ∧ σ i = σ i then 1 else 0 : ℕ) ≤
        ∑ x ∈ Finset.univ.erase i₀,
          (if x = i ∧ σ x = σ i then 1 else 0 : ℕ) :=
      Finset.single_le_sum (f := fun x => if x = i ∧ σ x = σ i then 1 else 0)
        (fun _ _ => Nat.zero_le _) hi_mem
    simp at h_le ⊢; omega
  -- But pderiv (i₀, j₀') excludes col j₀'. Contradiction.
  by_contra h
  have ⟨_, h2⟩ := pderiv_permPoly_coeff_support m i₀ j₀' _ h (i, j₀') (by omega)
  exact h2 rfl

end PermanentMonomials
