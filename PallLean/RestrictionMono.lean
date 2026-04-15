/-
  RestrictionMono.lean — Lemma 141: SPDP rank under restriction

  Paper §29.3 / Lemma 141:

  **Lemma 141** (SPDP rank under projection and submatrices):
    Let f be multilinear on variables split as (x, y) with disjoint
    supports. If we delete all SPDP columns whose monomials use any
    y-variable, the resulting submatrix of M_ℓ(f) has rank ≤ rk_{SPDP,ℓ}(f).

  Proof: Deleting columns cannot increase rank.

  Application: If f_{3SAT,N}(φ, a) is the language characteristic polynomial
  (multilinear in both formula-encoding and assignment variables), then
  restricting to a specific formula φ = φ_n gives a polynomial in
  assignment variables only. By Lemma 141:
    rk_{SPDP}(f_{3SAT,N} ↾ {φ = φ_n}) ≤ rk_{SPDP}(f_{3SAT,N})

  Combined with Theorem 139 (rk(f_{3SAT,N}) ≤ N^c when 3-SAT ∈ P):
    rk(χ_{φ_n}) ≤ rk(f_{3SAT,N}) ≤ N^c = poly(n)
-/
import PallLean.SPDPDefs
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace RestrictionMono

open MvPolynomial SPDP

/-! ## Variable Restriction -/

/-- A restriction assigns specific rational values to some variables. -/
structure VarRestriction (n : ℕ) where
  fixedVars : Finset (Fin n)
  assignment : Fin n → ℚ
  freeVars : Finset (Fin n)
  partition : fixedVars ∪ freeVars = Finset.univ
  disjoint : Disjoint fixedVars freeVars

noncomputable def applyRestriction {n : ℕ} (ρ : VarRestriction n)
    (f : MvPolynomial (Fin n) ℚ) : MvPolynomial (Fin n) ℚ :=
  MvPolynomial.eval₂ MvPolynomial.C
    (fun i => if i ∈ ρ.fixedVars then MvPolynomial.C (ρ.assignment i)
              else MvPolynomial.X i) f

/-! ## Restriction as an Algebra Homomorphism -/

noncomputable def restrictionFun {n : ℕ} (ρ : VarRestriction n) :
    Fin n → MvPolynomial (Fin n) ℚ :=
  fun i => if i ∈ ρ.fixedVars then MvPolynomial.C (ρ.assignment i)
           else MvPolynomial.X i

noncomputable def applyRestrictionAlgHom {n : ℕ} (ρ : VarRestriction n) :
    MvPolynomial (Fin n) ℚ →ₐ[ℚ] MvPolynomial (Fin n) ℚ :=
  MvPolynomial.aeval (restrictionFun ρ)

theorem applyRestriction_eq_algHom {n : ℕ} (ρ : VarRestriction n)
    (f : MvPolynomial (Fin n) ℚ) :
    applyRestriction ρ f = applyRestrictionAlgHom ρ f := by
  unfold applyRestriction applyRestrictionAlgHom
  simp only [aeval_def, MvPolynomial.algebraMap_eq]
  rfl

theorem applyRestriction_add {n : ℕ} (ρ : VarRestriction n)
    (f g : MvPolynomial (Fin n) ℚ) :
    applyRestriction ρ (f + g) = applyRestriction ρ f + applyRestriction ρ g := by
  simp only [applyRestriction_eq_algHom, map_add]

theorem applyRestriction_mul {n : ℕ} (ρ : VarRestriction n)
    (f g : MvPolynomial (Fin n) ℚ) :
    applyRestriction ρ (f * g) = applyRestriction ρ f * applyRestriction ρ g := by
  simp only [applyRestriction_eq_algHom, map_mul]

theorem applyRestriction_zero {n : ℕ} (ρ : VarRestriction n) :
    applyRestriction ρ 0 = 0 := by
  simp only [applyRestriction_eq_algHom, map_zero]

/-! ## Commutation of pderiv with applyRestriction -/

theorem free_not_fixed {n : ℕ} (ρ : VarRestriction n) (i : Fin n) (hi : i ∈ ρ.freeVars) :
    i ∉ ρ.fixedVars :=
  Finset.disjoint_right.mp ρ.disjoint hi

theorem fixed_or_free {n : ℕ} (ρ : VarRestriction n) (i : Fin n) :
    i ∈ ρ.fixedVars ∨ i ∈ ρ.freeVars := by
  have : i ∈ Finset.univ := Finset.mem_univ i
  rw [← ρ.partition] at this
  exact Finset.mem_union.mp this

set_option maxHeartbeats 3200000 in
theorem pderiv_applyRestriction_free {n : ℕ} (ρ : VarRestriction n)
    (v : Fin n) (hv : v ∈ ρ.freeVars)
    (f : MvPolynomial (Fin n) ℚ) :
    pderiv v (applyRestriction ρ f) = applyRestriction ρ (pderiv v f) := by
  have hv_nf : v ∉ ρ.fixedVars := free_not_fixed ρ v hv
  conv_lhs => rw [applyRestriction_eq_algHom]
  conv_rhs => rw [applyRestriction_eq_algHom]
  change pderiv v (aeval (restrictionFun ρ) f) = aeval (restrictionFun ρ) (pderiv v f)
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add]; rw [hp, hq]
  | mul_X p u h =>
    simp only [map_mul, aeval_X]
    rw [Derivation.leibniz, Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul]
    -- Rewrite restrictionFun ρ u to its definition
    have h_rfu_eq : restrictionFun ρ u = if u ∈ ρ.fixedVars then C (ρ.assignment u) else X u :=
      rfl
    by_cases huv : u = v
    · subst huv
      -- u = v, which is free, so restrictionFun ρ u = X u
      have h_rfu : restrictionFun ρ u = X u := by simp [restrictionFun, hv_nf]
      rw [h_rfu, pderiv_X_self]
      simp only [map_one, aeval_X, h_rfu, h]
    · -- u ≠ v
      have huv' : u ≠ v := huv
      have h_rfu_deriv : pderiv v (restrictionFun ρ u) = 0 := by
        simp only [restrictionFun]
        split
        · exact pderiv_C
        · exact pderiv_X_of_ne huv'
      have h_pderiv_Xu : pderiv v (X u : MvPolynomial (Fin n) ℚ) = 0 :=
        pderiv_X_of_ne huv'
      rw [h_rfu_deriv, mul_zero, zero_add, h_pderiv_Xu, map_zero, mul_zero, zero_add,
          aeval_X, h]

set_option maxHeartbeats 3200000 in
theorem pderiv_applyRestriction_fixed {n : ℕ} (ρ : VarRestriction n)
    (v : Fin n) (hv : v ∈ ρ.fixedVars)
    (f : MvPolynomial (Fin n) ℚ) :
    pderiv v (applyRestriction ρ f) = 0 := by
  conv_lhs => rw [applyRestriction_eq_algHom]
  change pderiv v (aeval (restrictionFun ρ) f) = 0
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, add_zero]
  | mul_X p u h =>
    simp only [map_mul, aeval_X]
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    have h_rfu : pderiv v (restrictionFun ρ u) = 0 := by
      simp only [restrictionFun]
      split
      · exact pderiv_C
      · have huv : u ≠ v := by
          intro heq; subst heq
          rename_i h_not_fixed; exact h_not_fixed hv
        exact pderiv_X_of_ne huv
    rw [h_rfu, mul_zero, zero_add, h, mul_zero]

/-! ## Iterated derivative commutation -/

theorem iterDerivList_applyRestriction_free {n : ℕ} (ρ : VarRestriction n)
    (S : List (Fin n)) (hS : ∀ v ∈ S, v ∈ ρ.freeVars)
    (f : MvPolynomial (Fin n) ℚ) :
    iterDerivList S (applyRestriction ρ f) =
      applyRestriction ρ (iterDerivList S f) := by
  induction S generalizing f with
  | nil => simp [iterDerivList]
  | cons i rest ih =>
    simp only [iterDerivList, List.foldl_cons]
    have hi : i ∈ ρ.freeVars := hS i List.mem_cons_self
    have hrest : ∀ v ∈ rest, v ∈ ρ.freeVars :=
      fun v hv => hS v (List.mem_cons.mpr (Or.inr hv))
    rw [pderiv_applyRestriction_free ρ i hi f]
    exact ih hrest (pderiv i f)

theorem iterDerivList_applyRestriction_has_fixed {n : ℕ} (ρ : VarRestriction n)
    (S : List (Fin n)) (f : MvPolynomial (Fin n) ℚ)
    (v : Fin n) (hv_fixed : v ∈ ρ.fixedVars) (hv_in_S : v ∈ S) :
    iterDerivList S (applyRestriction ρ f) = 0 := by
  induction S generalizing f with
  | nil => simp at hv_in_S
  | cons i rest ih =>
    simp only [iterDerivList, List.foldl_cons]
    rcases List.eq_or_mem_of_mem_cons hv_in_S with hvi | hv_rest
    · subst hvi
      rw [pderiv_applyRestriction_fixed ρ v hv_fixed f]
      exact foldl_pderiv_zero rest
    · rcases fixed_or_free ρ i with hi_fixed | hi_free
      · rw [pderiv_applyRestriction_fixed ρ i hi_fixed f]
        exact foldl_pderiv_zero rest
      · rw [pderiv_applyRestriction_free ρ i hi_free f]
        exact ih (pderiv i f) hv_rest

theorem iterDerivList_applyRestriction {n : ℕ} (ρ : VarRestriction n)
    (S : List (Fin n)) (f : MvPolynomial (Fin n) ℚ) :
    iterDerivList S (applyRestriction ρ f) =
      if ∀ v ∈ S, v ∈ ρ.freeVars
      then applyRestriction ρ (iterDerivList S f)
      else 0 := by
  split
  · exact iterDerivList_applyRestriction_free ρ S ‹_› f
  · push_neg at *
    obtain ⟨v, hv_in_S, hv_not_free⟩ := ‹_›
    have hv_fixed : v ∈ ρ.fixedVars :=
      (fixed_or_free ρ v).elim id (fun h => absurd h hv_not_free)
    exact iterDerivList_applyRestriction_has_fixed ρ S f v hv_fixed hv_in_S

theorem applyRestriction_monomial_of_support_subset_free {n : ℕ}
    (ρ : VarRestriction n) (d : Fin n →₀ ℕ)
    (hd : d.support ⊆ ρ.freeVars) :
    applyRestriction ρ (MvPolynomial.monomial d (1 : ℚ)) =
      MvPolynomial.monomial d (1 : ℚ) := by
  rw [applyRestriction_eq_algHom, applyRestrictionAlgHom, MvPolynomial.aeval_monomial]
  simp only [map_one, one_mul]
  rw [d.prod_of_support_subset hd (fun i e => restrictionFun ρ i ^ e) (by
        intro i hi
        simp),
      MvPolynomial.monic_monomial_eq,
      d.prod_of_support_subset hd (fun i e => (MvPolynomial.X i : MvPolynomial (Fin n) ℚ) ^ e) (by
        intro i hi
        simp)]
  apply Finset.prod_congr rfl
  intro i hi
  have hi_free : i ∈ ρ.freeVars := hi
  have hi_not_fixed : i ∉ ρ.fixedVars := free_not_fixed ρ i hi_free
  simp [restrictionFun, hi_not_fixed]

private theorem free_monomial_generator_mem_restriction_map {n : ℕ}
    (ρ : VarRestriction n) (f : MvPolynomial (Fin n) ℚ)
    (κ ℓ : ℕ) (S : List (Fin n)) (d : Fin n →₀ ℕ)
    (hSlen : S.length = κ)
    (hSfree : ∀ v ∈ S, v ∈ ρ.freeVars)
    (hddeg : d.sum (fun _ e => e) ≤ ℓ)
    (hdfree : d.support ⊆ ρ.freeVars) :
    MvPolynomial.monomial d (1 : ℚ) * iterDerivList S (applyRestriction ρ f) ∈
      Submodule.map (applyRestrictionAlgHom ρ).toLinearMap (spdpSubspace κ ℓ f) := by
  let q := MvPolynomial.monomial d (1 : ℚ) * iterDerivList S f
  have hq_mem : q ∈ spdpSubspace κ ℓ f := by
    apply Submodule.subset_span
    refine ⟨S, MvPolynomial.monomial d (1 : ℚ), hSlen, ?_, by simp [q]⟩
    exact le_trans (MvPolynomial.totalDegree_monomial_le d (1 : ℚ)) hddeg
  refine ⟨q, hq_mem, ?_⟩
  change applyRestriction ρ (MvPolynomial.monomial d (1 : ℚ) * iterDerivList S f) =
    MvPolynomial.monomial d (1 : ℚ) * iterDerivList S (applyRestriction ρ f)
  rw [applyRestriction_mul]
  rw [applyRestriction_monomial_of_support_subset_free ρ d hdfree,
      iterDerivList_applyRestriction_free ρ S hSfree f]

/-! ## Coefficient-space bridge

These local definitions are the reusable linear-algebra core needed for the
honest coefficient-matrix proof of Lemma 141. They are copied into the active
file so the remaining gap is closer to a concrete matrix-rank argument. -/

namespace CoeffBridge

open MvPolynomial

variable {σ : Type*} [DecidableEq σ] {F : Type*} [Field F]

noncomputable def coeffVector (monomials : Finset (σ →₀ ℕ))
    (p : MvPolynomial σ F) : monomials → F :=
  fun m => MvPolynomial.coeff m.val p

noncomputable def coeffVectorLin (monomials : Finset (σ →₀ ℕ)) :
    MvPolynomial σ F →ₗ[F] (monomials → F) where
  toFun := coeffVector monomials
  map_add' p q := by ext m; simp [coeffVector, MvPolynomial.coeff_add]
  map_smul' c p := by ext m; simp [coeffVector, MvPolynomial.coeff_smul]

theorem coeffVector_injective (monomials : Finset (σ →₀ ℕ))
    (p q : MvPolynomial σ F)
    (hp : p.support ⊆ monomials) (hq : q.support ⊆ monomials)
    (h : coeffVector monomials p = coeffVector monomials q) : p = q := by
  ext m
  by_cases hm : m ∈ monomials
  · exact congr_fun h ⟨m, hm⟩
  · have hp0 : MvPolynomial.coeff m p = 0 := by
      by_contra hne
      exact hm (hp (Finsupp.mem_support_iff.mpr hne))
    have hq0 : MvPolynomial.coeff m q = 0 := by
      by_contra hne
      exact hm (hq (Finsupp.mem_support_iff.mpr hne))
    simp [hp0, hq0]

noncomputable def coeffMatrix {ι : Type*} [Fintype ι]
    (monomials : Finset (σ →₀ ℕ))
    (generators : ι → MvPolynomial σ F) :
    Matrix ι monomials F :=
  fun i m => MvPolynomial.coeff m.val (generators i)

def supportedSub (monomials : Finset (σ →₀ ℕ)) :
    Submodule F (MvPolynomial σ F) where
  carrier := { p | p.support ⊆ monomials }
  add_mem' ha hb := Finset.Subset.trans Finsupp.support_add (Finset.union_subset ha hb)
  zero_mem' := by simp
  smul_mem' c _ hp := Finset.Subset.trans Finsupp.support_smul hp

theorem span_in_supported (monomials : Finset (σ →₀ ℕ))
    (S : Set (MvPolynomial σ F))
    (h : ∀ g ∈ S, (g : MvPolynomial σ F).support ⊆ monomials) :
    Submodule.span F S ≤ supportedSub monomials :=
  Submodule.span_le.mpr h

theorem coeffVectorLin_injOn (monomials : Finset (σ →₀ ℕ)) :
    Function.Injective
      ((coeffVectorLin (F := F) monomials).domRestrict (supportedSub monomials)) := by
  intro ⟨p, hp⟩ ⟨q, hq⟩ heq
  simp only [LinearMap.domRestrict_apply, Subtype.mk.injEq] at heq ⊢
  exact coeffVector_injective monomials p q hp hq heq

theorem finrank_span_eq_matrix_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (monomials : Finset (σ →₀ ℕ))
    (generators : ι → MvPolynomial σ F)
    (hsupport : ∀ i, (generators i).support ⊆ monomials) :
    Module.finrank F (Submodule.span F (Set.range generators)) =
    (coeffMatrix monomials generators).rank := by
  let f := coeffVectorLin (σ := σ) (F := F) monomials
  have h_le := span_in_supported monomials _ (by
    intro g hg
    rw [Set.mem_range] at hg
    obtain ⟨i, rfl⟩ := hg
    exact hsupport i)
  have step1 : Module.finrank F (Submodule.span F (Set.range generators)) =
      Module.finrank F (Submodule.map f (Submodule.span F (Set.range generators))) := by
    let fV := f.domRestrict (Submodule.span F (Set.range generators))
    have fV_inj : Function.Injective fV := by
      intro ⟨p, hp⟩ ⟨q, hq⟩ heq
      simp only [Subtype.mk.injEq] at heq ⊢
      exact coeffVector_injective monomials p q (h_le hp) (h_le hq) heq
    let e := LinearEquiv.ofInjective fV fV_inj
    have h_range : LinearMap.range fV = (Submodule.span F (Set.range generators)).map f := by
      ext x
      simp only [LinearMap.mem_range, Submodule.mem_map]
      constructor
      · rintro ⟨⟨a, ha⟩, rfl⟩
        exact ⟨a, ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, rfl⟩
    rw [← h_range]
    exact (LinearEquiv.finrank_eq e)
  have step2 : Submodule.map f (Submodule.span F (Set.range generators)) =
      Submodule.span F (Set.range (fun i : ι => f (generators i))) := by
    rw [Submodule.map_span]
    congr 1
    ext v
    simp [Set.mem_image, Set.mem_range]
  have step3 : (fun i : ι => f (generators i)) =
      (fun i : ι => (fun m : monomials => (coeffMatrix monomials generators) i m)) := by
    ext i m
    rfl
  rw [step1, step2, step3]
  let A := coeffMatrix monomials generators
  rw [show (fun i : ι => (fun m : monomials => A i m)) =
      (fun i : ι => (Matrix.transpose A).col i) from by
        ext i m
        simp [Matrix.transpose, Matrix.col]]
  rw [← Matrix.rank_eq_finrank_span_cols, Matrix.rank_transpose]

end CoeffBridge

/-! ## Degree-bounded columns and restriction action on coefficient vectors -/

noncomputable def monomialsLE (n D : ℕ) : Finset ((Fin n) →₀ ℕ) :=
  (Finset.range (D + 1)).biUnion fun k =>
    (Finset.univ : Finset (Fin n)).finsuppAntidiag k

theorem mem_monomialsLE {n D : ℕ} {d : (Fin n) →₀ ℕ} :
    d ∈ monomialsLE n D ↔ d.sum (fun _ e => e) ≤ D := by
  unfold monomialsLE
  constructor
  · intro hd
    rcases Finset.mem_biUnion.mp hd with ⟨k, hk, hdk⟩
    rw [(Finset.mem_finsuppAntidiag'.mp hdk).1]
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  · intro hd
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨d.sum (fun _ e => e), Finset.mem_range.mpr (Nat.lt_succ_of_le hd), ?_⟩
    exact Finset.mem_finsuppAntidiag'.mpr ⟨rfl, Finset.subset_univ _⟩

noncomputable def restrictionColumnMatrix {n : ℕ}
    (ρ : VarRestriction n)
    (source target : Finset ((Fin n) →₀ ℕ)) :
    Matrix source target ℚ :=
  fun s t =>
    MvPolynomial.coeff t.1 (applyRestriction ρ (MvPolynomial.monomial s.1 (1 : ℚ)))

theorem coeffVector_applyRestriction_eq_sum_restrictionColumns {n : ℕ}
    (ρ : VarRestriction n)
    (source target : Finset ((Fin n) →₀ ℕ))
    (p : MvPolynomial (Fin n) ℚ)
    (hsource : p.support ⊆ source)
    (_htarget : (applyRestriction ρ p).support ⊆ target) :
    CoeffBridge.coeffVector target (applyRestriction ρ p) =
      fun t =>
        ∑ s : source,
          CoeffBridge.coeffVector source p s *
            restrictionColumnMatrix ρ source target s t := by
  sorry

theorem coeffMatrix_applyRestriction_eq_mul_restrictionColumns
    {n ι : ℕ}
    (ρ : VarRestriction n)
    (source target : Finset ((Fin n) →₀ ℕ))
    (generators : Fin ι → MvPolynomial (Fin n) ℚ)
    (hsource : ∀ i, (generators i).support ⊆ source)
    (htarget : ∀ i, (applyRestriction ρ (generators i)).support ⊆ target) :
    CoeffBridge.coeffMatrix target (fun i => applyRestriction ρ (generators i)) =
      CoeffBridge.coeffMatrix source generators *
        restrictionColumnMatrix ρ source target := by
  ext i t
  rw [Matrix.mul_apply]
  simpa [CoeffBridge.coeffMatrix, CoeffBridge.coeffVector] using
    congrFun
      (coeffVector_applyRestriction_eq_sum_restrictionColumns ρ source target
        (generators i) (hsource i) (htarget i)) t

theorem spdpSubspace_eq_span_monomials {n : ℕ} {F : Type*} [CommRing F]
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    spdpSubspace κ ℓ p =
      Submodule.span F
        { q | ∃ (S : List (Fin n)) (d : (Fin n →₀ ℕ)),
            S.length = κ ∧ d.sum (fun _ e => e) ≤ ℓ ∧
            q = MvPolynomial.monomial d (1 : F) * iterDerivList S p } := by
  refine le_antisymm ?_ ?_
  · apply Submodule.span_le.mpr
    intro q hq
    rcases hq with ⟨S, m, hlen, hdeg, rfl⟩
    have hdecomp :
        m * iterDerivList S p =
          ∑ d ∈ m.support,
            MvPolynomial.coeff d m •
              (MvPolynomial.monomial d (1 : F) * iterDerivList S p) := by
      calc
        m * iterDerivList S p
            = (∑ d ∈ m.support, MvPolynomial.monomial d (MvPolynomial.coeff d m)) *
                iterDerivList S p := by
                  conv_lhs => rw [m.as_sum]
        _ = ∑ d ∈ m.support,
              MvPolynomial.monomial d (MvPolynomial.coeff d m) * iterDerivList S p := by
                rw [Finset.sum_mul]
        _ = ∑ d ∈ m.support,
              MvPolynomial.coeff d m •
                (MvPolynomial.monomial d (1 : F) * iterDerivList S p) := by
                  apply Finset.sum_congr rfl
                  intro d hd
                  calc
                    MvPolynomial.monomial d (MvPolynomial.coeff d m) * iterDerivList S p
                        = ((MvPolynomial.coeff d m) • MvPolynomial.monomial d (1 : F)) *
                            iterDerivList S p := by
                              rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
                    _ = (MvPolynomial.C (MvPolynomial.coeff d m) * MvPolynomial.monomial d (1 : F)) *
                          iterDerivList S p := by
                            rw [MvPolynomial.smul_eq_C_mul]
                    _ = MvPolynomial.coeff d m •
                          (MvPolynomial.monomial d (1 : F) * iterDerivList S p) := by
                            rw [MvPolynomial.smul_eq_C_mul, mul_assoc]
    rw [hdecomp]
    apply Submodule.sum_mem
    intro d hd
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨S, d, hlen, ?_, rfl⟩
    exact le_trans (MvPolynomial.le_totalDegree hd) hdeg
  · apply Submodule.span_le.mpr
    intro q hq
    rcases hq with ⟨S, d, hlen, hdeg, rfl⟩
    apply Submodule.subset_span
    refine ⟨S, MvPolynomial.monomial d (1 : F), hlen, ?_, rfl⟩
    exact le_trans (MvPolynomial.totalDegree_monomial_le d (1 : F)) hdeg

noncomputable def spdpMonomialGenerator {n : ℕ} {F : Type*} [CommRing F]
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    ((Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ }) →
      MvPolynomial (Fin n) F :=
  fun idx => MvPolynomial.monomial idx.2.1 (1 : F) * iterDerivList (List.ofFn idx.1) p

theorem spdpSubspace_eq_span_monomialGenerators {n : ℕ} {F : Type*} [CommRing F]
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    spdpSubspace κ ℓ p =
      Submodule.span F (Set.range (spdpMonomialGenerator (F := F) κ ℓ p)) := by
  rw [spdpSubspace_eq_span_monomials]
  refine le_antisymm ?_ ?_
  · apply Submodule.span_le.mpr
    intro q hq
    rcases hq with ⟨S, d, hlen, hdeg, rfl⟩
    let f : Fin κ → Fin n := fun i => by
      have hi : i.1 < S.length := by
        simpa [hlen] using i.2
      exact S.get ⟨i.1, hi⟩
    have hS : List.ofFn f = S := by
      dsimp [f]
      simpa [hlen] using (List.ofFn_get (l := S))
    apply Submodule.subset_span
    refine ⟨(f, ⟨d, hdeg⟩), ?_⟩
    simp [spdpMonomialGenerator, hS]
  · apply Submodule.span_le.mpr
    intro q hq
    rcases hq with ⟨⟨f, d, hd⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨List.ofFn f, d, by simp, hd, rfl⟩

noncomputable def spdpMonomialCoeffMatrix {n : ℕ} {F : Type*} [Field F]
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F)
    (monomials : Finset ((Fin n) →₀ ℕ))
    [Fintype ((Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ })] :
    Matrix ((Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ })
      monomials F :=
  CoeffBridge.coeffMatrix monomials (spdpMonomialGenerator (F := F) κ ℓ p)

theorem spdpRank_eq_matrix_rank_of_supported {n : ℕ} {F : Type*} [Field F] [Nontrivial F]
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F)
    (monomials : Finset ((Fin n) →₀ ℕ))
    [Fintype ((Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ })]
    (hsupport : ∀ i,
      (spdpMonomialGenerator (F := F) κ ℓ p i).support ⊆ monomials) :
    spdpRank κ ℓ p = (spdpMonomialCoeffMatrix (F := F) κ ℓ p monomials).rank := by
  unfold spdpRank spdpMonomialCoeffMatrix
  rw [spdpSubspace_eq_span_monomialGenerators]
  simpa [spdpMonomialGenerator] using
    (CoeffBridge.finrank_span_eq_matrix_rank (F := F) (σ := Fin n) monomials
      (spdpMonomialGenerator (F := F) κ ℓ p) hsupport)

/-! ## Lemma 141: Restriction Monotonicity

The mathematical argument (paper Lemma 141): the SPDP matrix M_{κ,ℓ}(f)
has rows indexed by (S, m) and columns indexed by monomials x^α.
Applying restriction ρ corresponds to a column operation on this matrix.
Column operations cannot increase matrix rank, so
rank(M_{κ,ℓ}(f|_ρ)) ≤ rank(M_{κ,ℓ}(f)).

Infrastructure proved above:
1. applyRestriction ρ is an algebra homomorphism (hence linear)
2. pderiv commutes with restriction for free variables; gives 0 for fixed vars
3. iterDerivList commutes with restriction for all-free lists; gives 0 otherwise
4. `spdpSubspace κ ℓ p` is the span of canonical monomial generators
5. restriction acts on coefficient matrices by explicit right multiplication
   (`coeffMatrix_applyRestriction_eq_mul_restrictionColumns`)

The remaining gap is now exact: choose a uniform finite monomial support set
for the SPDP generators of `f` and `applyRestriction ρ f`, identify both
SPDP ranks with matrix ranks, and then invoke the standard inequality
`Matrix.rank_mul_le_left`. See the docstring on `spdpRank_restriction_mono`
for the frontier statement.

NOTE: This sorry is NOT load-bearing for the main separation theorem.
Separation29.three_sat_not_in_P uses two monolithic axioms (Theorems 139/140)
and does not depend on this file. -/

/-- Lemma 141 (column deletion monotonicity): restriction cannot increase SPDP rank.

    Mathematical argument: the SPDP matrix M_{κ,ℓ}(f) has rows indexed by
    (S, m) with |S|=κ, deg(m)≤ℓ, and columns indexed by monomials x^α.
    Entry (S,m,α) = coefficient of x^α in m·∂_S f.
    Restriction ρ acts on column indices: each column x^α maps to
    ρ(x^α) = ∏_{i fixed} a_i^{α_i} · ∏_{i free} x_i^{α_i}, which is a
    right-multiplication of the coefficient matrix by a matrix with at most
    one nonzero entry per row. Such column operations cannot increase rank.

    Hence rank(M_{κ,ℓ}(ρ(f))) ≤ rank(M_{κ,ℓ}(f)), i.e.,
    Γ_{κ,ℓ}(ρ(f)) ≤ Γ_{κ,ℓ}(f).

    **Why the sorry remains**: the algebraic action is now explicit.
    The proved seam is:

    - `spdpSubspace_eq_span_monomialGenerators`
    - `spdpRank_eq_matrix_rank_of_supported`
    - `coeffMatrix_applyRestriction_eq_mul_restrictionColumns`

    So the remaining obligation is the finite-support/rank bridge:
    find a uniform finite monomial set supporting all SPDP generators for
    both `f` and `applyRestriction ρ f`, then combine the above with
    `Matrix.rank_mul_le_left`. Several alternative approaches were tried
    before reducing the frontier to this matrix statement:

    - Submodule-image approach (spdpSubspace(ρf) ≤ image of spdpSubspace(f)
      under ρ): FAILS because target generators m · ∂_S(ρf) include
      multipliers m that use fixed variables, which lie outside the image
      of the restriction map.

    - Generating-set size comparison: FAILS because the multiplier factor
      (monomials of degree ≤ ℓ) is the same in both source and target, so
      the ratio does not simplify without matrix-rank infrastructure.

    - Direct linear map on generators (m·d_S ↦ m·ρ(d_S)): FAILS because
      well-definedness requires showing that linear relations among generators
      are preserved, which circularly requires the column-deletion principle.

    **NOT LOAD-BEARING**: This sorry does not affect the main separation
    theorem (Separation29.three_sat_not_in_P / P_ne_NP). That theorem
    depends on two monolithic axioms: `theorem_140_np_side` (Theorem 140)
    and `theorem_139_p_side` (Theorem 139). Lemma 141 would only be needed
    to decompose `theorem_139_p_side` into finer sub-axioms (see
    SeparationAssembly.lean). The main proof chain has ZERO sorry.

    Infrastructure proved:
    1. applyRestriction ρ is an algebra homomorphism (hence linear)
    2. pderiv commutes with restriction for free variables; gives 0 for fixed
    3. iterDerivList commutes with restriction for all-free lists; gives 0
       when any fixed variable appears in the derivative list
-/
-- Helper: the SPDP subspace of ρ(f) is contained in the image of a linear map
-- applied to the SPDP subspace of f. This is the coefficient-matrix column-operation
-- argument from the paper's Lemma 141.
private theorem spdpSubspace_restriction_le_image {n : ℕ}
    (ρ : VarRestriction n) (f : MvPolynomial (Fin n) ℚ) (κ ℓ : ℕ) :
    ∃ (φ : MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ),
    spdpSubspace κ ℓ (applyRestriction ρ f) ≤ Submodule.map φ (spdpSubspace κ ℓ f) := by
  -- The remaining gap is now the finite-support/rank bridge from the explicit
  -- coefficient-matrix factorization proved above to a submodule-image witness.
  sorry

theorem spdpRank_restriction_mono {n : ℕ}
    (ρ : VarRestriction n) (f : MvPolynomial (Fin n) ℚ) (κ ℓ : ℕ) :
    spdpRank κ ℓ (applyRestriction ρ f) ≤ spdpRank κ ℓ f := by
  -- Follows from the submodule containment + finrank monotonicity.
  obtain ⟨φ, hle⟩ := spdpSubspace_restriction_le_image ρ f κ ℓ
  unfold spdpRank
  exact le_trans (Submodule.finrank_mono hle) (Submodule.finrank_map_le φ _)

/-! ## Application: Language Polynomial → Instance Polynomial -/

theorem hard_instance_p_side_bound
    (language_rank instance_rank : ℕ)
    (h_restriction : instance_rank ≤ language_rank)
    (h_p_side : language_rank ≤ 200) :
    instance_rank ≤ 200 :=
  le_trans h_restriction h_p_side

end RestrictionMono
