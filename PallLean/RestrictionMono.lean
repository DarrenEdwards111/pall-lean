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
import PallLean.CoeffMatrixHelpers
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

theorem applyRestriction_vars_subset_freeVars {n : ℕ} (ρ : VarRestriction n)
    (f : MvPolynomial (Fin n) ℚ) :
    (applyRestriction ρ f).vars ⊆ ρ.freeVars := by
  intro x hx
  rw [applyRestriction_eq_algHom, applyRestrictionAlgHom] at hx
  rcases MvPolynomial.mem_vars_bind₁ (restrictionFun ρ) f hx with ⟨i, -, hxi⟩
  by_cases hi : i ∈ ρ.fixedVars
  · simp [restrictionFun, hi] at hxi
  · have hi_free : i ∈ ρ.freeVars := by
      have hi_union : i ∈ ρ.fixedVars ∪ ρ.freeVars := by
        simp [ρ.partition]
      rcases Finset.mem_union.mp hi_union with hi_fixed | hi_free
      · exact (hi.elim hi_fixed)
      · exact hi_free
    have hxi_eq : x = i := by
      simpa [restrictionFun, hi] using hxi
    subst x
    exact hi_free

theorem mem_freeVars_of_mem_vars_applyRestriction {n : ℕ} (ρ : VarRestriction n)
    (f : MvPolynomial (Fin n) ℚ) {x : Fin n}
    (hx : x ∈ (applyRestriction ρ f).vars) :
    x ∈ ρ.freeVars :=
  applyRestriction_vars_subset_freeVars ρ f hx

theorem support_subset_freeVars_of_mem_applyRestriction_support {n : ℕ}
    (ρ : VarRestriction n) (f : MvPolynomial (Fin n) ℚ)
    {m : Fin n →₀ ℕ}
    (hm : m ∈ (applyRestriction ρ f).support) :
    m.support ⊆ ρ.freeVars := by
  intro x hx
  exact mem_freeVars_of_mem_vars_applyRestriction ρ f
    ((MvPolynomial.mem_vars x).mpr ⟨m, hm, hx⟩)

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

theorem applyRestriction_monomial_of_support_subset_free_coeff {n : ℕ}
    (ρ : VarRestriction n) (d : Fin n →₀ ℕ) (c : ℚ)
    (hd : d.support ⊆ ρ.freeVars) :
    applyRestriction ρ (MvPolynomial.monomial d c) =
      MvPolynomial.monomial d c := by
  rw [show MvPolynomial.monomial d c =
      MvPolynomial.C c * MvPolynomial.monomial d (1 : ℚ) by
        simp [MvPolynomial.C_mul_monomial]]
  rw [applyRestriction_mul, applyRestriction_monomial_of_support_subset_free ρ d hd]
  simp [applyRestriction_eq_algHom]

theorem applyRestriction_eq_self_of_vars_subset_free {n : ℕ}
    (ρ : VarRestriction n) (m : MvPolynomial (Fin n) ℚ)
    (hm : m.vars ⊆ ρ.freeVars) :
    applyRestriction ρ m = m := by
  conv_lhs => rw [m.as_sum]
  conv_rhs => rw [m.as_sum]
  rw [applyRestriction_eq_algHom, applyRestrictionAlgHom, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdfree : d.support ⊆ ρ.freeVars := by
    intro x hx
    exact hm ((MvPolynomial.mem_vars x).mpr ⟨d, hd, hx⟩)
  exact applyRestriction_monomial_of_support_subset_free_coeff ρ d (MvPolynomial.coeff d m) hdfree

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

/-! ## Degree-bounded columns and restriction action on coefficient vectors -/

noncomputable def monomialsLE (n D : ℕ) : Finset ((Fin n) →₀ ℕ) :=
  (Finset.range (D + 1)).biUnion fun k =>
    (Finset.univ : Finset (Fin n)).finsuppAntidiag k

/-- Degree-bounded monomials whose support stays inside the free variables of `ρ`. -/
noncomputable def freeMonomialsLE {n : ℕ}
    (ρ : VarRestriction n) (D : ℕ) : Finset ((Fin n) →₀ ℕ) :=
  (monomialsLE n D).filter fun d => d.support ⊆ ρ.freeVars

/-- SPDP generator indices whose derivative list and multiplier monomial both stay
inside the free variables of `ρ`. -/
def FreeSpdpGeneratorIdx {n : ℕ} (ρ : VarRestriction n) (κ ℓ : ℕ) :=
  { i : ((Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ }) //
      (∀ j, i.1 j ∈ ρ.freeVars) ∧ i.2.1.support ⊆ ρ.freeVars }

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

theorem mem_freeMonomialsLE {n D : ℕ} (ρ : VarRestriction n) {d : (Fin n) →₀ ℕ} :
    d ∈ freeMonomialsLE ρ D ↔ d.sum (fun _ e => e) ≤ D ∧ d.support ⊆ ρ.freeVars := by
  simp [freeMonomialsLE, mem_monomialsLE]

private noncomputable def boundedDegreeMonomialEquiv {n D : ℕ} :
    { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ D } ≃ monomialsLE n D where
  toFun d := ⟨d.1, (mem_monomialsLE).2 d.2⟩
  invFun d := ⟨d.1, (mem_monomialsLE).1 d.2⟩
  left_inv d := by
    cases d
    rfl
  right_inv d := by
    cases d
    rfl

private noncomputable instance boundedDegreeMonomialFintype {n D : ℕ} :
    Fintype { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ D } :=
  Fintype.ofEquiv (monomialsLE n D) boundedDegreeMonomialEquiv.symm

noncomputable def restrictionColumnMatrix {n : ℕ}
    (ρ : VarRestriction n)
    (source target : Finset ((Fin n) →₀ ℕ)) :
    Matrix source target ℚ :=
  CoeffMatrixHelpers.monomialActionMatrix source target
    (applyRestrictionAlgHom ρ).toLinearMap

theorem coeffVector_applyRestriction_eq_sum_restrictionColumns {n : ℕ}
    (ρ : VarRestriction n)
    (source target : Finset ((Fin n) →₀ ℕ))
    (p : MvPolynomial (Fin n) ℚ)
    (hsource : p.support ⊆ source)
    (_htarget : (applyRestriction ρ p).support ⊆ target) :
    CoeffMatrixHelpers.coeffVector target (applyRestriction ρ p) =
      fun t =>
        ∑ s : source,
          CoeffMatrixHelpers.coeffVector source p s *
            restrictionColumnMatrix ρ source target s t := by
  ext t
  simpa [restrictionColumnMatrix, CoeffMatrixHelpers.coeffVector, applyRestriction_eq_algHom] using
    CoeffMatrixHelpers.coeff_apply_eq_sum_monomialActionMatrix
      (σ := Fin n) (F := ℚ) source
      (applyRestrictionAlgHom ρ).toLinearMap p hsource t.1

private theorem support_subset_monomialsLE_of_totalDegree_le {n D : ℕ}
    (p : MvPolynomial (Fin n) ℚ) (hdeg : p.totalDegree ≤ D) :
    p.support ⊆ monomialsLE n D := by
  intro d hd
  rw [mem_monomialsLE]
  exact le_trans (MvPolynomial.le_totalDegree hd) hdeg

private theorem applyRestriction_totalDegree_le {n : ℕ}
    (ρ : VarRestriction n) (p : MvPolynomial (Fin n) ℚ) :
    (applyRestriction ρ p).totalDegree ≤ p.totalDegree := by
  rw [applyRestriction_eq_algHom, applyRestrictionAlgHom]
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply le_trans (MvPolynomial.totalDegree_finset_sum _ _)
  apply Finset.sup_le
  intro d hd
  rw [MvPolynomial.aeval_monomial]
  have hprod :
      (d.prod fun i e => restrictionFun ρ i ^ e).totalDegree ≤ d.sum fun _ e => e := by
    unfold Finsupp.prod
    refine le_trans (MvPolynomial.totalDegree_finset_prod _ _) ?_
    refine Finset.sum_le_sum ?_
    intro i hi
    have hone : (restrictionFun ρ i).totalDegree ≤ 1 := by
      by_cases hfixed : i ∈ ρ.fixedVars
      · simp [restrictionFun, hfixed, MvPolynomial.totalDegree_C]
      · simp [restrictionFun, hfixed, MvPolynomial.totalDegree_X]
    calc
      ((restrictionFun ρ i) ^ d i).totalDegree
          ≤ d i * (restrictionFun ρ i).totalDegree := MvPolynomial.totalDegree_pow _ _
      _ ≤ d i * 1 := Nat.mul_le_mul_left _ hone
      _ = d i := by omega
  have hcoeff :
      (((algebraMap ℚ (MvPolynomial (Fin n) ℚ)) (MvPolynomial.coeff d p)).totalDegree) ≤ 0 := by
    simp [MvPolynomial.totalDegree_C]
  calc
    (((algebraMap ℚ (MvPolynomial (Fin n) ℚ)) (MvPolynomial.coeff d p)) *
        d.prod (fun i k => restrictionFun ρ i ^ k)).totalDegree
        ≤ (((algebraMap ℚ (MvPolynomial (Fin n) ℚ)) (MvPolynomial.coeff d p)).totalDegree) +
            (d.prod (fun i k => restrictionFun ρ i ^ k)).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + d.sum (fun _ e => e) := Nat.add_le_add hcoeff hprod
    _ = d.sum (fun _ e => e) := by omega
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hd

theorem coeffMatrix_applyRestriction_eq_mul_restrictionColumns
    {n ι : ℕ}
    (ρ : VarRestriction n)
    (source target : Finset ((Fin n) →₀ ℕ))
    (generators : Fin ι → MvPolynomial (Fin n) ℚ)
    (hsource : ∀ i, (generators i).support ⊆ source)
    (htarget : ∀ i, (applyRestriction ρ (generators i)).support ⊆ target) :
    CoeffMatrixHelpers.coeffMatrix target (fun i => applyRestriction ρ (generators i)) =
      CoeffMatrixHelpers.coeffMatrix source generators *
        restrictionColumnMatrix ρ source target := by
  ext i t
  rw [Matrix.mul_apply]
  simpa [CoeffMatrixHelpers.coeffMatrix, CoeffMatrixHelpers.coeffVector] using
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

private theorem applyRestriction_spdpMonomialGenerator_of_free {n : ℕ}
    (ρ : VarRestriction n) (f : MvPolynomial (Fin n) ℚ)
    (κ ℓ : ℕ)
    (idx : (Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ })
    (hSfree : ∀ i, idx.1 i ∈ ρ.freeVars)
    (hdfree : idx.2.1.support ⊆ ρ.freeVars) :
    applyRestriction ρ (spdpMonomialGenerator (F := ℚ) κ ℓ f idx) =
      spdpMonomialGenerator (F := ℚ) κ ℓ (applyRestriction ρ f) idx := by
  rcases idx with ⟨S, d, hd⟩
  simp only [spdpMonomialGenerator]
  rw [applyRestriction_mul,
    applyRestriction_monomial_of_support_subset_free ρ d hdfree,
    iterDerivList_applyRestriction_free ρ (List.ofFn S)]
  · intro v hv
    rw [List.mem_ofFn'] at hv
    rcases hv with ⟨i, rfl⟩
    exact hSfree i

private theorem free_spdpMonomialGenerator_mem_restriction_map {n : ℕ}
    (ρ : VarRestriction n) (f : MvPolynomial (Fin n) ℚ)
    (κ ℓ : ℕ)
    (idx : (Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ })
    (hSfree : ∀ i, idx.1 i ∈ ρ.freeVars)
    (hdfree : idx.2.1.support ⊆ ρ.freeVars) :
    spdpMonomialGenerator (F := ℚ) κ ℓ (applyRestriction ρ f) idx ∈
      Submodule.map (applyRestrictionAlgHom ρ).toLinearMap (spdpSubspace κ ℓ f) := by
  rcases idx with ⟨S, d, hd⟩
  simpa [spdpMonomialGenerator] using
    free_monomial_generator_mem_restriction_map ρ f κ ℓ (List.ofFn S) d
      (by simp) (by
        intro v hv
        rw [List.mem_ofFn'] at hv
        rcases hv with ⟨i, rfl⟩
        exact hSfree i) hd hdfree

private theorem spdpMonomialGenerator_totalDegree_le {n : ℕ}
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    (i : (Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ }) :
    (spdpMonomialGenerator κ ℓ p i : MvPolynomial (Fin n) ℚ).totalDegree ≤
      ℓ + p.totalDegree := by
  rcases i with ⟨S, d, hd⟩
  change (MvPolynomial.monomial d (1 : ℚ) * iterDerivList (List.ofFn S) p).totalDegree ≤
    ℓ + p.totalDegree
  exact le_trans (MvPolynomial.totalDegree_mul _ _)
    (Nat.add_le_add
      (le_trans (MvPolynomial.totalDegree_monomial_le d (1 : ℚ)) hd)
      (SPDP.totalDegree_iterDerivList_le (List.ofFn S) p))

private theorem spdpMonomialGenerator_support_subset_monomialsLE {n : ℕ}
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    (i : (Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ }) :
    (spdpMonomialGenerator κ ℓ p i : MvPolynomial (Fin n) ℚ).support ⊆
      monomialsLE n (ℓ + p.totalDegree) :=
  support_subset_monomialsLE_of_totalDegree_le _
    (spdpMonomialGenerator_totalDegree_le κ ℓ p i)

private theorem restrictedSpdpMonomialGenerator_support_subset_monomialsLE {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    (i : (Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ }) :
    (spdpMonomialGenerator κ ℓ (applyRestriction ρ p) i : MvPolynomial (Fin n) ℚ).support ⊆
      monomialsLE n (ℓ + p.totalDegree) := by
  apply support_subset_monomialsLE_of_totalDegree_le
  exact le_trans (spdpMonomialGenerator_totalDegree_le κ ℓ (applyRestriction ρ p) i)
    (Nat.add_le_add_left (applyRestriction_totalDegree_le ρ p) ℓ)

private theorem restrictedSourceSpdpMonomialGenerator_support_subset_monomialsLE {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    (i : (Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ }) :
    (applyRestriction ρ (spdpMonomialGenerator κ ℓ p i) : MvPolynomial (Fin n) ℚ).support ⊆
      monomialsLE n (ℓ + p.totalDegree) := by
  apply support_subset_monomialsLE_of_totalDegree_le
  exact le_trans (applyRestriction_totalDegree_le ρ (spdpMonomialGenerator κ ℓ p i))
    (spdpMonomialGenerator_totalDegree_le κ ℓ p i)

theorem restrictedSpdpMonomialGenerator_support_subset_freeMonomialsLE {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    (i : FreeSpdpGeneratorIdx ρ κ ℓ) :
    (spdpMonomialGenerator κ ℓ (applyRestriction ρ p) i.1 : MvPolynomial (Fin n) ℚ).support ⊆
      freeMonomialsLE ρ (ℓ + p.totalDegree) := by
  rcases i with ⟨i, hSfree, hdfree⟩
  intro m hm
  refine (mem_freeMonomialsLE ρ).2 ?_
  constructor
  · simpa [mem_monomialsLE] using
      restrictedSpdpMonomialGenerator_support_subset_monomialsLE ρ κ ℓ p i hm
  · have hm' : m ∈
        (applyRestriction ρ (spdpMonomialGenerator κ ℓ p i) : MvPolynomial (Fin n) ℚ).support := by
      simpa [applyRestriction_spdpMonomialGenerator_of_free ρ p κ ℓ i hSfree hdfree] using hm
    exact support_subset_freeVars_of_mem_applyRestriction_support ρ
      (spdpMonomialGenerator κ ℓ p i) hm'

private theorem applyRestriction_spdpMonomialGenerator {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    (i : (Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ }) :
    applyRestriction ρ (spdpMonomialGenerator κ ℓ p i) =
      applyRestriction ρ (MvPolynomial.monomial i.2.1 (1 : ℚ)) *
        applyRestriction ρ (iterDerivList (List.ofFn i.1) p) := by
  rcases i with ⟨S, d, hd⟩
  simp [spdpMonomialGenerator, applyRestriction_mul]

private theorem restrictedSpdpMonomialGenerator_eq_if_free {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    (i : (Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ }) :
    spdpMonomialGenerator κ ℓ (applyRestriction ρ p) i =
      MvPolynomial.monomial i.2.1 (1 : ℚ) *
        (if ∀ v ∈ List.ofFn i.1, v ∈ ρ.freeVars
         then applyRestriction ρ (iterDerivList (List.ofFn i.1) p)
         else 0) := by
  rcases i with ⟨S, d, hd⟩
  simp [spdpMonomialGenerator, iterDerivList_applyRestriction]

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
        have hik : i.1 < κ := i.2
        omega
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
  CoeffMatrixHelpers.coeffMatrix monomials (spdpMonomialGenerator (F := F) κ ℓ p)

theorem spdpRank_eq_matrix_rank_of_supported {n : ℕ} {F : Type*} [Field F] [Nontrivial F]
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F)
    (monomials : Finset ((Fin n) →₀ ℕ))
    [Fintype ((Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ })]
    (hsupport : ∀ i,
      (spdpMonomialGenerator (F := F) κ ℓ p i).support ⊆ monomials) :
    spdpRank κ ℓ p = (spdpMonomialCoeffMatrix (F := F) κ ℓ p monomials).rank := by
  unfold spdpRank spdpMonomialCoeffMatrix
  rw [spdpSubspace_eq_span_monomialGenerators]
  exact CoeffMatrixHelpers.finrank_span_eq_matrix_rank (F := F) (σ := Fin n) monomials
    (spdpMonomialGenerator (F := F) κ ℓ p) hsupport

private theorem spdpRank_eq_matrix_rank_monomialsLE {n : ℕ}
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    [Fintype ((Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ })] :
    spdpRank κ ℓ p =
      (spdpMonomialCoeffMatrix (F := ℚ) κ ℓ p
        (monomialsLE n (ℓ + p.totalDegree))).rank := by
  apply spdpRank_eq_matrix_rank_of_supported
  intro i
  exact spdpMonomialGenerator_support_subset_monomialsLE κ ℓ p i

private theorem restrictedSpdpRank_eq_matrix_rank_monomialsLE {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    [Fintype ((Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ })] :
    spdpRank κ ℓ (applyRestriction ρ p) =
      (spdpMonomialCoeffMatrix (F := ℚ) κ ℓ (applyRestriction ρ p)
        (monomialsLE n (ℓ + p.totalDegree))).rank := by
  exact spdpRank_eq_matrix_rank_of_supported (F := ℚ) κ ℓ (applyRestriction ρ p)
    (monomialsLE n (ℓ + p.totalDegree))
    (fun i => restrictedSpdpMonomialGenerator_support_subset_monomialsLE ρ κ ℓ p i)

private theorem restrictedSourceSpdpCoeffMatrix_rank_le {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    [Fintype ((Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ })] :
    let monomials := monomialsLE n (ℓ + p.totalDegree)
    (CoeffMatrixHelpers.coeffMatrix monomials
      (fun i => applyRestriction ρ (spdpMonomialGenerator (F := ℚ) κ ℓ p i))).rank ≤
        spdpRank κ ℓ p := by
  let monomials := monomialsLE n (ℓ + p.totalDegree)
  have hsupport :
      ∀ i,
        (spdpMonomialGenerator (F := ℚ) κ ℓ p i).support ⊆ monomials := by
    intro i
    simpa [monomials] using spdpMonomialGenerator_support_subset_monomialsLE κ ℓ p i
  calc
    (CoeffMatrixHelpers.coeffMatrix monomials
      (fun i => applyRestriction ρ (spdpMonomialGenerator (F := ℚ) κ ℓ p i))).rank
        ≤ (CoeffMatrixHelpers.coeffMatrix monomials
            (spdpMonomialGenerator (F := ℚ) κ ℓ p)).rank := by
          simpa [CoeffMatrixHelpers.coeffMatrix, monomials, applyRestriction_eq_algHom] using
            CoeffMatrixHelpers.rank_coeffMatrix_map_le
              (σ := Fin n) (F := ℚ) monomials monomials
              (applyRestrictionAlgHom ρ).toLinearMap
              (spdpMonomialGenerator (F := ℚ) κ ℓ p) hsupport
    _ = spdpRank κ ℓ p := by
      symm
      exact spdpRank_eq_matrix_rank_monomialsLE κ ℓ p

/-- The restriction image of the SPDP subspace is exactly the span of the
restricted canonical SPDP generators. -/
theorem restriction_image_spdpSubspace_eq_span_restrictedGenerators {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    [Fintype ((Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ })] :
    Submodule.map (applyRestrictionAlgHom ρ).toLinearMap (spdpSubspace κ ℓ p) =
      Submodule.span ℚ
        (Set.range (fun i =>
          applyRestriction ρ (spdpMonomialGenerator (F := ℚ) κ ℓ p i))) := by
  rw [spdpSubspace_eq_span_monomialGenerators, Submodule.map_span]
  congr 1
  ext q
  constructor
  · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨spdpMonomialGenerator (F := ℚ) κ ℓ p i, ⟨i, rfl⟩, rfl⟩

/-- Finite-support bridge for the restriction image: its dimension is exactly
the rank of the coefficient matrix of the restricted canonical generators over
the bounded monomial universe. -/
theorem restriction_image_spdpSubspace_finrank_eq_restrictedSourceCoeffMatrix_rank {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    [Fintype ((Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ })] :
    let monomials := monomialsLE n (ℓ + p.totalDegree)
    Module.finrank ℚ
        (Submodule.map (applyRestrictionAlgHom ρ).toLinearMap (spdpSubspace κ ℓ p)) =
      (CoeffMatrixHelpers.coeffMatrix monomials
        (fun i => applyRestriction ρ (spdpMonomialGenerator (F := ℚ) κ ℓ p i))).rank := by
  let monomials := monomialsLE n (ℓ + p.totalDegree)
  rw [restriction_image_spdpSubspace_eq_span_restrictedGenerators]
  exact CoeffMatrixHelpers.finrank_span_eq_matrix_rank (F := ℚ) (σ := Fin n) monomials
    (fun i => applyRestriction ρ (spdpMonomialGenerator (F := ℚ) κ ℓ p i))
    (fun i => by
      simpa [monomials] using
        restrictedSourceSpdpMonomialGenerator_support_subset_monomialsLE ρ κ ℓ p i)

/-- Restriction sends the SPDP subspace into a finite-dimensional image whose
dimension is bounded by the original SPDP rank. -/
theorem restriction_image_spdpSubspace_finrank_le_spdpRank {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) :
    Module.finrank ℚ
        (Submodule.map (applyRestrictionAlgHom ρ).toLinearMap (spdpSubspace κ ℓ p)) ≤
      spdpRank κ ℓ p := by
  calc
    Module.finrank ℚ
        (Submodule.map (applyRestrictionAlgHom ρ).toLinearMap (spdpSubspace κ ℓ p))
      = let monomials := monomialsLE n (ℓ + p.totalDegree)
        (CoeffMatrixHelpers.coeffMatrix monomials
          (fun i => applyRestriction ρ (spdpMonomialGenerator (F := ℚ) κ ℓ p i))).rank := by
            exact restriction_image_spdpSubspace_finrank_eq_restrictedSourceCoeffMatrix_rank
              ρ κ ℓ p
    _ ≤ spdpRank κ ℓ p := by
      exact restrictedSourceSpdpCoeffMatrix_rank_le ρ κ ℓ p

/-- The paper-faithful target SPDP subspace generated by derivative lists and
multiplier monomials supported only on the free variables of `ρ`. -/
noncomputable def freeRestrictedSpdpSubspace {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  Submodule.span ℚ
    { q | ∃ i : ((Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ }),
        (∀ j, i.1 j ∈ ρ.freeVars) ∧
        i.2.1.support ⊆ ρ.freeVars ∧
        q = spdpMonomialGenerator (F := ℚ) κ ℓ (applyRestriction ρ p) i }

/-- Typed index family for the free-variable-only target SPDP generators. -/
abbrev freeRestrictedSpdpGeneratorIdx {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) :=
  FreeSpdpGeneratorIdx ρ κ ℓ

noncomputable instance instDecidableEqFreeRestrictedSpdpGeneratorIdx {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) :
    DecidableEq (freeRestrictedSpdpGeneratorIdx ρ κ ℓ) :=
  by
    classical
    exact Classical.decEq _

noncomputable instance freeRestrictedSpdpGeneratorIdxFintype {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ)
    [Fintype ((Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ })] :
    Fintype (freeRestrictedSpdpGeneratorIdx ρ κ ℓ) :=
  by
    classical
    exact Fintype.ofInjective
      (fun i : freeRestrictedSpdpGeneratorIdx ρ κ ℓ => i.1)
      (by
        intro a b h
        exact Subtype.ext h)

/-- Canonical generator family spanning `freeRestrictedSpdpSubspace`. -/
noncomputable def freeRestrictedSpdpGenerator {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) :
    freeRestrictedSpdpGeneratorIdx ρ κ ℓ → MvPolynomial (Fin n) ℚ :=
  fun i => spdpMonomialGenerator (F := ℚ) κ ℓ (applyRestriction ρ p) i.1

/-- The existential definition of `freeRestrictedSpdpSubspace` is exactly the
span of its typed free-variable-only generator family. -/
theorem freeRestrictedSpdpSubspace_eq_span_generators {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    [Fintype ((Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ })] :
    freeRestrictedSpdpSubspace ρ κ ℓ p =
      Submodule.span ℚ
        (Set.range (freeRestrictedSpdpGenerator ρ κ ℓ p)) := by
  unfold freeRestrictedSpdpSubspace freeRestrictedSpdpGenerator
  congr 1
  ext q
  constructor
  · rintro ⟨i, hSfree, hdfree, rfl⟩
    exact ⟨⟨i, hSfree, hdfree⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.1, i.2.1, i.2.2, rfl⟩

noncomputable instance freeRestrictedSpdpSubspaceModuleFinite {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    [Fintype ((Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ })] :
    Module.Finite ℚ (freeRestrictedSpdpSubspace ρ κ ℓ p) := by
  rw [Module.Finite.iff_fg, freeRestrictedSpdpSubspace_eq_span_generators]
  exact Submodule.fg_span (Set.finite_range _)

private theorem freeRestrictedSpdpGenerator_support_subset_freeMonomialsLE {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    (i : freeRestrictedSpdpGeneratorIdx ρ κ ℓ) :
    (freeRestrictedSpdpGenerator ρ κ ℓ p i).support ⊆
      freeMonomialsLE ρ (ℓ + p.totalDegree) := by
  exact restrictedSpdpMonomialGenerator_support_subset_freeMonomialsLE ρ κ ℓ p i

/-- Finite-support bridge for the paper-faithful target subspace: over the
bounded monomial universe, its dimension is exactly the coefficient-matrix rank
of the free-variable-only target generators. -/
theorem freeRestrictedSpdpSubspace_finrank_eq_coeffMatrix_rank {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    [Fintype ((Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ })] :
    let monomials := freeMonomialsLE ρ (ℓ + p.totalDegree)
    Module.finrank ℚ (freeRestrictedSpdpSubspace ρ κ ℓ p) =
      (CoeffMatrixHelpers.coeffMatrix monomials
        (freeRestrictedSpdpGenerator ρ κ ℓ p)).rank := by
  classical
  let monomials := freeMonomialsLE ρ (ℓ + p.totalDegree)
  rw [freeRestrictedSpdpSubspace_eq_span_generators]
  exact CoeffMatrixHelpers.finrank_span_eq_matrix_rank (F := ℚ) (σ := Fin n) monomials
    (freeRestrictedSpdpGenerator ρ κ ℓ p)
    (fun i => by
      simpa [monomials] using
        freeRestrictedSpdpGenerator_support_subset_freeMonomialsLE ρ κ ℓ p i)

/-- Over the free-variable-only bounded monomial universe, the honest target SPDP
generator matrix is the row/column submatrix of the restricted-source generator
matrix obtained by keeping only free generator rows and free-support columns. -/
theorem coeffMatrix_freeRestrictedSpdpGenerator_eq_submatrix_restrictedSource {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    [Fintype ((Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ })] :
    let monomials := monomialsLE n (ℓ + p.totalDegree)
    let freeMonomials := freeMonomialsLE ρ (ℓ + p.totalDegree)
    CoeffMatrixHelpers.coeffMatrix freeMonomials (freeRestrictedSpdpGenerator ρ κ ℓ p) =
      (CoeffMatrixHelpers.coeffMatrix monomials
        (fun i => applyRestriction ρ (spdpMonomialGenerator (F := ℚ) κ ℓ p i))).submatrix
          (fun i : freeRestrictedSpdpGeneratorIdx ρ κ ℓ => i.1)
          (fun m : freeMonomials => ⟨m.1, (Finset.mem_filter.mp m.2).1⟩) := by
  classical
  ext i m
  rcases i with ⟨i, hSfree, hdfree⟩
  simp [freeRestrictedSpdpGenerator, CoeffMatrixHelpers.coeffMatrix,
    applyRestriction_spdpMonomialGenerator_of_free ρ p κ ℓ i hSfree hdfree]

/-- The honest target coefficient matrix over free rows/columns is rank-bounded by the
restricted-source coefficient matrix on the ambient bounded monomial universe. -/
theorem freeRestrictedSpdpCoeffMatrix_rank_le_restrictedSource {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    [Fintype ((Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ })] :
    let monomials := monomialsLE n (ℓ + p.totalDegree)
    let freeMonomials := freeMonomialsLE ρ (ℓ + p.totalDegree)
    (CoeffMatrixHelpers.coeffMatrix freeMonomials
      (freeRestrictedSpdpGenerator ρ κ ℓ p)).rank ≤
      (CoeffMatrixHelpers.coeffMatrix monomials
        (fun i => applyRestriction ρ (spdpMonomialGenerator (F := ℚ) κ ℓ p i))).rank := by
  classical
  let monomials := monomialsLE n (ℓ + p.totalDegree)
  let freeMonomials := freeMonomialsLE ρ (ℓ + p.totalDegree)
  let rowMap : freeRestrictedSpdpGeneratorIdx ρ κ ℓ →
      ((Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ }) :=
    fun i => i.1
  let colMap : freeMonomials → monomials :=
    fun m => ⟨m.1, (Finset.mem_filter.mp m.2).1⟩
  change (CoeffMatrixHelpers.coeffMatrix freeMonomials
    (freeRestrictedSpdpGenerator ρ κ ℓ p)).rank ≤
      (CoeffMatrixHelpers.coeffMatrix monomials
        (fun i => applyRestriction ρ (spdpMonomialGenerator (F := ℚ) κ ℓ p i))).rank
  have hmatrix :
      CoeffMatrixHelpers.coeffMatrix freeMonomials (freeRestrictedSpdpGenerator ρ κ ℓ p) =
        (CoeffMatrixHelpers.coeffMatrix monomials
          (fun i => applyRestriction ρ (spdpMonomialGenerator (F := ℚ) κ ℓ p i))).submatrix
            rowMap colMap := by
    have h :=
      coeffMatrix_freeRestrictedSpdpGenerator_eq_submatrix_restrictedSource ρ κ ℓ p
    simpa [monomials, freeMonomials, rowMap, colMap] using h
  calc
    (CoeffMatrixHelpers.coeffMatrix freeMonomials
      (freeRestrictedSpdpGenerator ρ κ ℓ p)).rank
      = ((CoeffMatrixHelpers.coeffMatrix monomials
          (fun i => applyRestriction ρ (spdpMonomialGenerator (F := ℚ) κ ℓ p i))).submatrix
            rowMap colMap).rank := by
              exact congrArg Matrix.rank hmatrix
    _ ≤ (CoeffMatrixHelpers.coeffMatrix monomials
          (fun i => applyRestriction ρ (spdpMonomialGenerator (F := ℚ) κ ℓ p i))).rank := by
            exact CoeffMatrixHelpers.rank_coeffMatrix_submatrix_le
              (σ := Fin n) (F := ℚ) monomials
              (fun i => applyRestriction ρ (spdpMonomialGenerator (F := ℚ) κ ℓ p i))
              rowMap colMap

/-- Every free-variable-only target generator of `applyRestriction ρ p` comes
from restricting a source SPDP generator of `p`. -/
theorem freeRestrictedSpdpSubspace_le_restriction_image {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    [Fintype ((Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ })] :
    freeRestrictedSpdpSubspace ρ κ ℓ p ≤
      Submodule.map (applyRestrictionAlgHom ρ).toLinearMap (spdpSubspace κ ℓ p) := by
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨i, hSfree, hdfree, rfl⟩
  exact free_spdpMonomialGenerator_mem_restriction_map ρ p κ ℓ i hSfree hdfree

private noncomputable instance freeRestrictedSpdpSubspace_finite {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    [Fintype ((Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ })] :
    Module.Finite ℚ (freeRestrictedSpdpSubspace ρ κ ℓ p) := by
  have hle :
      freeRestrictedSpdpSubspace ρ κ ℓ p ≤
        MvPolynomial.restrictTotalDegree (Fin n) ℚ (ℓ + p.totalDegree) := by
    rw [freeRestrictedSpdpSubspace_eq_span_generators]
    apply Submodule.span_le.mpr
    intro q hq
    rcases hq with ⟨i, rfl⟩
    exact (MvPolynomial.mem_restrictTotalDegree _ _ _).2
      (le_trans (spdpMonomialGenerator_totalDegree_le κ ℓ (applyRestriction ρ p) i.1)
        (Nat.add_le_add_left (applyRestriction_totalDegree_le ρ p) ℓ))
  have :
      Module.Finite ℚ
        (MvPolynomial.restrictTotalDegree (Fin n) ℚ (ℓ + p.totalDegree)) :=
    MvPolynomial.instFiniteSubtypeMemSubmoduleRestrictTotalDegreeOfFinite _ _ _
  exact Module.Finite.of_injective (Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)

/-- The free-variable-only target SPDP subspace has dimension at most the
original SPDP rank. This is the theorem-level form of the paper-faithful
restriction target currently available in the shared tree. -/
theorem freeRestrictedSpdpSubspace_finrank_le_spdpRank {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    [Fintype ((Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ })] :
    Module.finrank ℚ (freeRestrictedSpdpSubspace ρ κ ℓ p) ≤ spdpRank κ ℓ p := by
  calc
    Module.finrank ℚ (freeRestrictedSpdpSubspace ρ κ ℓ p)
      ≤ Module.finrank ℚ
          (Submodule.map (applyRestrictionAlgHom ρ).toLinearMap (spdpSubspace κ ℓ p)) :=
        Submodule.finrank_mono
          (freeRestrictedSpdpSubspace_le_restriction_image ρ κ ℓ p)
    _ ≤ spdpRank κ ℓ p :=
        restriction_image_spdpSubspace_finrank_le_spdpRank ρ κ ℓ p

/-- Coefficient-matrix form of the free-variable-only target bridge over the
bounded monomial universe. -/
theorem freeRestrictedSpdpCoeffMatrix_rank_le_spdpRank {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    [Fintype ((Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ })] :
    let monomials := freeMonomialsLE ρ (ℓ + p.totalDegree)
    (CoeffMatrixHelpers.coeffMatrix monomials
      (freeRestrictedSpdpGenerator ρ κ ℓ p)).rank ≤
        spdpRank κ ℓ p := by
  let monomials := freeMonomialsLE ρ (ℓ + p.totalDegree)
  change (CoeffMatrixHelpers.coeffMatrix monomials
    (freeRestrictedSpdpGenerator ρ κ ℓ p)).rank ≤ spdpRank κ ℓ p
  calc
    (CoeffMatrixHelpers.coeffMatrix monomials
      (freeRestrictedSpdpGenerator ρ κ ℓ p)).rank
        = Module.finrank ℚ (freeRestrictedSpdpSubspace ρ κ ℓ p) := by
            simpa [monomials] using
              (freeRestrictedSpdpSubspace_finrank_eq_coeffMatrix_rank ρ κ ℓ p).symm
    _ ≤ spdpRank κ ℓ p :=
      freeRestrictedSpdpSubspace_finrank_le_spdpRank ρ κ ℓ p

/-! ## Restriction-Matrix Frontier

The file proves the linear-algebra half of the intended Lemma 141 argument:
restricting the canonical SPDP generators of `f` and then passing to
coefficient matrices inside a fixed finite monomial universe cannot increase
rank.

What is not proved here is the stronger statement
`spdpRank κ ℓ (applyRestriction ρ f) ≤ spdpRank κ ℓ f` for the current ambient
definitions. The issue is semantic, not just technical: `applyRestriction ρ f`
still lives in `MvPolynomial (Fin n) ℚ`, so the target-side SPDP multipliers
may continue to use variables that were fixed by `ρ`. The paper's
column-deletion argument needs a target space where those multiplier variables
have also been removed or forbidden.

The local lemmas `applyRestriction_spdpMonomialGenerator` and
`restrictedSpdpMonomialGenerator_eq_if_free` make the mismatch explicit:
restricting a source generator replaces the fixed-variable part of the
multiplier monomial by a scalar, while the honest target generator keeps the
full monomial factor and only restricts the derivative term.

Concrete counterexample to the abandoned bridge
`spdpMonomialCoeffMatrix(applyRestriction ρ f) ≤ coeffMatrix(restricted source
generators)`:

- `n = 2`, `κ = 0`, `ℓ = 1`, `f = X 0`
- fix variable `0` to `1` and leave variable `1` free

Then `applyRestriction ρ f = 1`. The honest target SPDP generators are
`{1, X 0, X 1}`, while the naively restricted source generators are
`{1, 1, X 1}`. So that candidate bridge already fails at the level of row
spaces.

The theorem below records the exact matrix inequality that is established by
the infrastructure above and is the honest frontier for this file. -/

/-- Restricting the canonical SPDP generators of `p` and taking coefficient
matrices over a common finite monomial set cannot increase rank. -/
theorem restrictedSourceSpdpCoeffMatrix_rank_le_spdpRank {n : ℕ}
    (ρ : VarRestriction n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    [Fintype ((Fin κ → Fin n) × { d : (Fin n →₀ ℕ) // d.sum (fun _ e => e) ≤ ℓ })] :
    let monomials := monomialsLE n (ℓ + p.totalDegree)
    (CoeffMatrixHelpers.coeffMatrix monomials
      (fun i => applyRestriction ρ (spdpMonomialGenerator (F := ℚ) κ ℓ p i))).rank ≤
        spdpRank κ ℓ p := by
  simpa using restrictedSourceSpdpCoeffMatrix_rank_le ρ κ ℓ p

/-! ## Application: Language Polynomial → Instance Polynomial -/

theorem hard_instance_p_side_bound
    (language_rank instance_rank : ℕ)
    (h_restriction : instance_rank ≤ language_rank)
    (h_p_side : language_rank ≤ 200) :
    instance_rank ≤ 200 :=
  le_trans h_restriction h_p_side

end RestrictionMono
