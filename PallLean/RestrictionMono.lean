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

The remaining sorry is for the final dimension inequality. The subspace
containment approach (image ≤ target or target ≤ image) does not work
for the unblocked SPDP rank because multipliers m can involve fixed
variables, creating generators in the target that are outside the image
of the restriction map. The correct argument requires formalizing the
coefficient-matrix rank and column-deletion principle. -/

theorem spdpRank_restriction_mono {n : ℕ}
    (ρ : VarRestriction n) (f : MvPolynomial (Fin n) ℚ) (κ ℓ : ℕ) :
    spdpRank κ ℓ (applyRestriction ρ f) ≤ spdpRank κ ℓ f := by
  sorry

/-! ## Application: Language Polynomial → Instance Polynomial -/

theorem hard_instance_p_side_bound
    (language_rank instance_rank : ℕ)
    (h_restriction : instance_rank ≤ language_rank)
    (h_p_side : language_rank ≤ 200) :
    instance_rank ≤ 200 :=
  le_trans h_restriction h_p_side

end RestrictionMono
