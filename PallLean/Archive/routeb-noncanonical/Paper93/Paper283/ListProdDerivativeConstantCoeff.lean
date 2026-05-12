import PallLean.ProductDeriv
import Mathlib.Tactic

/-!
# Constant coefficient of a derivative of a list product

This file records a small generic helper for the Route B / Bridge A compiler
frontier: if every factor has constant coefficient `1`, exactly one
distinguished factor has derivative constant coefficient `-1`, and all other
factor derivatives have constant coefficient `0`, then the derivative of the
whole `List.prod` has constant coefficient `-1`.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial

attribute [local instance] Classical.dec

namespace ListProdDerivativeConstantCoeff

private theorem coeff_zero_mul {R : Type*} [CommRing R] {N : Nat}
    (p q : MvPolynomial (Fin N) R) :
    coeff 0 (p * q) =
      coeff 0 p * coeff 0 q := by
  calc
    coeff 0 (p * q) =
        MvPolynomial.constantCoeff (p * q) := rfl
    _ = MvPolynomial.constantCoeff p * MvPolynomial.constantCoeff q :=
        map_mul MvPolynomial.constantCoeff p q
    _ = coeff 0 p * coeff 0 q := by
        rw [MvPolynomial.constantCoeff_eq]

theorem coeff_zero_list_prod_eq_list_prod_coeff_zero {N : Nat}
    {R : Type*} [CommRing R]
    (fs : List (MvPolynomial (Fin N) R)) :
    coeff 0 fs.prod =
      (fs.map (fun p => coeff 0 p)).prod := by
  calc
    coeff 0 fs.prod =
        MvPolynomial.constantCoeff fs.prod := rfl
    _ = (fs.map (fun p => MvPolynomial.constantCoeff p)).prod := by
        rw [map_list_prod]
    _ = (fs.map (fun p => coeff 0 p)).prod := by
        simp [MvPolynomial.constantCoeff_eq]

theorem coeff_zero_list_prod_eq_one_of_forall {N : Nat}
    {R : Type*} [CommRing R]
    (fs : List (MvPolynomial (Fin N) R))
    (hconst : ∀ p, p ∈ fs -> coeff 0 p = 1) :
    coeff 0 fs.prod = 1 := by
  rw [coeff_zero_list_prod_eq_list_prod_coeff_zero]
  apply List.prod_eq_one
  intro c hc
  simp only [List.mem_map] at hc
  obtain ⟨p, hp, rfl⟩ := hc
  exact hconst p hp

theorem coeff_zero_pderiv_list_prod_eq_sum_deriv_coeff {N : Nat}
    {R : Type*} [CommRing R]
    (i : Fin N) (fs : List (MvPolynomial (Fin N) R))
    (hconst : ∀ p, p ∈ fs -> coeff 0 p = 1) :
    coeff 0 (pderiv i fs.prod) =
      (fs.map (fun p => coeff 0 (pderiv i p))).sum := by
  induction fs with
  | nil =>
      simp
  | cons p ps ih =>
      have hpconst : coeff 0 p = 1 := hconst p (by simp)
      have hpsconst :
          ∀ q, q ∈ ps -> coeff 0 q = 1 := by
        intro q hq
        exact hconst q (by simp [hq])
      have hpsprod :
          coeff 0 ps.prod = 1 :=
        coeff_zero_list_prod_eq_one_of_forall ps hpsconst
      calc
        coeff 0 (pderiv i (p :: ps).prod) =
            coeff 0
              (pderiv i p * ps.prod + p * pderiv i ps.prod) := by
              rw [List.prod_cons, pderiv_mul]
        _ =
            coeff 0 (pderiv i p) +
              coeff 0 (pderiv i ps.prod) := by
              rw [MvPolynomial.coeff_add, coeff_zero_mul, coeff_zero_mul,
                hpsprod, hpconst]
              ring
        _ = ((p :: ps).map
              (fun q => coeff 0 (pderiv i q))).sum := by
              rw [ih hpsconst]
              simp

theorem coeff_zero_pderiv_list_prod_eq_zero_of_forall {N : Nat}
    {R : Type*} [CommRing R]
    (i : Fin N) (fs : List (MvPolynomial (Fin N) R))
    (hconst : ∀ p, p ∈ fs -> coeff 0 p = 1)
    (hderiv : ∀ p, p ∈ fs -> coeff 0 (pderiv i p) = 0) :
    coeff 0 (pderiv i fs.prod) = 0 := by
  rw [coeff_zero_pderiv_list_prod_eq_sum_deriv_coeff i fs hconst]
  apply List.sum_eq_zero
  intro c hc
  simp only [List.mem_map] at hc
  obtain ⟨p, hp, rfl⟩ := hc
  exact hderiv p hp

theorem coeff_zero_pderiv_list_prod_distinguished_split {N : Nat}
    {R : Type*} [CommRing R]
    (i : Fin N)
    (left right : List (MvPolynomial (Fin N) R))
    (special : MvPolynomial (Fin N) R)
    (hleft_const :
      ∀ p, p ∈ left -> coeff 0 p = 1)
    (hspecial_const :
      coeff 0 special = 1)
    (hright_const :
      ∀ p, p ∈ right -> coeff 0 p = 1)
    (hleft_deriv :
      ∀ p, p ∈ left -> coeff 0 (pderiv i p) = 0)
    (hspecial_deriv :
      coeff 0 (pderiv i special) = -1)
    (hright_deriv :
      ∀ p, p ∈ right -> coeff 0 (pderiv i p) = 0) :
    coeff 0
        (pderiv i (left ++ special :: right).prod) = -1 := by
  let dcoeff : MvPolynomial (Fin N) R -> R :=
    fun p => coeff 0 (pderiv i p)
  have hall_const :
      ∀ p, p ∈ left ++ special :: right ->
        coeff 0 p = 1 := by
    intro p hp
    simp only [List.mem_append, List.mem_cons] at hp
    rcases hp with hp | hp
    · exact hleft_const p hp
    · rcases hp with rfl | hp
      · exact hspecial_const
      · exact hright_const p hp
  have hleft_sum : (left.map dcoeff).sum = 0 := by
    apply List.sum_eq_zero
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    exact hleft_deriv p hp
  have hright_sum : (right.map dcoeff).sum = 0 := by
    apply List.sum_eq_zero
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    exact hright_deriv p hp
  rw [coeff_zero_pderiv_list_prod_eq_sum_deriv_coeff i
    (left ++ special :: right) hall_const]
  simp [dcoeff, List.map_append, hleft_sum, hright_sum, hspecial_deriv]

private theorem rat_sum_le_zero_of_all_zero_or_neg_one
    (L : List ℚ)
    (hall : ∀ x, x ∈ L -> x = 0 ∨ x = -1) :
    L.sum ≤ 0 := by
  induction L with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : x = 0 ∨ x = -1 := hall x (by simp)
      have hxs : xs.sum ≤ 0 := by
        apply ih
        intro y hy
        exact hall y (by simp [hy])
      simp only [List.sum_cons]
      rcases hx with rfl | rfl <;> linarith

private theorem rat_sum_le_neg_one_of_mem_neg_one_and_all_zero_or_neg_one
    (L : List ℚ)
    (hmem : (-1 : ℚ) ∈ L)
    (hall : ∀ x, x ∈ L -> x = 0 ∨ x = -1) :
    L.sum ≤ -1 := by
  induction L with
  | nil =>
      cases hmem
  | cons x xs ih =>
      have hx : x = 0 ∨ x = -1 := hall x (by simp)
      simp only [List.mem_cons] at hmem
      simp only [List.sum_cons]
      rcases hmem with hxmem | hxsmem
      · subst hxmem
        have hxs : xs.sum ≤ 0 := by
          apply rat_sum_le_zero_of_all_zero_or_neg_one
          intro y hy
          exact hall y (by simp [hy])
        linarith
      · have hxs : xs.sum ≤ -1 := by
          apply ih hxsmem
          intro y hy
          exact hall y (by simp [hy])
        rcases hx with rfl | rfl <;> linarith

theorem rat_sum_ne_zero_of_mem_neg_one_and_all_zero_or_neg_one
    (L : List ℚ)
    (hmem : (-1 : ℚ) ∈ L)
    (hall : ∀ x, x ∈ L -> x = 0 ∨ x = -1) :
    L.sum ≠ 0 := by
  have hle := rat_sum_le_neg_one_of_mem_neg_one_and_all_zero_or_neg_one L hmem hall
  intro hzero
  rw [hzero] at hle
  norm_num at hle

end ListProdDerivativeConstantCoeff

end PallLean.Paper93.Paper283
