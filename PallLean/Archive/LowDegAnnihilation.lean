/-
  LowDegAnnihilation.lean — Iterated derivatives kill low-degree polynomials
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Finsupp.Order
import Mathlib.Tactic

open MvPolynomial

namespace LowDeg

variable {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]

/-- Key inequality: subtracting single x 1 decreases degree sum by ≥ 1. -/
theorem finsupp_tsub_single_degree (s : σ →₀ ℕ) (x : σ) (hsx : s x ≠ 0) :
    (s - Finsupp.single x 1).sum (fun _ n => n) + 1 ≤ s.sum (fun _ n => n) := by
  have hx_supp : x ∈ s.support := Finsupp.mem_support_iff.mpr hsx
  -- Use Finsupp.coe_tsub to convert (s - t) to ⇑s - ⇑t
  have h_supp_sub : (s - Finsupp.single x 1).support ⊆ s.support := by
    intro i hi; rw [Finsupp.mem_support_iff] at hi ⊢
    intro hs; apply hi; simp [Finsupp.coe_tsub, hs]
  have h_le_each : ∀ i, (s - Finsupp.single x 1).toFun i ≤ s i := fun i =>
    Nat.sub_le _ _
  have h_lt_x : (s - Finsupp.single x 1).toFun x < s x := by
    show s x - Finsupp.single x 1 x < s x
    rw [Finsupp.single_apply, if_pos rfl]; omega
  have h1 : (s - Finsupp.single x 1).sum (fun _ n => n) ≤
      ∑ i ∈ s.support, (s - Finsupp.single x 1).toFun i := by
    unfold Finsupp.sum
    exact Finset.sum_le_sum_of_subset_of_nonneg h_supp_sub (fun _ _ _ => Nat.zero_le _)
  have h2 : ∑ i ∈ s.support, (s - Finsupp.single x 1).toFun i <
      ∑ i ∈ s.support, s.toFun i :=
    Finset.sum_lt_sum (fun i _ => h_le_each i) ⟨x, hx_supp, h_lt_x⟩
  -- s.sum (fun _ n => n) = ∑ i ∈ s.support, s.toFun i
  have h3 : s.sum (fun _ n => n) = ∑ i ∈ s.support, s.toFun i := rfl
  linarith

theorem foldl_pderiv_zero (l : List σ) :
    l.foldl (fun (r : MvPolynomial σ F) i => pderiv i r) 0 = 0 := by
  induction l with
  | nil => simp
  | cons a rest ih => simp [List.foldl, map_zero, ih]

theorem foldl_pderiv_add (l : List σ) (p q : MvPolynomial σ F) :
    l.foldl (fun r i => pderiv i r) (p + q) =
    l.foldl (fun r i => pderiv i r) p +
    l.foldl (fun r i => pderiv i r) q := by
  induction l generalizing p q with
  | nil => simp
  | cons a rest ih => simp only [List.foldl]; rw [map_add]; exact ih _ _

theorem foldl_pderiv_monomial_zero (S : List σ) (s : σ →₀ ℕ) (a : F)
    (h : s.sum (fun _ n => n) < S.length) :
    S.foldl (fun (r : MvPolynomial σ F) i => pderiv i r) (monomial s a) = 0 := by
  induction S generalizing s a with
  | nil => exact absurd h (Nat.not_lt_zero _)
  | cons x rest ih =>
    simp only [List.foldl, pderiv_monomial]
    by_cases hsx : s x = 0
    · simp [hsx, foldl_pderiv_zero]
    · apply ih; simp only [List.length_cons] at h
      have := finsupp_tsub_single_degree s x hsx; omega

theorem foldl_pderiv_finset_sum {ι : Type*} (S : List σ) (t : Finset ι)
    (f : ι → MvPolynomial σ F) :
    S.foldl (fun r i => pderiv i r) (∑ i ∈ t, f i) =
    ∑ i ∈ t, S.foldl (fun r i => pderiv i r) (f i) := by
  induction t using Finset.cons_induction with
  | empty => simp [foldl_pderiv_zero]
  | cons a t ha ih =>
    rw [Finset.sum_cons, foldl_pderiv_add, ih, Finset.sum_cons]

end LowDeg
