import PallLean.MultilinearSPDP
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

namespace PolynomialSupport

open MvPolynomial
open MultilinearSPDP

/-- pderiv does not introduce new variables. -/
theorem vars_pderiv_subset
    {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]
    (i : σ) (p : MvPolynomial σ F) :
    (MvPolynomial.pderiv i p).vars ⊆ p.vars := by
  intro x hx
  rw [MvPolynomial.mem_vars] at hx ⊢
  obtain ⟨m, hm, hmx⟩ := hx
  rw [MvPolynomial.as_sum p] at hm
  simp only [map_sum, MvPolynomial.pderiv_monomial] at hm
  obtain ⟨d, hd, hm_in⟩ := Finsupp.mem_support_finset_sum m hm
  have hsub := MvPolynomial.support_monomial_subset hm_in
  rw [Finset.mem_singleton] at hsub
  subst hsub
  exact ⟨d, hd, by
    rw [Finsupp.mem_support_iff] at hmx ⊢
    intro h0
    exact hmx (by simpa [h0])⟩

/-- iterated pderiv does not introduce new variables. -/
theorem vars_iterDerivList_subset
    {n : ℕ} {F : Type*} [CommRing F]
    (S : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    (iterDerivList S p).vars ⊆ p.vars := by
  induction S generalizing p with
  | nil =>
      simpa [iterDerivList]
  | cons a rest ih =>
      simp [iterDerivList]
      exact Set.Subset.trans (ih _) (vars_pderiv_subset a p)

/-- mlProj is always multilinear. -/
theorem isMultilinear_mlProj
    {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]
    (p : MvPolynomial σ F) :
    IsMultilinear (mlProj p) := by
  intro α hα i
  have hfilter : Finsupp.IsMultilinear α := by
    rw [mlProj] at hα
    change α ∈ (Finsupp.filter (fun β => Finsupp.IsMultilinear β) p).support at hα
    rw [Finsupp.support_filter] at hα
    exact (Finset.mem_filter.mp hα).2
  exact hfilter i

/-- mlProj does not introduce new variables. -/
theorem vars_mlProj_subset
    {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]
    (p : MvPolynomial σ F) :
    (mlProj p).vars ⊆ p.vars := by
  intro x hx
  rw [MvPolynomial.mem_vars] at hx ⊢
  obtain ⟨m, hm, hmx⟩ := hx
  exact ⟨m, mlProj_support_subset p hm, hmx⟩

end PolynomialSupport
