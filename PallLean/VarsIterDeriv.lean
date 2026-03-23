/-
  VarsIterDeriv.lean — vars(iterDerivList S V) ⊆ vars(V)
-/
import PallLean.SPDPDefs
import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.PDeriv

namespace VarsIterDeriv

open MvPolynomial

/-- vars(pderiv i p) ⊆ vars(p) (copied from ProfileCompression to break import cycle) -/
theorem vars_pderiv_subset' {N : ℕ} {F : Type*} [CommRing F]
    (i : Fin N) (p : MvPolynomial (Fin N) F) :
    (pderiv i p).vars ⊆ p.vars := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  apply (vars_sum_subset _ _).trans
  intro j hj
  simp only [Finset.mem_biUnion] at hj
  obtain ⟨s, hs, hj_s⟩ := hj
  rw [pderiv_monomial] at hj_s
  by_cases hsi : p.coeff s * s i = 0
  · simp [hsi] at hj_s
  · rw [vars_monomial hsi] at hj_s
    have : (s - Finsupp.single i 1).support ⊆ s.support := by
      intro k hk
      rw [Finsupp.mem_support_iff] at hk ⊢
      simp [Finsupp.tsub_apply, Finsupp.single_apply] at hk ⊢
      split at hk <;> omega
    exact (mem_vars j).mpr ⟨s, hs, this hj_s⟩

theorem vars_iterDerivList_subset {N : ℕ} {F : Type*} [CommRing F]
    (S : List (Fin N)) (V : MvPolynomial (Fin N) F) :
    (SPDP.iterDerivList S V).vars ⊆ V.vars := by
  induction S generalizing V with
  | nil => simp [SPDP.iterDerivList]
  | cons i T ih =>
    simp only [SPDP.iterDerivList, List.foldl_cons]
    exact (ih (pderiv i V)).trans (vars_pderiv_subset' i V)

end VarsIterDeriv

/-- If S.toFinset ⊄ V.vars, iterDerivList S V = 0. -/
theorem iterDerivList_eq_zero_of_not_subset_vars {N : ℕ} {F : Type*} [CommRing F]
    (S : List (Fin N)) (V : MvPolynomial (Fin N) F)
    (h : ¬ S.toFinset ⊆ V.vars) :
    SPDP.iterDerivList S V = 0 := by
  induction S generalizing V with
  | nil => simp at h
  | cons i T ih =>
    simp only [SPDP.iterDerivList, List.foldl_cons]
    by_cases hi : i ∈ V.vars
    · apply ih (pderiv i V)
      intro hsub; apply h
      simp only [List.toFinset_cons]
      exact Finset.insert_subset_iff.mpr ⟨hi, fun x hx => vars_pderiv_subset' i V (hsub hx)⟩
    · rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars hi]
      exact SPDP.foldl_pderiv_zero T
