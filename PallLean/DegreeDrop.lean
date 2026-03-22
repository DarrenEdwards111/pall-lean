/-
  DegreeDrop.lean — Derivatives kill polynomials past their degree
-/
import PallLean.SPDPDefs
import Mathlib.Tactic

namespace SPDP

open MvPolynomial

/-- Subtracting single i 1 strictly decreases Finsupp.sum when s i ≥ 1. -/
private lemma finsupp_sum_tsub_single_lt {n : ℕ} (s : Fin n →₀ ℕ) (i : Fin n) (hi : 1 ≤ s i) :
    (s - Finsupp.single i 1).sum (fun _ e => e) < s.sum (fun _ e => e) := by
  simp only [Finsupp.sum]
  have hsub : (s - Finsupp.single i 1).support ⊆ s.support := by
    intro j hj
    rw [Finsupp.mem_support_iff] at hj ⊢
    simp only [Finsupp.tsub_apply, Finsupp.single_apply] at hj
    split at hj <;> omega
  rw [Finset.sum_subset hsub (by
    intro j _ hj
    rw [Finsupp.mem_support_iff, not_not] at hj
    exact hj)]
  apply Finset.sum_lt_sum
  · intro j _
    simp only [Finsupp.tsub_apply, Finsupp.single_apply]
    split <;> omega
  · refine ⟨i, Finsupp.mem_support_iff.mpr (by omega), ?_⟩
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
    omega

theorem totalDegree_pderiv_lt {n : ℕ} {F : Type*} [CommRing F]
    (i : Fin n) (p : MvPolynomial (Fin n) F) (hp : pderiv i p ≠ 0) :
    (pderiv i p).totalDegree < p.totalDegree := by
  classical
  -- Write pderiv i p as sum over p.support
  have hpd : pderiv i p = p.support.sum (fun s => pderiv i (monomial s (p.coeff s))) := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
  -- td(p) > 0 (otherwise p constant → pderiv = 0)
  have hne : p ≠ 0 := by intro h; rw [h, map_zero] at hp; exact hp rfl
  have htd_pos : 0 < p.totalDegree := by
    by_contra h; push_neg at h
    apply hp
    rw [hpd]
    apply Finset.sum_eq_zero
    intro s hs
    rw [pderiv_monomial]
    -- s ∈ p.support and td(p) = 0 → degree(s) = 0 → s = 0 → s i = 0
    have hsd : s.sum (fun _ e => e) ≤ 0 := le_trans (le_totalDegree hs) (by omega)
    have hsd0 : s.sum (fun _ e => e) = 0 := by omega
    -- s i = 0 because s(j) ≥ 0 for all j and sum = 0
    have hsi : s i = 0 := by
      -- If s i > 0 then s.sum id ≥ s i > 0, contradicting hsd0
      by_contra hi; push_neg at hi
      have hpos : 0 < s i := by omega
      have : s i ≤ s.sum (fun _ e => e) := by
        apply Finset.single_le_sum (fun j _ => Nat.zero_le (s j))
        exact Finsupp.mem_support_iff.mpr (by omega)
      omega
    simp [hsi]
  -- Each summand pderiv i (monomial s c) = monomial (s - single i 1) (c * s i)
  -- has degree < td(p):
  --   if s i = 0: the monomial is 0 (coeff = c * 0 = 0)
  --   if s i ≥ 1: degree = (s - single i 1).sum id < s.sum id ≤ td(p)
  calc (pderiv i p).totalDegree
      = (p.support.sum (fun s => pderiv i (monomial s (p.coeff s)))).totalDegree :=
        congr_arg totalDegree hpd
    _ ≤ p.support.sup (fun s => (pderiv i (monomial s (p.coeff s))).totalDegree) :=
        totalDegree_finset_sum _ _
    _ < p.totalDegree := by
        rw [Finset.sup_lt_iff (by omega)]
        intro s hs
        rw [pderiv_monomial]
        by_cases hsi : s i = 0
        · simp [hsi]; omega
        · exact lt_of_le_of_lt (totalDegree_monomial_le _ _)
            (lt_of_lt_of_le (finsupp_sum_tsub_single_lt s i (by omega)) (le_totalDegree hs))

/-- Iterated derivative = 0 when list is longer than totalDegree. -/
theorem iterDerivList_eq_zero_of_length_gt {n : ℕ} {F : Type*} [CommRing F]
    (S : List (Fin n)) (p : MvPolynomial (Fin n) F)
    (hlen : S.length > p.totalDegree) :
    iterDerivList S p = 0 := by
  induction S generalizing p with
  | nil => simp at hlen
  | cons i T ih =>
    simp only [iterDerivList, List.foldl_cons]
    by_cases hp : pderiv i p = 0
    · rw [hp]; exact foldl_pderiv_zero T
    · apply ih
      have hlt := totalDegree_pderiv_lt i p hp
      simp only [List.length_cons] at hlen
      omega

end SPDP
