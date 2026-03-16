/-
  DegreeBounds.lean — Degree bounds for pderiv, iterDerivList, restrictPoly.
  Used to prove Module.Finite for the SPDP span.
-/
import PallLean.SPDPDefs
import PallLean.Restriction
import PallLean.Depth4Simulation
import Mathlib.Tactic

open MvPolynomial SPDP Finset Restriction

namespace DegreeBounds

variable {n : ℕ}

private lemma finsupp_sum_eq_univ_sum (s : Fin n →₀ ℕ) :
    s.sum (fun _ e => e) = ∑ j : Fin n, s j := by
  rw [Finsupp.sum, ← Finset.sum_subset (Finset.subset_univ _)]
  intro j _ hj; rw [Finsupp.mem_support_iff, not_not] at hj; exact hj

private lemma tsub_finsupp_sum_le (s : Fin n →₀ ℕ) (i : Fin n) :
    (s - Finsupp.single i 1).sum (fun _ e => e) ≤ s.sum (fun _ e => e) := by
  rw [finsupp_sum_eq_univ_sum, finsupp_sum_eq_univ_sum]
  exact Finset.sum_le_sum (fun j _ => tsub_le_self)

private lemma totalDegree_finset_sum_le {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → MvPolynomial (Fin n) ℚ) (d : ℕ)
    (h : ∀ i ∈ S, (f i).totalDegree ≤ d) :
    (∑ i ∈ S, f i).totalDegree ≤ d := by
  induction S using Finset.induction with
  | empty => simp
  | @insert j S hj ih =>
    rw [sum_insert hj]
    exact le_trans (totalDegree_add _ _) (max_le (h j (mem_insert_self j S))
      (ih (fun i hi => h i (mem_insert_of_mem hi))))

/-- Differentiation cannot increase totalDegree. -/
lemma totalDegree_pderiv_le (i : Fin n) (p : MvPolynomial (Fin n) ℚ) :
    (pderiv i p).totalDegree ≤ p.totalDegree := by
  have hp : pderiv i p = ∑ s ∈ p.support, monomial (s - Finsupp.single i 1)
      (coeff s p * ↑(s i)) := by
    conv_lhs => rw [← support_sum_monomial_coeff p]; simp only [map_sum, pderiv_monomial]
  rw [hp]; apply totalDegree_finset_sum_le _ _ p.totalDegree
  intro s hs
  by_cases hc : coeff s p * ↑(s i) = 0
  · simp [hc]
  · rw [totalDegree_monomial _ hc]; exact le_trans (tsub_finsupp_sum_le s i) (le_totalDegree hs)

/-- Iterated differentiation cannot increase totalDegree. -/
lemma totalDegree_iterDerivList_le (S : List (Fin n)) (p : MvPolynomial (Fin n) ℚ) :
    (iterDerivList S p).totalDegree ≤ p.totalDegree := by
  unfold iterDerivList; induction S generalizing p with
  | nil => simp
  | cons i S ih => exact le_trans (ih _) (totalDegree_pderiv_le i p)

/-- Restriction cannot increase totalDegree (substitutes X_i with X_i, 0, or 1). -/
lemma totalDegree_restrictPoly_le (ρ : Restriction n) (p : MvPolynomial (Fin n) ℚ) :
    (restrictPoly ρ p).totalDegree ≤ p.totalDegree := by
  -- restrictPoly = aeval (fun i => match ρ i with ...) p
  -- Each substitution has totalDegree ≤ 1 (X_i, 0, or 1).
  -- By MvPolynomial.totalDegree_aeval_le (if available) or manually.
  sorry

end DegreeBounds
