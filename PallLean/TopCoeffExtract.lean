/-
  TopCoeffExtract.lean — iterDerivList over all live vars extracts the top coefficient.
-/
import PallLean.SPDPDefs
import PallLean.Restriction
import PallLean.Depth4Simulation
import PallLean.UniversalRestriction
import PallLean.PneqNP_Defs
import PallLean.IterDerivTopCoeff
import PallLean.MultilinearRestrict
import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.CommRing

open MvPolynomial Finset SPDP Restriction BoolEval Depth4Simulation
open IterDerivTopCoeff MultilinearRestrict PneqNP_Defs UniversalRestriction

namespace TopCoeffExtract

variable {n : ℕ}

/-- Helper: iterDerivList of a monomial not equal to topMon is 0 (via multilinearity). -/
private lemma iterDerivList_non_top_zero (f : BoolFun n) (ρ : Restriction n)
    (s : Fin n →₀ ℕ) (hs : s ∈ (restrictPoly ρ (multilinearInterp f)).support)
    (hne : s ≠ ∑ j ∈ liveVars ρ, Finsupp.single j 1) :
    iterDerivList (liveVars ρ).toList (monomial s (coeff s (restrictPoly ρ (multilinearInterp f)))) = 0 := by
  obtain ⟨j, hj_live, hj_zero⟩ := support_ne_topMon_has_zero f ρ s hs hne
  exact iterDerivList_monomial_zero _ s _ (liveVars ρ).nodup_toList j
    (Finset.mem_toList.mpr hj_live) hj_zero

theorem iterDerivList_allLive_eq_topCoeff_proved (n : ℕ) (f : BoolFun n) :
    iterDerivList (liveVars (universalRestriction n)).toList
      (restrictPoly (universalRestriction n) (multilinearInterp f)) =
    C (coeff (∑ j ∈ liveVars (universalRestriction n), Finsupp.single j 1)
      (restrictPoly (universalRestriction n) (multilinearInterp f))) := by
  set ρ := universalRestriction n
  set q := restrictPoly ρ (multilinearInterp f)
  set topMon := ∑ j ∈ liveVars ρ, Finsupp.single j 1
  -- Expand q as sum over support
  conv_lhs => rw [q.as_sum]
  rw [iterDerivList_sum]
  -- Each non-top monomial contributes 0
  have h_kill : ∀ s ∈ q.support, s ≠ topMon →
      iterDerivList (liveVars ρ).toList (monomial s (coeff s q)) = 0 :=
    fun s hs hne => iterDerivList_non_top_zero f ρ s hs hne
  -- The top monomial (if present) contributes C(topCoeff)
  -- Case split on whether topMon ∈ q.support
  by_cases htop : topMon ∈ q.support
  · -- topMon ∈ support: sum = top_contribution + rest
    rw [← Finset.add_sum_erase _ _ htop]
    -- The top contribution
    have h_top : iterDerivList (liveVars ρ).toList (monomial topMon (coeff topMon q)) = C (coeff topMon q) :=
      iterDerivList_top_monomial _ _
    -- The rest is all zero
    have h_rest : ∑ s ∈ q.support.erase topMon,
        iterDerivList (liveVars ρ).toList (monomial s (coeff s q)) = 0 := by
      apply Finset.sum_eq_zero; intro s hs
      exact h_kill s (Finset.mem_of_mem_erase hs) (Finset.ne_of_mem_erase hs)
    rw [h_top, h_rest, add_zero]
  · -- topMon ∉ support: coeff = 0, all contributions are 0
    have h_coeff : coeff topMon q = 0 := by
      rwa [MvPolynomial.mem_support_iff, not_not] at htop
    rw [h_coeff, C_0]
    apply Finset.sum_eq_zero; intro s hs
    by_cases heq : s = topMon
    · subst heq; exact absurd hs htop
    · exact h_kill s hs heq

end TopCoeffExtract
