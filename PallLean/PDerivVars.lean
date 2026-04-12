/-
  PDerivVars.lean -- vars(pderiv w p) subset vars(p) for MvPolynomial
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Variables

namespace PDerivVars

open MvPolynomial

set_option maxHeartbeats 800000

/-- vars(pderiv w p) is a subset of vars(p). -/
theorem pderiv_vars_subset {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R] [NoZeroDivisors R]
    (w : σ) (p : MvPolynomial σ R) :
    (pderiv w p).vars ⊆ p.vars := by
  intro v hv
  rw [MvPolynomial.mem_vars] at hv ⊢
  obtain ⟨d, hd_supp, hd_v⟩ := hv
  refine ⟨d + Finsupp.single w 1, ?_, ?_⟩
  · rw [MvPolynomial.mem_support_iff]
    intro h_zero
    have hd_ne : coeff d (pderiv w p) ≠ 0 := MvPolynomial.mem_support_iff.mp hd_supp
    apply hd_ne
    conv_lhs => rw [as_sum p]
    rw [map_sum, coeff_sum]
    apply Finset.sum_eq_zero
    intro t _
    rw [pderiv_monomial, coeff_monomial]
    split
    · rename_i heq
      -- t - single w 1 = d. Either t w = 0 (so coeff * t w = 0) or t w >= 1 (so t = d + single w 1)
      by_cases htw : t w = 0
      · -- t w = 0, so coeff t p * ↑(t w) = coeff t p * 0 = 0
        simp [htw]
      · -- t w >= 1, so t = d + single w 1
        have ht_eq : t = d + Finsupp.single w 1 := by
          ext j
          have hj := Finsupp.ext_iff.mp heq j
          simp only [Finsupp.tsub_apply, Finsupp.single_apply] at hj
          simp only [Finsupp.add_apply, Finsupp.single_apply]
          by_cases hjw : j = w
          · subst hjw; simp only [ite_true] at hj ⊢; omega
          · have hjw' : ¬(w = j) := Ne.symm hjw
            simp only [hjw, hjw', ite_false, if_neg, Nat.sub_zero] at hj ⊢; omega
        rw [ht_eq, h_zero, zero_mul]
    · rfl
  · rw [Finsupp.mem_support_iff] at hd_v ⊢
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    omega

end PDerivVars
