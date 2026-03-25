/-
  CoordSeparation.lean — Generic diagonal/off-diagonal → linear independence → finrank
-/
import Mathlib.Tactic

open MvPolynomial

theorem linearIndependent_of_diag_offdiag_coeff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {σ : Type*} [DecidableEq σ]
    (v : ι → MvPolynomial σ ℚ)
    (tag : ι → σ →₀ ℕ)
    (hdiag : ∀ i, (v i).coeff (tag i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → (v i).coeff (tag j) = 0) :
    LinearIndependent ℚ v := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  -- Extract coefficient of tag i from Σ g(j) • v(j) = 0
  have h := congr_arg (MvPolynomial.lcoeff ℚ (tag i)) hg
  simp only [map_sum, map_smul, map_zero, MvPolynomial.lcoeff_apply, smul_eq_mul] at h
  -- h : Σ g(j) * coeff(tag i)(v(j)) = 0
  -- Off-diagonal terms vanish
  have : g i * (v i).coeff (tag i) = 0 := by
    have := Finset.sum_eq_single i (fun j _ hji => show g j * (v j).coeff (tag i) = 0 from by rw [hoff j i hji, mul_zero]) (fun h => absurd hi h)
    linarith
  exact (mul_eq_zero.mp this).elim id (absurd · (hdiag i))
