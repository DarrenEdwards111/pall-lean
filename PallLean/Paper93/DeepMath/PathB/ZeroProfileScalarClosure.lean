import PallLean.Paper93.DeepMath.PathB.ZeroProfileSupportBasisCardinality
import PallLean.CompiledBoolFactorBridge

/-!
# Zero-profile scalar closure obstruction

The singleton scalar closure isolated in
`CookLevinZeroProfileTemplateScalarObligation` is false for the actual
Cook-Levin zero-profile base product.

The obstruction is coefficient-level and uses the real base product.  Its
constant coefficient is `1`.  If all shifted projections were scalar multiples
of one anchor, then `shift = 1` would force the anchor to have nonzero constant
coefficient.  But for any variable `i`, `shift = X i` has zero constant
coefficient and nonzero `X i` coefficient, an immediate contradiction.
-/

namespace PallLean
namespace Paper93
namespace DeepMath
namespace PathB

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP SPDP SymmetricPower
open scoped BigOperators

attribute [local instance] Classical.dec

/-- The zero-profile base product is the actual product-form Cook-Levin
compiled polynomial. -/
theorem cookLevinZeroProfileBaseProduct_eq_compiledPoly
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    cookLevinZeroProfileBaseProduct M n hn htb hns =
      compiledPoly (cook_levin_compilation M n hn htb hns) := by
  unfold cookLevinZeroProfileBaseProduct
  let factors : List (MvPolynomial (Fin n) ℚ) :=
    cookLevinFactorList M n hn htb hns
  have hcompiled :
      compiledPoly (cook_levin_compilation M n hn htb hns) = factors.prod := by
    simpa [factors, cookLevinFactorList] using
      compiledPoly_eq_constraints_prod M n hn htb hns
  rw [hcompiled]
  rw [← Fin.prod_univ_getElem]
  simp [factors, List.get_eq_getElem]

/-- The actual Cook-Levin zero-profile base product has constant coefficient
`1`.  This uses the booleanity/rest factorization of the compiled product. -/
theorem cookLevinZeroProfileBaseProduct_coeff_zero
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    MvPolynomial.coeff (0 : Fin n →₀ ℕ)
      (cookLevinZeroProfileBaseProduct M n hn htb hns) = (1 : ℚ) := by
  rw [cookLevinZeroProfileBaseProduct_eq_compiledPoly M n hn htb hns]
  rw [CompiledBoolFactorBridge.compiledPoly_eq_boolFactorFullProd_mul_rest]
  rw [← MvPolynomial.constantCoeff_eq]
  rw [map_mul]
  rw [MvPolynomial.constantCoeff_eq]
  have hbool :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ) (boolFactorFullProd n) = (1 : ℚ) := by
    simpa [boolFactorFullProd] using
      (SymmetricPower.coeff_zero_boolFactor_prod
        (N := n) (Finset.univ : Finset (Fin n)))
  rw [hbool]
  rw [restFactorProd'_const_one]
  norm_num

/-- A nonzero constant coefficient blocks singleton scalar closure under
`shift = 1` and `shift = X i`. -/
theorem zeroProfileScalarClosure_obstruction_of_constCoeff_ne_zero
    {n κ : ℕ} (p : MvPolynomial (Fin n) ℚ) (i : Fin n)
    (hκ : 1 ≤ κ)
    (hp0 : MvPolynomial.coeff (0 : Fin n →₀ ℕ) p ≠ 0) :
    ¬ (∃ anchor : MvPolynomial (Fin n) ℚ,
      ∀ (S : List (Fin n)), S.length ≤ κ →
        ∀ shift : MvPolynomial (Fin n) ℚ, shift.vars ⊆ S.toFinset →
          ∃ c : ℚ, c • anchor = mlProj (shift * p)) := by
  rintro ⟨anchor, hscalar⟩
  obtain ⟨c0, hc0⟩ :=
    hscalar [] (by simp) (1 : MvPolynomial (Fin n) ℚ) (by simp)
  obtain ⟨c1, hc1⟩ :=
    hscalar [i] (by simpa using hκ) (MvPolynomial.X i) (by simp)
  have hc0_coeff :
      c0 * MvPolynomial.coeff (0 : Fin n →₀ ℕ) anchor =
        MvPolynomial.coeff (0 : Fin n →₀ ℕ) p := by
    have hc := congrArg
      (fun q => MvPolynomial.coeff (0 : Fin n →₀ ℕ) q) hc0
    dsimp at hc
    rw [MvPolynomial.coeff_smul] at hc
    change c0 * MvPolynomial.coeff (0 : Fin n →₀ ℕ) anchor =
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (mlProj ((1 : MvPolynomial (Fin n) ℚ) * p)) at hc
    simp only [one_mul] at hc
    rw [coeff_mlProj_of_isMultilinear_mono] at hc
    · exact hc
    · intro j
      simp
  have hanchor0 : MvPolynomial.coeff (0 : Fin n →₀ ℕ) anchor ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hc0_coeff
    exact hp0 hc0_coeff.symm
  have hc1_const :
      c1 * MvPolynomial.coeff (0 : Fin n →₀ ℕ) anchor = 0 := by
    have hc := congrArg
      (fun q => MvPolynomial.coeff (0 : Fin n →₀ ℕ) q) hc1
    dsimp at hc
    rw [MvPolynomial.coeff_smul] at hc
    change c1 * MvPolynomial.coeff (0 : Fin n →₀ ℕ) anchor =
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (mlProj (MvPolynomial.X i * p)) at hc
    rw [coeff_mlProj_of_isMultilinear_mono] at hc
    · rw [MvPolynomial.coeff_X_mul'] at hc
      have hnot : i ∉ (0 : Fin n →₀ ℕ).support := by
        simp
      rw [if_neg hnot] at hc
      exact hc
    · intro j
      simp
  have hc1_zero : c1 = 0 := by
    rcases mul_eq_zero.mp hc1_const with hc | ha
    · exact hc
    · exact False.elim (hanchor0 ha)
  have hc1_single :
      c1 * MvPolynomial.coeff (Finsupp.single i 1) anchor =
        MvPolynomial.coeff (0 : Fin n →₀ ℕ) p := by
    have hc := congrArg
      (fun q => MvPolynomial.coeff (Finsupp.single i 1) q) hc1
    dsimp at hc
    rw [MvPolynomial.coeff_smul] at hc
    change c1 * MvPolynomial.coeff (Finsupp.single i 1) anchor =
      MvPolynomial.coeff (Finsupp.single i 1)
        (mlProj (MvPolynomial.X i * p)) at hc
    rw [coeff_mlProj_of_isMultilinear_mono] at hc
    · rw [MvPolynomial.coeff_X_mul'] at hc
      have hmem : i ∈ (Finsupp.single i 1 : Fin n →₀ ℕ).support := by
        simp
      rw [if_pos hmem] at hc
      simpa using hc
    · intro j
      simp [Finsupp.single_apply]
      split_ifs <;> omega
  rw [hc1_zero, zero_mul] at hc1_single
  exact hp0 hc1_single.symm

/-- The exact scalar-multiple form of the zero-profile singleton-template
obligation is false for the actual Cook-Levin base product. -/
theorem not_CookLevinZeroProfileTemplateScalarObligation
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ¬ CookLevinZeroProfileTemplateScalarObligation M n hn htb hns := by
  have hlog_pos : 0 < Nat.log 2 n := Nat.log_pos (by omega) hn
  have hlog : 1 ≤ Nat.log 2 n := Nat.succ_le_of_lt hlog_pos
  apply zeroProfileScalarClosure_obstruction_of_constCoeff_ne_zero
    (p := cookLevinZeroProfileBaseProduct M n hn htb hns)
    (i := ⟨0, by omega⟩)
    hlog
  rw [cookLevinZeroProfileBaseProduct_coeff_zero M n hn htb hns]
  norm_num

/-! ## Axiom audit anchors -/

#print axioms cookLevinZeroProfileBaseProduct_eq_compiledPoly
#print axioms cookLevinZeroProfileBaseProduct_coeff_zero
#print axioms zeroProfileScalarClosure_obstruction_of_constCoeff_ne_zero
#print axioms not_CookLevinZeroProfileTemplateScalarObligation

end PathB
end DeepMath
end Paper93
end PallLean
