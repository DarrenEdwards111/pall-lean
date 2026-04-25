import PallLean.Paper93.Paper283.BridgeBSpectralReal
import Mathlib.Data.Real.StarOrdered

/-!
# Bridge B shifted positive-definiteness

This file removes one analytic side condition from the Route B spectral
certificate.  For a positive semidefinite matrix `A`, the shifted matrix

`I + theta • A`

is positive definite whenever `0 <= theta`.  This is the standard PSD/PD
matrix-order fact needed before applying the N-frame log-det/eigenvalue
identity.

The shifted eigenvalue identity is still separate; this file closes only the
positive-definiteness input.
-/

namespace PallLean.Paper93.Paper283

/-- If `A` is PSD and `theta >= 0`, then `I + theta A` is positive definite. -/
theorem one_add_smul_posSemidef_posDef {N : Nat}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    {theta : Real} (htheta : 0 <= theta) :
    ((1 : Matrix (Fin N) (Fin N) Real) + theta • A).PosDef := by
  exact Matrix.PosDef.add_posSemidef
    (Matrix.PosDef.one : (1 : Matrix (Fin N) (Fin N) Real).PosDef)
    (Matrix.PosSemidef.smul hA htheta)

/-- Positive-`theta` form of `one_add_smul_posSemidef_posDef`. -/
theorem one_add_smul_posSemidef_posDef_of_pos {N : Nat}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    {theta : Real} (htheta : 0 < theta) :
    ((1 : Matrix (Fin N) (Fin N) Real) + theta • A).PosDef :=
  one_add_smul_posSemidef_posDef A hA htheta.le

/-- Bridge B spectral hypotheses with the shifted positive-definiteness
discharged from `A.PosSemidef` and `0 < theta`.

The only spectral side conditions still supplied are the true spectral
composition identity

`eigenvalues(I + theta A) = 1 + theta * eigenvalues(A)`

and the operator/eigenvalue norm bound. -/
theorem bridgeB_spectral_hypotheses_of_posSemidef_with_auto_shiftPosDef
    {N : Nat} {theta normBound : Real}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (htheta : 0 < theta)
    (hshift_eigenvalues_eq_one_add_theta_mul :
      ∀ i,
        (one_add_smul_posSemidef_posDef_of_pos A hA htheta).1.eigenvalues i =
          1 + theta * hA.1.eigenvalues i)
    (heigenvalues_le_normBound :
      ∀ i, hA.1.eigenvalues i <= normBound) :
    BridgeBSpectralHypotheses theta normBound
      (Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det))
      A.rank hA.1.eigenvalues := by
  exact
    bridgeB_spectral_hypotheses_of_posSemidef_with_shift_posDef_and_shift_eigenvalues_eq_one_add_theta_mul_and_eigenvalue_bound
      (theta := theta) (normBound := normBound)
      A hA
      (one_add_smul_posSemidef_posDef_of_pos A hA htheta)
      hshift_eigenvalues_eq_one_add_theta_mul
      heigenvalues_le_normBound

/-- Bridge B rank lower bound with shifted positive-definiteness discharged.

This is the same endpoint as
`bridgeB_rank_lower_of_posSemidef_with_shift_posDef_and_shift_eigenvalues_eq_one_add_theta_mul_and_eigenvalue_bound`,
but it no longer asks for `((1 : Matrix _) + theta • A).PosDef` as a field. -/
theorem bridgeB_rank_lower_of_posSemidef_with_auto_shiftPosDef
    {N : Nat} {theta normBound delta : Real}
    {activeCard : Nat}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (htheta : 0 < theta) (hnorm : 0 < normBound)
    (hshift_eigenvalues_eq_one_add_theta_mul :
      ∀ i,
        (one_add_smul_posSemidef_posDef_of_pos A hA htheta).1.eigenvalues i =
          1 + theta * hA.1.eigenvalues i)
    (heigenvalues_le_normBound :
      ∀ i, hA.1.eigenvalues i <= normBound)
    (hlower :
      delta * (activeCard : Real) <=
        Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det)) :
    (delta / bridgeBLogCapacity theta normBound) *
        (activeCard : Real) <= (A.rank : Real) := by
  exact
    bridgeB_rank_lower_of_posSemidef_with_shift_posDef_and_shift_eigenvalues_eq_one_add_theta_mul_and_eigenvalue_bound
      (theta := theta) (normBound := normBound) (delta := delta)
      (activeCard := activeCard)
      A hA
      (one_add_smul_posSemidef_posDef_of_pos A hA htheta)
      hshift_eigenvalues_eq_one_add_theta_mul
      heigenvalues_le_normBound htheta hnorm hlower

/-! ## Axiom audit anchors -/

#print axioms one_add_smul_posSemidef_posDef
#print axioms one_add_smul_posSemidef_posDef_of_pos
#print axioms bridgeB_spectral_hypotheses_of_posSemidef_with_auto_shiftPosDef
#print axioms bridgeB_rank_lower_of_posSemidef_with_auto_shiftPosDef

end PallLean.Paper93.Paper283
