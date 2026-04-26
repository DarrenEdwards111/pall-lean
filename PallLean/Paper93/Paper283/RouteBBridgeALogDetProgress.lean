import PallLean.Paper93.Paper283.BridgeALogDetLower
import PallLean.Paper93.Paper283.BridgeBShiftedEigenvalueCFC

/-!
# Route B Bridge A shifted log-det progress

This file records a kernel-only reduction of the Bridge A rank-logdet lower
package to the concrete shifted determinant used by Route B:

`Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det)`.

The PSD/spectral/logdet facts already available in Route B discharge the
shifted log-det expansion.  The only remaining analytic field is the sharper
standard spectral-sum lower bound against

`∑ i, Real.log (1 + theta * hA.1.eigenvalues i)`.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators

/-- For a PSD matrix and positive shift, the Route B shifted determinant log is
the sum of logs of the affine-shifted Hermitian eigenvalues. -/
theorem bridgeA_shifted_logDet_eq_sum_log_one_add_theta_eigenvalues
    {N : Nat} {theta : Real}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (htheta : 0 < theta) :
    Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det) =
      ∑ i, Real.log (1 + theta * hA.1.eigenvalues i) := by
  exact
    logdet_shift_eq_sum_of_shift_posDef_with_shift_eigenvalues_eq_one_add_theta_mul
      (theta := theta) A hA
      (one_add_smul_posSemidef_posDef_of_pos A hA htheta)
      (one_add_smul_posSemidef_posDef_of_pos_eigenvalues A hA htheta)

/-- Constructor for the Bridge A rank-logdet lower package with the actual
Route B shifted determinant log.

After PSD and `0 < theta` identify the shifted log-det with the spectral log
sum, the remaining analytic obligation is exactly

`rankLogRate * totalRank <= ∑ i, log (1 + theta * eigenvalue_i)`.
-/
theorem bridgeA_rankLogDetLowerHypotheses_of_shifted_logdet_spectral_sum_lower
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    {theta rankLogRate delta : Real}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (htheta : 0 < theta)
    (hrate_nonneg : 0 <= rankLogRate)
    (hdelta_rate : delta <= rankLogRate * (kappa : Real))
    (hspectral_lower :
      rankLogRate *
          ((∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
            (gadgetFamily v).rank) : Real) <=
        ∑ i, Real.log (1 + theta * hA.1.eigenvalues i)) :
    BridgeARankLogDetLowerHypotheses
      alpha beta alpha0 kappa G chi Phi gadgetFamily rankLogRate
      (Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det))
      delta := by
  refine ⟨hrate_nonneg, hdelta_rate, ?_⟩
  calc
    rankLogRate *
        ((∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
          (gadgetFamily v).rank) : Real)
        <= ∑ i, Real.log (1 + theta * hA.1.eigenvalues i) :=
          hspectral_lower
    _ =
        Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det) :=
          (bridgeA_shifted_logDet_eq_sum_log_one_add_theta_eigenvalues
            A hA htheta).symm

/-- PSD and positive shift give a nonnegative shifted log-det.  This is a
zero-rate sanity constructor useful for checking that the shifted determinant
target is compatible with the rank-logdet package when `delta <= 0`. -/
theorem bridgeA_shifted_logDet_nonneg_of_posSemidef
    {N : Nat} {theta : Real}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (htheta : 0 < theta) :
    0 <= Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det) := by
  rw [bridgeA_shifted_logDet_eq_sum_log_one_add_theta_eigenvalues A hA htheta]
  exact Finset.sum_nonneg (fun i _ => by
    have hlambda : 0 <= hA.1.eigenvalues i :=
      posSemidef_eigenvalues_nonneg A hA i
    have hone : 1 <= 1 + theta * hA.1.eigenvalues i := by
      nlinarith [mul_nonneg htheta.le hlambda]
    exact Real.log_nonneg hone)

/-- Nonpositive `delta` is discharged for the actual shifted log-det with
zero rank-log rate.  Positive Route B applications should use
`bridgeA_rankLogDetLowerHypotheses_of_shifted_logdet_spectral_sum_lower`
instead; this theorem records the base compatibility case. -/
theorem bridgeA_rankLogDetLowerHypotheses_of_shifted_logdet_zero_rate
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    {theta delta : Real}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (htheta : 0 < theta)
    (hdelta : delta <= 0) :
    BridgeARankLogDetLowerHypotheses
      alpha beta alpha0 kappa G chi Phi gadgetFamily 0
      (Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det))
      delta := by
  refine ⟨le_rfl, ?_, ?_⟩
  · simpa using hdelta
  · simpa using bridgeA_shifted_logDet_nonneg_of_posSemidef A hA htheta

/-! ## Axiom audit anchors -/

#print axioms bridgeA_shifted_logDet_eq_sum_log_one_add_theta_eigenvalues
#print axioms bridgeA_rankLogDetLowerHypotheses_of_shifted_logdet_spectral_sum_lower
#print axioms bridgeA_shifted_logDet_nonneg_of_posSemidef
#print axioms bridgeA_rankLogDetLowerHypotheses_of_shifted_logdet_zero_rate

end PallLean.Paper93.Paper283
