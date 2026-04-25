import PallLean.Paper93.Paper283.BridgeBSpectralSandwich
import PallLean.Paper93.Paper283.PSDSpectral
import PallLean.Paper93.DeepMath.NFrame.LogDetEigenvalues

/-!
# Bridge B spectral/log-det package from concrete PSD facts

This file pushes `BridgeBSpectralSandwich` one step closer to the Mathlib
matrix layer.  The rank-count and eigenvalue nonnegativity fields of
`BridgeBSpectralHypotheses` are now discharged from `A.PosSemidef`.

The remaining analytic inputs are kept as explicitly named hypotheses:
* the shifted log-det expansion, or
* the shifted-matrix eigenvalue identity needed to derive that expansion from
  the NFrame `log_det_posDef_eq_sum_log_eigenvalues` theorem;
* the pointwise bound by the chosen norm bound.
-/

namespace PallLean.Paper93.Paper283

open Finset

/-- For a PSD matrix, counting nonzero eigenvalues is the same as counting
positive eigenvalues. -/
theorem posSemidef_rank_eq_positive_eigenvalue_count {N : Nat}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef) :
    A.rank =
      (Finset.univ.filter (fun i => 0 < hA.1.eigenvalues i)).card := by
  classical
  have hfilter :
      Finset.univ.filter (fun i => hA.1.eigenvalues i ≠ 0) =
        Finset.univ.filter (fun i => 0 < hA.1.eigenvalues i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hne
      exact lt_of_le_of_ne (posSemidef_eigenvalues_nonneg A hA i) hne.symm
    · intro hpos
      exact ne_of_gt hpos
  rw [posSemidef_rank_eq_nonzero_eigenvalues A hA, hfilter]

/-- Construct the Bridge B spectral package from a PSD matrix, once the
shifted log-det expansion and the pointwise norm bound are supplied. -/
theorem bridgeB_spectral_hypotheses_of_posSemidef_with_logdet_shift_eq_sum_and_eigenvalue_bound
    {N : Nat} {theta normBound logDet : Real}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (hlogDet_shift_eq_sum :
      logDet = ∑ i, Real.log (1 + theta * hA.1.eigenvalues i))
    (heigenvalues_le_normBound :
      ∀ i, hA.1.eigenvalues i <= normBound) :
    BridgeBSpectralHypotheses theta normBound logDet A.rank hA.1.eigenvalues := by
  exact
    { logDet_eq_sum := hlogDet_shift_eq_sum
      eigenvalues_nonneg := posSemidef_eigenvalues_nonneg A hA
      eigenvalues_le_norm := heigenvalues_le_normBound
      rank_eq_positive_eigenvalue_count :=
        posSemidef_rank_eq_positive_eigenvalue_count A hA }

/-- Bridge B log-det upper bound for a concrete PSD matrix, with the remaining
log-det expansion and norm bound stated as named hypotheses. -/
theorem bridgeB_logdet_upper_of_posSemidef_with_logdet_shift_eq_sum_and_eigenvalue_bound
    {N : Nat} {theta normBound logDet : Real}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (htheta : 0 < theta)
    (hlogDet_shift_eq_sum :
      logDet = ∑ i, Real.log (1 + theta * hA.1.eigenvalues i))
    (heigenvalues_le_normBound :
      ∀ i, hA.1.eigenvalues i <= normBound) :
    logDet <= (A.rank : Real) * bridgeBLogCapacity theta normBound := by
  exact bridgeB_logdet_upper_from_spectral_hypotheses
    (theta := theta) (normBound := normBound) (logDet := logDet)
    (rankA := A.rank) (eigenvalues := hA.1.eigenvalues) htheta
    (bridgeB_spectral_hypotheses_of_posSemidef_with_logdet_shift_eq_sum_and_eigenvalue_bound
      (theta := theta) (normBound := normBound) (logDet := logDet)
      A hA hlogDet_shift_eq_sum heigenvalues_le_normBound)

/-- Paper-shaped Bridge B rank lower bound for a concrete PSD matrix, with the
remaining log-det expansion and norm bound stated as named hypotheses. -/
theorem bridgeB_rank_lower_of_posSemidef_with_logdet_shift_eq_sum_and_eigenvalue_bound
    {N : Nat} {theta normBound logDet delta : Real}
    {activeCard : Nat}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (htheta : 0 < theta) (hnorm : 0 < normBound)
    (hlogDet_shift_eq_sum :
      logDet = ∑ i, Real.log (1 + theta * hA.1.eigenvalues i))
    (heigenvalues_le_normBound :
      ∀ i, hA.1.eigenvalues i <= normBound)
    (hlower : delta * (activeCard : Real) <= logDet) :
    (delta / bridgeBLogCapacity theta normBound) *
        (activeCard : Real) <= (A.rank : Real) := by
  exact bridgeB_rank_lower_from_spectral_logdet_sandwich
    (theta := theta) (normBound := normBound) (logDet := logDet)
    (delta := delta) (activeCard := activeCard) (rankA := A.rank)
    (eigenvalues := hA.1.eigenvalues)
    htheta hnorm
    (bridgeB_spectral_hypotheses_of_posSemidef_with_logdet_shift_eq_sum_and_eigenvalue_bound
      (theta := theta) (normBound := normBound) (logDet := logDet)
      A hA hlogDet_shift_eq_sum heigenvalues_le_normBound)
    hlower

/-- Derive the shifted log-det expansion from the NFrame positive-definite
log-det/eigenvalue theorem plus the named shifted-eigenvalue identity. -/
theorem logdet_shift_eq_sum_of_shift_posDef_with_shift_eigenvalues_eq_one_add_theta_mul
    {N : Nat} {theta : Real}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (hshift :
      ((1 : Matrix (Fin N) (Fin N) Real) + theta • A).PosDef)
    (hshift_eigenvalues_eq_one_add_theta_mul :
      ∀ i, hshift.1.eigenvalues i = 1 + theta * hA.1.eigenvalues i) :
    Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det) =
      ∑ i, Real.log (1 + theta * hA.1.eigenvalues i) := by
  have hlog :=
    PallLean.Paper93.DeepMath.NFrame.log_det_posDef_eq_sum_log_eigenvalues
      ((1 : Matrix (Fin N) (Fin N) Real) + theta • A) hshift
  calc
    Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det)
        = ∑ i, Real.log (hshift.1.eigenvalues i) := hlog
    _ = ∑ i, Real.log (1 + theta * hA.1.eigenvalues i) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [hshift_eigenvalues_eq_one_add_theta_mul i]

/-- Construct the Bridge B spectral package for the actual shifted matrix
log-det, deriving the log-det expansion from NFrame.  The still-missing
operator-level facts are named in the theorem name and hypotheses. -/
theorem bridgeB_spectral_hypotheses_of_posSemidef_with_shift_posDef_and_shift_eigenvalues_eq_one_add_theta_mul_and_eigenvalue_bound
    {N : Nat} {theta normBound : Real}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (hshift :
      ((1 : Matrix (Fin N) (Fin N) Real) + theta • A).PosDef)
    (hshift_eigenvalues_eq_one_add_theta_mul :
      ∀ i, hshift.1.eigenvalues i = 1 + theta * hA.1.eigenvalues i)
    (heigenvalues_le_normBound :
      ∀ i, hA.1.eigenvalues i <= normBound) :
    BridgeBSpectralHypotheses theta normBound
      (Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det))
      A.rank hA.1.eigenvalues := by
  exact
    bridgeB_spectral_hypotheses_of_posSemidef_with_logdet_shift_eq_sum_and_eigenvalue_bound
      (theta := theta) (normBound := normBound)
      (logDet := Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det))
      A hA
      (logdet_shift_eq_sum_of_shift_posDef_with_shift_eigenvalues_eq_one_add_theta_mul
        (theta := theta) A hA hshift hshift_eigenvalues_eq_one_add_theta_mul)
      heigenvalues_le_normBound

/-- Bridge B rank lower bound for the actual shifted matrix log-det, deriving
the spectral log-det expansion from NFrame. -/
theorem bridgeB_rank_lower_of_posSemidef_with_shift_posDef_and_shift_eigenvalues_eq_one_add_theta_mul_and_eigenvalue_bound
    {N : Nat} {theta normBound delta : Real}
    {activeCard : Nat}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (hshift :
      ((1 : Matrix (Fin N) (Fin N) Real) + theta • A).PosDef)
    (hshift_eigenvalues_eq_one_add_theta_mul :
      ∀ i, hshift.1.eigenvalues i = 1 + theta * hA.1.eigenvalues i)
    (heigenvalues_le_normBound :
      ∀ i, hA.1.eigenvalues i <= normBound)
    (htheta : 0 < theta) (hnorm : 0 < normBound)
    (hlower :
      delta * (activeCard : Real) <=
        Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det)) :
    (delta / bridgeBLogCapacity theta normBound) *
        (activeCard : Real) <= (A.rank : Real) := by
  exact bridgeB_rank_lower_from_spectral_logdet_sandwich
    (theta := theta) (normBound := normBound)
    (logDet := Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det))
    (delta := delta) (activeCard := activeCard) (rankA := A.rank)
    (eigenvalues := hA.1.eigenvalues)
    htheta hnorm
    (bridgeB_spectral_hypotheses_of_posSemidef_with_shift_posDef_and_shift_eigenvalues_eq_one_add_theta_mul_and_eigenvalue_bound
      (theta := theta) (normBound := normBound)
      A hA hshift hshift_eigenvalues_eq_one_add_theta_mul
      heigenvalues_le_normBound)
    hlower

/-! ## Axiom audit anchors -/

#print axioms posSemidef_rank_eq_positive_eigenvalue_count
#print axioms bridgeB_spectral_hypotheses_of_posSemidef_with_logdet_shift_eq_sum_and_eigenvalue_bound
#print axioms bridgeB_logdet_upper_of_posSemidef_with_logdet_shift_eq_sum_and_eigenvalue_bound
#print axioms bridgeB_rank_lower_of_posSemidef_with_logdet_shift_eq_sum_and_eigenvalue_bound
#print axioms logdet_shift_eq_sum_of_shift_posDef_with_shift_eigenvalues_eq_one_add_theta_mul
#print axioms bridgeB_spectral_hypotheses_of_posSemidef_with_shift_posDef_and_shift_eigenvalues_eq_one_add_theta_mul_and_eigenvalue_bound
#print axioms bridgeB_rank_lower_of_posSemidef_with_shift_posDef_and_shift_eigenvalues_eq_one_add_theta_mul_and_eigenvalue_bound

end PallLean.Paper93.Paper283
