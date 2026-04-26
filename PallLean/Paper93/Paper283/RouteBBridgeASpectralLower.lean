import PallLean.Paper93.Paper283.RouteBBridgeALogDetProgress

/-!
# Route B Bridge A spectral-sum lower bounds

This file closes a nontrivial kernel-only part of the remaining Bridge A
shifted log-det lower obligation isolated in
`RouteBBridgeALogDetProgress`.

The main arithmetic input is a finite set of eigenvalue slots `S` on which the
PSD eigenvalues are bounded below by a common floor `lambdaFloor`.  If the
floor budget

`rankLogRate * totalRank <= |S| * log (1 + theta * lambdaFloor)`

is large enough, then the full spectral sum

`sum_i log (1 + theta * eigenvalue_i)`

dominates `rankLogRate * totalRank`.  A uniform-eigenvalue-floor corollary is
included by taking `S = univ`.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators

/-- A lower bound on a chosen finite set of eigenvalues gives a lower bound on
the full shifted spectral log sum.  Eigenvalues outside `S` contribute
nonnegatively, so no lower floor is needed there. -/
theorem spectral_sum_lower_of_eigenvalue_floor_on_finset
    {N : Nat} {theta lambdaFloor : Real}
    {eigenvalues : Fin N -> Real}
    (S : Finset (Fin N))
    (htheta : 0 < theta)
    (heigenvalues_nonneg : ∀ i, 0 <= eigenvalues i)
    (hlambdaFloor_nonneg : 0 <= lambdaFloor)
    (hfloor : ∀ i ∈ S, lambdaFloor <= eigenvalues i) :
    (S.card : Real) * Real.log (1 + theta * lambdaFloor) <=
      ∑ i, Real.log (1 + theta * eigenvalues i) := by
  classical
  have hfloor_term_le :
      ∀ i ∈ S,
        Real.log (1 + theta * lambdaFloor) <=
          Real.log (1 + theta * eigenvalues i) := by
    intro i hi
    have harg_floor_pos : 0 < 1 + theta * lambdaFloor := by
      have hprod : 0 <= theta * lambdaFloor :=
        mul_nonneg htheta.le hlambdaFloor_nonneg
      linarith
    have hprod_le : theta * lambdaFloor <= theta * eigenvalues i :=
      mul_le_mul_of_nonneg_left (hfloor i hi) htheta.le
    have harg_le : 1 + theta * lambdaFloor <= 1 + theta * eigenvalues i := by
      linarith
    exact Real.log_le_log harg_floor_pos harg_le
  have hsum_floor_le :
      (∑ _i ∈ S, Real.log (1 + theta * lambdaFloor)) <=
        ∑ i ∈ S, Real.log (1 + theta * eigenvalues i) :=
    Finset.sum_le_sum hfloor_term_le
  have hsum_floor_const :
      (∑ _i ∈ S, Real.log (1 + theta * lambdaFloor)) =
        (S.card : Real) * Real.log (1 + theta * lambdaFloor) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hsum_S_le_univ :
      (∑ i ∈ S, Real.log (1 + theta * eigenvalues i)) <=
        ∑ i, Real.log (1 + theta * eigenvalues i) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) ?_
    intro i _hi_univ hi_not_mem
    have hprod : 0 <= theta * eigenvalues i :=
      mul_nonneg htheta.le (heigenvalues_nonneg i)
    have hone_le : 1 <= 1 + theta * eigenvalues i := by
      linarith
    exact Real.log_nonneg hone_le
  calc
    (S.card : Real) * Real.log (1 + theta * lambdaFloor)
        = ∑ _i ∈ S, Real.log (1 + theta * lambdaFloor) :=
          hsum_floor_const.symm
    _ <= ∑ i ∈ S, Real.log (1 + theta * eigenvalues i) := hsum_floor_le
    _ <= ∑ i, Real.log (1 + theta * eigenvalues i) := hsum_S_le_univ

/-- If the floor budget covers `rankLogRate * totalRank`, then the selected
eigenvalue-floor condition implies the remaining Route B spectral lower
obligation. -/
theorem rankLogRate_totalRank_le_spectral_sum_of_eigenvalue_floor_on_finset
    {N : Nat} {theta lambdaFloor rankLogRate totalRank : Real}
    {eigenvalues : Fin N -> Real}
    (S : Finset (Fin N))
    (htheta : 0 < theta)
    (heigenvalues_nonneg : ∀ i, 0 <= eigenvalues i)
    (hlambdaFloor_nonneg : 0 <= lambdaFloor)
    (hfloor : ∀ i ∈ S, lambdaFloor <= eigenvalues i)
    (hbudget :
      rankLogRate * totalRank <=
        (S.card : Real) * Real.log (1 + theta * lambdaFloor)) :
    rankLogRate * totalRank <=
      ∑ i, Real.log (1 + theta * eigenvalues i) :=
  hbudget.trans
    (spectral_sum_lower_of_eigenvalue_floor_on_finset
      S htheta heigenvalues_nonneg hlambdaFloor_nonneg hfloor)

/-- Uniform eigenvalue-floor corollary of
`spectral_sum_lower_of_eigenvalue_floor_on_finset`, obtained by taking
`S = Finset.univ`. -/
theorem spectral_sum_lower_of_uniform_eigenvalue_floor
    {N : Nat} {theta lambdaFloor : Real}
    {eigenvalues : Fin N -> Real}
    (htheta : 0 < theta)
    (heigenvalues_nonneg : ∀ i, 0 <= eigenvalues i)
    (hlambdaFloor_nonneg : 0 <= lambdaFloor)
    (hfloor : ∀ i, lambdaFloor <= eigenvalues i) :
    (N : Real) * Real.log (1 + theta * lambdaFloor) <=
      ∑ i, Real.log (1 + theta * eigenvalues i) := by
  simpa using
    (spectral_sum_lower_of_eigenvalue_floor_on_finset
      (N := N) (theta := theta) (lambdaFloor := lambdaFloor)
      (eigenvalues := eigenvalues) Finset.univ
      htheta heigenvalues_nonneg hlambdaFloor_nonneg
      (by intro i _hi; exact hfloor i))

/-- Uniform eigenvalue-floor sufficient condition for the remaining spectral
lower obligation. -/
theorem rankLogRate_totalRank_le_spectral_sum_of_uniform_eigenvalue_floor
    {N : Nat} {theta lambdaFloor rankLogRate totalRank : Real}
    {eigenvalues : Fin N -> Real}
    (htheta : 0 < theta)
    (heigenvalues_nonneg : ∀ i, 0 <= eigenvalues i)
    (hlambdaFloor_nonneg : 0 <= lambdaFloor)
    (hfloor : ∀ i, lambdaFloor <= eigenvalues i)
    (hbudget :
      rankLogRate * totalRank <=
        (N : Real) * Real.log (1 + theta * lambdaFloor)) :
    rankLogRate * totalRank <=
      ∑ i, Real.log (1 + theta * eigenvalues i) :=
  hbudget.trans
    (spectral_sum_lower_of_uniform_eigenvalue_floor
      (N := N) (theta := theta) (lambdaFloor := lambdaFloor)
      (eigenvalues := eigenvalues)
      htheta heigenvalues_nonneg hlambdaFloor_nonneg hfloor)

/-- Bridge A shifted-logdet lower package from lower bounds on enough PSD
eigenvalues.  This fills the remaining spectral-sum field in
`bridgeA_rankLogDetLowerHypotheses_of_shifted_logdet_spectral_sum_lower`. -/
theorem bridgeA_rankLogDetLowerHypotheses_of_shifted_logdet_eigenvalue_floor_on_finset
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    {theta rankLogRate delta lambdaFloor : Real}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (S : Finset (Fin N))
    (htheta : 0 < theta)
    (hrate_nonneg : 0 <= rankLogRate)
    (hdelta_rate : delta <= rankLogRate * (kappa : Real))
    (hlambdaFloor_nonneg : 0 <= lambdaFloor)
    (hfloor : ∀ i ∈ S, lambdaFloor <= hA.1.eigenvalues i)
    (hbudget :
      rankLogRate *
          ((∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
            (gadgetFamily v).rank) : Real) <=
        (S.card : Real) * Real.log (1 + theta * lambdaFloor)) :
    BridgeARankLogDetLowerHypotheses
      alpha beta alpha0 kappa G chi Phi gadgetFamily rankLogRate
      (Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det))
      delta := by
  exact
    bridgeA_rankLogDetLowerHypotheses_of_shifted_logdet_spectral_sum_lower
      alpha beta alpha0 kappa G chi Phi gadgetFamily A hA htheta
      hrate_nonneg hdelta_rate
      (rankLogRate_totalRank_le_spectral_sum_of_eigenvalue_floor_on_finset
        (N := N) (theta := theta) (lambdaFloor := lambdaFloor)
        (rankLogRate := rankLogRate)
        (totalRank :=
          ((∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
            (gadgetFamily v).rank) : Real))
        (eigenvalues := hA.1.eigenvalues)
        S htheta (posSemidef_eigenvalues_nonneg A hA)
        hlambdaFloor_nonneg hfloor hbudget)

/-- Bridge A shifted-logdet lower package from a uniform lower bound on all PSD
eigenvalues. -/
theorem bridgeA_rankLogDetLowerHypotheses_of_shifted_logdet_uniform_eigenvalue_floor
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    {theta rankLogRate delta lambdaFloor : Real}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (htheta : 0 < theta)
    (hrate_nonneg : 0 <= rankLogRate)
    (hdelta_rate : delta <= rankLogRate * (kappa : Real))
    (hlambdaFloor_nonneg : 0 <= lambdaFloor)
    (hfloor : ∀ i, lambdaFloor <= hA.1.eigenvalues i)
    (hbudget :
      rankLogRate *
          ((∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
            (gadgetFamily v).rank) : Real) <=
        (N : Real) * Real.log (1 + theta * lambdaFloor)) :
    BridgeARankLogDetLowerHypotheses
      alpha beta alpha0 kappa G chi Phi gadgetFamily rankLogRate
      (Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det))
      delta := by
  exact
    bridgeA_rankLogDetLowerHypotheses_of_shifted_logdet_spectral_sum_lower
      alpha beta alpha0 kappa G chi Phi gadgetFamily A hA htheta
      hrate_nonneg hdelta_rate
      (rankLogRate_totalRank_le_spectral_sum_of_uniform_eigenvalue_floor
        (N := N) (theta := theta) (lambdaFloor := lambdaFloor)
        (rankLogRate := rankLogRate)
        (totalRank :=
          ((∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
            (gadgetFamily v).rank) : Real))
        (eigenvalues := hA.1.eigenvalues)
        htheta (posSemidef_eigenvalues_nonneg A hA)
        hlambdaFloor_nonneg hfloor hbudget)

/-! ## Axiom audit anchors -/

#print axioms spectral_sum_lower_of_eigenvalue_floor_on_finset
#print axioms rankLogRate_totalRank_le_spectral_sum_of_eigenvalue_floor_on_finset
#print axioms spectral_sum_lower_of_uniform_eigenvalue_floor
#print axioms rankLogRate_totalRank_le_spectral_sum_of_uniform_eigenvalue_floor
#print axioms bridgeA_rankLogDetLowerHypotheses_of_shifted_logdet_eigenvalue_floor_on_finset
#print axioms bridgeA_rankLogDetLowerHypotheses_of_shifted_logdet_uniform_eigenvalue_floor

end PallLean.Paper93.Paper283
