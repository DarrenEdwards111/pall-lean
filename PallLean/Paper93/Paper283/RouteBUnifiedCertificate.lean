import PallLean.Paper93.Paper283.RouteBFinalAssembly

/-!
# Unified Route B concrete certificate

This file sharpens `RouteBPerInstanceCertificate` one step further.  Instead
of asking directly for a generic `BridgeBSpectralHypotheses` package and raw
lower-logdet inequality, it accepts:

* an actual PSD matrix `A`;
* the shifted positive-definite/eigenvalue identity facts needed by Bridge B;
* the rank-budget lower-logdet package from Bridge A;
* the narrowed SAT/SPDP functoriality package.

It then builds the exact `RouteBPerInstanceCertificate` consumed by
`RouteBFinalAssembly`.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open TuringMachine
open PaperFaithfulSeparation
open PallLean.Paper93.DeepMath.PathB

/-- Concrete matrix-side Route B certificate for one Cook-Levin SAT-decider
instance.  This is still not the final unconditional `Π⋆`; it is the
strongest concrete matrix certificate currently expressible in the active
Paper283 vocabulary. -/
def RouteBConcreteMatrixCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (N d : Nat)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (theta normBound delta rankLogRate : Real)
    (A : Matrix (Fin N) (Fin N) Real)
    (hA : A.PosSemidef)
    (hshift :
      ((1 : Matrix (Fin N) (Fin N) Real) + theta • A).PosDef)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)),
      0 < alpha ∧ 0 < alpha0 ∧ 2 <= gadgetN ∧
      0 < theta ∧ 0 < normBound ∧
      (∀ i, hshift.1.eigenvalues i = 1 + theta * hA.1.eigenvalues i) ∧
      (∀ i, hA.1.eigenvalues i <= normBound) ∧
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        rankLogRate
        (Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det))
        delta ∧
      PallLean.Paper93.NFrame.AdmissibleGauge Pi ∧
      RouteBProjectionRankCompatible M n hn2 htb hns A.rank Pi ∧
      RouteBMatrixToSATGaugeFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        (bridgeBLogCapacity theta normBound) delta A.rank Pi

/-- A concrete PSD/shifted-logdet Route B matrix certificate supplies the
generic certificate consumed by `RouteBFinalAssembly`. -/
theorem routeBPerInstanceCertificate_of_concreteMatrixCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (cert : RouteBConcreteMatrixCertificate M n hn2 htb hns) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  rcases cert with
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, normBound, delta, rankLogRate, A, hA, hshift, Pi,
      halpha, halpha0, hgadgetN, htheta, hnorm,
      hshift_eigs, heigs_bound, hlower, hAdm, hcompat, hfun⟩
  refine ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
    theta, normBound,
    Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det),
    delta, A.rank, hA.1.eigenvalues, Pi,
    halpha, halpha0, hgadgetN, htheta, hnorm, ?_, ?_,
    hAdm, hcompat, hfun⟩
  · exact
      bridgeB_spectral_hypotheses_of_posSemidef_with_shift_posDef_and_shift_eigenvalues_eq_one_add_theta_mul_and_eigenvalue_bound
        (theta := theta) (normBound := normBound)
        A hA hshift hshift_eigs heigs_bound
  · exact
      bridgeA_cookLevin_logDet_lower_from_rank_budget
        alpha beta alpha0 kappa gadgetN G chi Phi
        halpha halpha0 hgadgetN hlower

/-- Concrete matrix certificate form of the per-instance rich-projection
target. -/
theorem cookLevinRichProjectionTarget_of_concreteMatrixCertificate
    {M : DTM} {n : Nat} {hn : n ≥ 2 ^ 804} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (cert : RouteBConcreteMatrixCertificate M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_routeBCertificate
    (hn := hn)
    (routeBPerInstanceCertificate_of_concreteMatrixCertificate cert)

/-- Uniform concrete matrix certificates discharge the final Route B
rich-projection frontier. -/
theorem cookLevinRichProjectionDischarge_of_concreteMatrixCertificates
    (hcert :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        RouteBConcreteMatrixCertificate M n hn2 htb hns) :
    CookLevinRichProjectionDischarge := by
  apply cookLevinRichProjectionDischarge_of_routeBCertificates
  intro M n hn hn2 htb hns hdec
  exact routeBPerInstanceCertificate_of_concreteMatrixCertificate
    (hcert M n hn hn2 htb hns hdec)

/-- Contradiction-strength endpoint from uniform concrete matrix certificates. -/
theorem noBoundedSATDeciderAtPaperScale_of_concreteMatrixCertificates
    (hcert :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        RouteBConcreteMatrixCertificate M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBCertificates
    (fun M n hn hn2 htb hns hdec =>
      routeBPerInstanceCertificate_of_concreteMatrixCertificate
        (hcert M n hn hn2 htb hns hdec))

/-! ## Axiom audit anchors -/

#print axioms routeBPerInstanceCertificate_of_concreteMatrixCertificate
#print axioms cookLevinRichProjectionTarget_of_concreteMatrixCertificate
#print axioms cookLevinRichProjectionDischarge_of_concreteMatrixCertificates
#print axioms noBoundedSATDeciderAtPaperScale_of_concreteMatrixCertificates

end PallLean.Paper93.Paper283
