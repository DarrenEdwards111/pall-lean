import PallLean.Paper93.Paper283.BridgeBShiftPosDef
import PallLean.Paper93.Paper283.RouteBUnifiedCertificate

/-!
# Strict Route B matrix certificate

This file keeps the Route B path on its analytic side.  It defines a concrete
matrix certificate that no longer asks for the shifted positive-definite fact
`(I + theta A).PosDef` as data.  That field is now derived by
`one_add_smul_posSemidef_posDef_of_pos` from:

* `A.PosSemidef`;
* `0 < theta`.

No alternate-route adapter input appears in this file.
The remaining genuine Route B fields are the shifted-eigenvalue composition
identity, the eigenvalue norm bound, the Bridge A lower log-det package, and
the matrix-to-SAT functoriality package.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open TuringMachine
open PaperFaithfulSeparation
open PallLean.Paper93.DeepMath.PathB

/-- Route B concrete matrix certificate with shifted positive-definiteness
derived rather than stored.

This is stricter than `RouteBConcreteMatrixCertificate`: the matrix side asks
only for PSD, positive `theta`, the shifted-eigenvalue composition identity,
and the norm/lower-logdet/functorial data. -/
def RouteBStrictMatrixCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (N d : Nat)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (theta normBound delta rankLogRate : Real)
    (A : Matrix (Fin N) (Fin N) Real)
    (hA : A.PosSemidef)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)),
    ∃ htheta : 0 < theta,
      0 < alpha ∧ 0 < alpha0 ∧ 2 <= gadgetN ∧
      0 < normBound ∧
      (∀ i,
        (one_add_smul_posSemidef_posDef_of_pos A hA htheta).1.eigenvalues i =
          1 + theta * hA.1.eigenvalues i) ∧
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

/-- A strict Route B matrix certificate supplies the existing concrete matrix
certificate by deriving the shifted positive-definite field. -/
theorem routeBConcreteMatrixCertificate_of_strictMatrixCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (cert : RouteBStrictMatrixCertificate M n hn2 htb hns) :
    RouteBConcreteMatrixCertificate M n hn2 htb hns := by
  rcases cert with
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, normBound, delta, rankLogRate, A, hA, Pi,
      htheta, halpha, halpha0, hgadgetN, hnorm,
      hshift_eigs, heigs_bound, hlower, hAdm, hcompat, hfun⟩
  exact
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, normBound, delta, rankLogRate, A, hA,
      one_add_smul_posSemidef_posDef_of_pos A hA htheta,
      Pi,
      halpha, halpha0, hgadgetN, htheta, hnorm,
      hshift_eigs, heigs_bound, hlower, hAdm, hcompat, hfun⟩

/-- Strict matrix certificates supply the generic Route B per-instance
certificate. -/
theorem routeBPerInstanceCertificate_of_strictMatrixCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (cert : RouteBStrictMatrixCertificate M n hn2 htb hns) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_concreteMatrixCertificate
    (routeBConcreteMatrixCertificate_of_strictMatrixCertificate cert)

/-- Strict matrix certificate form of the per-instance rich-projection
target. -/
theorem cookLevinRichProjectionTarget_of_strictMatrixCertificate
    {M : DTM} {n : Nat} {hn : n ≥ 2 ^ 804} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (cert : RouteBStrictMatrixCertificate M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_concreteMatrixCertificate
    (routeBConcreteMatrixCertificate_of_strictMatrixCertificate cert)

/-- Uniform strict Route B certificates discharge the rich-projection
frontier. -/
theorem cookLevinRichProjectionDischarge_of_strictMatrixCertificates
    (hcert :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        RouteBStrictMatrixCertificate M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_of_concreteMatrixCertificates
    (fun M n hn hn2 htb hns hdec =>
      routeBConcreteMatrixCertificate_of_strictMatrixCertificate
        (hcert M n hn hn2 htb hns hdec))

/-- Contradiction-strength endpoint from uniform strict Route B matrix
certificates. -/
theorem noBoundedSATDeciderAtPaperScale_of_strictMatrixCertificates
    (hcert :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        RouteBStrictMatrixCertificate M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_concreteMatrixCertificates
    (fun M n hn hn2 htb hns hdec =>
      routeBConcreteMatrixCertificate_of_strictMatrixCertificate
        (hcert M n hn hn2 htb hns hdec))

/-! ## Axiom audit anchors -/

#print axioms routeBConcreteMatrixCertificate_of_strictMatrixCertificate
#print axioms routeBPerInstanceCertificate_of_strictMatrixCertificate
#print axioms cookLevinRichProjectionTarget_of_strictMatrixCertificate
#print axioms cookLevinRichProjectionDischarge_of_strictMatrixCertificates
#print axioms noBoundedSATDeciderAtPaperScale_of_strictMatrixCertificates

end PallLean.Paper93.Paper283
