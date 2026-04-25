import PallLean.Paper93.Paper283.BridgeBShiftedEigenvalueCFC
import PallLean.Paper93.Paper283.RouteBFunctorialTransportCertificate

/-!
# Reduced Route B certificate

This file is a narrow Route B-only constructor layer.  It combines:

* the discharged shifted-eigenvalue theorem from
  `BridgeBShiftedEigenvalueCFC`;
* the Bridge A rank-budget lower-logdet interface;
* the primitive SAT-side `RouteBFunctorialTransportCertificate`.

The resulting per-instance input no longer carries the shifted eigenvalue
identity, a separate eigenvalue norm bound, or the older broad
`RouteBMatrixToSATGaugeFunctoriality` package.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open TuringMachine
open PaperFaithfulSeparation
open PallLean.Paper93.DeepMath.PathB

/-- Reduced concrete Route B matrix certificate for one Cook-Levin instance.

The remaining explicit inputs are the concrete PSD matrix and positive shift,
the Bridge A lower-logdet package, NFrame admissibility and projection-rank
compatibility, and the primitive Route B transport certificate. -/
def RouteBReducedCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (N d : Nat)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (theta delta rankLogRate : Real)
    (A : Matrix (Fin N) (Fin N) Real)
    (_hA : A.PosSemidef)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)),
    ∃ _htheta : 0 < theta,
      0 < alpha ∧ 0 < alpha0 ∧ 2 <= gadgetN ∧
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        rankLogRate
        (Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det))
        delta ∧
      PallLean.Paper93.NFrame.AdmissibleGauge Pi ∧
      RouteBProjectionRankCompatible M n hn2 htb hns A.rank Pi ∧
      RouteBFunctorialTransportCertificate M n hn2 htb hns Pi

/-- The reduced certificate supplies the existing derived auto-norm matrix
certificate.  The shifted eigenvalue field is discharged by CFC, the norm
bound is the canonical PSD sum bound, and the broad matrix-to-SAT package is
constructed from the primitive transport certificate. -/
theorem routeBStrictAutoNormDerivedMatrixCertificate_of_reducedCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (cert : RouteBReducedCertificate M n hn2 htb hns) :
    RouteBStrictAutoNormDerivedMatrixCertificate M n hn2 htb hns := by
  rcases cert with
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, delta, rankLogRate, A, hA, Pi,
      htheta, halpha, halpha0, hgadgetN,
      hlower, hAdm, hcompat, htransport⟩
  refine
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, delta, rankLogRate, A, hA, Pi,
      htheta, halpha, halpha0, hgadgetN,
      hlower, hAdm, hcompat, ?_⟩
  exact
    routeBMatrixToSATGaugeFunctoriality_of_transportCertificate
      M n hn2 htb hns alpha beta alpha0 kappa G chi Phi
      (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
      (bridgeBLogCapacity theta (routeBEigenvalueSumNormBound A hA))
      delta A.rank Pi htransport

/-- Reduced certificates supply the generic Route B per-instance certificate
used by the final assembly. -/
theorem routeBPerInstanceCertificate_of_reducedCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (cert : RouteBReducedCertificate M n hn2 htb hns) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_derivedMatrixCertificate
    (routeBStrictAutoNormDerivedMatrixCertificate_of_reducedCertificate cert)

/-- Reduced certificate form of the per-instance rich-projection target. -/
theorem cookLevinRichProjectionTarget_of_reducedCertificate
    {M : DTM} {n : Nat} {hn : n ≥ 2 ^ 804} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (cert : RouteBReducedCertificate M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_routeBCertificate
    (hn := hn)
    (routeBPerInstanceCertificate_of_reducedCertificate cert)

/-- Uniform reduced certificates discharge the Route B rich-projection
frontier. -/
theorem cookLevinRichProjectionDischarge_of_reducedCertificates
    (hcert :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        RouteBReducedCertificate M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_of_routeBCertificates
    (fun M n hn hn2 htb hns hdec =>
      routeBPerInstanceCertificate_of_reducedCertificate
        (hcert M n hn hn2 htb hns hdec))

/-- Contradiction-strength endpoint from uniform reduced Route B
certificates. -/
theorem noBoundedSATDeciderAtPaperScale_of_reducedCertificates
    (hcert :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        RouteBReducedCertificate M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBCertificates
    (fun M n hn hn2 htb hns hdec =>
      routeBPerInstanceCertificate_of_reducedCertificate
        (hcert M n hn hn2 htb hns hdec))

/-! ## Axiom audit anchors -/

#print axioms routeBStrictAutoNormDerivedMatrixCertificate_of_reducedCertificate
#print axioms routeBPerInstanceCertificate_of_reducedCertificate
#print axioms cookLevinRichProjectionTarget_of_reducedCertificate
#print axioms cookLevinRichProjectionDischarge_of_reducedCertificates
#print axioms noBoundedSATDeciderAtPaperScale_of_reducedCertificates

end PallLean.Paper93.Paper283
