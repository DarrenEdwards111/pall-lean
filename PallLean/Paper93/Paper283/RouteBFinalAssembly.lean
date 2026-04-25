import PallLean.Paper93.Paper283.RouteBRound1Bridge
import PallLean.Paper93.Paper283.RouteBToSATGaugeBridge
import PallLean.Paper93.Paper283.BridgeBSpectralReal
import PallLean.Paper93.Paper283.BridgeALogDetLower
import PallLean.Paper93.Paper283.RouteBMatrixToSATGauge

/-!
# Route B final assembly surface

This file is the narrow end-to-end Route B assembly layer.  It does not assert
the final God-Move projection for free.  Instead it proves that explicit
Route B/N-Frame certificate data feeds the existing
`CookLevinRichProjectionTarget`.

The assembly uses only:

* checked Cook-Levin `κ`-pocket Bridge A gadget ranks;
* checked spectral Bridge B det/rank sandwich;
* the explicit matrix-rank-to-SAT/SPDP gauge conversion hypothesis.

No profile-template-collapse route is used here.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open TuringMachine
open PaperFaithfulSeparation
open PallLean.Paper93.DeepMath.PathB

/-- Explicit Route B analytic output from the concrete Cook-Levin pocket
Bridge A theorem plus the spectral Bridge B upper bound. -/
theorem routeBAnalyticRankCoreOutput_of_explicit_routeB_certificate
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hgadgetN : 2 <= gadgetN)
    {theta normBound logDet delta : Real} {rankA : Nat}
    {eigenvalues : Fin N -> Real}
    (htheta : 0 < theta) (hnorm : 0 < normBound)
    (hspec :
      BridgeBSpectralHypotheses theta normBound logDet rankA eigenvalues)
    (hLogLower :
      delta *
          ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
            Real) <= logDet) :
    RouteBAnalyticRankCoreOutput
      alpha beta alpha0 kappa G chi Phi
      (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
      (bridgeBLogCapacity theta normBound) delta rankA := by
  exact routeBAnalyticRankCoreOutput_of_hypotheses
    alpha beta alpha0 kappa G chi Phi
    (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
    halpha0
    (cookLevin_hGadgetRank_kappa
      alpha beta alpha0 kappa gadgetN G chi Phi halpha hgadgetN)
    (bridgeBLogCapacity_pos htheta hnorm)
    hLogLower
    (bridgeB_logdet_upper_from_spectral_hypotheses
      (N := N) (theta := theta) (normBound := normBound)
      (logDet := logDet) (rankA := rankA)
      (eigenvalues := eigenvalues) htheta hspec)

/-- Explicit per-instance final Route B assembly into the existing Cook-Levin
rich projection target. -/
theorem cookLevinRichProjectionTarget_of_explicit_routeB_certificate
    {M : DTM} {n : Nat} {hn : n ≥ 2 ^ 804} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hgadgetN : 2 <= gadgetN)
    {theta normBound logDet delta : Real} {rankA : Nat}
    {eigenvalues : Fin N -> Real}
    (htheta : 0 < theta) (hnorm : 0 < normBound)
    (hspec :
      BridgeBSpectralHypotheses theta normBound logDet rankA eigenvalues)
    (hLogLower :
      delta *
          ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
            Real) <= logDet)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (_hAdm : PallLean.Paper93.NFrame.AdmissibleGauge Pi)
    (hcompat :
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi)
    (hfun :
      RouteBMatrixToSATGaugeFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        (bridgeBLogCapacity theta normBound) delta rankA Pi) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_routeBNFrameGaugeSubgoals
    M n hn hn2 htb hns Pi
      (routeBNFrameGaugeSubgoals_of_routeBMatrixFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        (bridgeBLogCapacity theta normBound) delta rankA Pi
        (routeBAnalyticRankCoreOutput_of_explicit_routeB_certificate
          alpha beta alpha0 kappa gadgetN G chi Phi
          halpha halpha0 hgadgetN htheta hnorm hspec hLogLower)
        hcompat hfun)

/-- Existential certificate form of the explicit Route B data for one
Cook-Levin SAT-decider instance. -/
def RouteBPerInstanceCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (N d : Nat)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (theta normBound logDet delta : Real) (rankA : Nat)
    (eigenvalues : Fin N -> Real)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)),
      0 < alpha ∧ 0 < alpha0 ∧ 2 <= gadgetN ∧
      0 < theta ∧ 0 < normBound ∧
      BridgeBSpectralHypotheses theta normBound logDet rankA eigenvalues ∧
      delta *
          ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
            Real) <= logDet ∧
      PallLean.Paper93.NFrame.AdmissibleGauge Pi ∧
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi ∧
      RouteBMatrixToSATGaugeFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        (bridgeBLogCapacity theta normBound) delta rankA Pi

/-- Existential certificate form of the final per-instance Route B assembly. -/
theorem cookLevinRichProjectionTarget_of_routeBCertificate
    {M : DTM} {n : Nat} {hn : n ≥ 2 ^ 804} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (cert : RouteBPerInstanceCertificate M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns := by
  rcases cert with
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, normBound, logDet, delta, rankA, eigenvalues, Pi,
      halpha, halpha0, hgadgetN, htheta, hnorm, hspec, hLogLower,
      hAdm, hcompat, hfun⟩
  exact cookLevinRichProjectionTarget_of_explicit_routeB_certificate
    (hn := hn) alpha beta alpha0 kappa gadgetN G chi Phi
    halpha halpha0 hgadgetN htheta hnorm hspec hLogLower Pi hAdm
    hcompat hfun

/-- Uniform Route B certificates discharge the existing final rich-projection
frontier.  This is the precise Route B replacement for the old profile route. -/
theorem cookLevinRichProjectionDischarge_of_routeBCertificates
    (hcert :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        RouteBPerInstanceCertificate M n hn2 htb hns) :
    CookLevinRichProjectionDischarge := by
  intro M n hn hn2 htb hns hdec
  exact cookLevinRichProjectionTarget_of_routeBCertificate
    (hn := hn) (hcert M n hn hn2 htb hns hdec)

/-- Contradiction-strength Route B endpoint from uniform certificates.  This
is the strongest honest final theorem in this file: it is not unconditional,
but the single remaining hypothesis is now exactly the uniform Route B
certificate family. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBCertificates
    (hcert :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        RouteBPerInstanceCertificate M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mp
    (cookLevinRichProjectionDischarge_of_routeBCertificates hcert)

/-! ## Axiom audit anchors -/

#print axioms routeBAnalyticRankCoreOutput_of_explicit_routeB_certificate
#print axioms cookLevinRichProjectionTarget_of_explicit_routeB_certificate
#print axioms cookLevinRichProjectionTarget_of_routeBCertificate
#print axioms cookLevinRichProjectionDischarge_of_routeBCertificates
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBCertificates

end PallLean.Paper93.Paper283
