import PallLean.Paper93.Paper283.BridgeAKappaGeneralRouteBIntegration
import PallLean.Paper93.Paper283.BridgeAKappaOneRouteBIntegration

/-!
# General-kappa real Bridge A data to final Route B certificates

This file is deliberately only an integration layer.  It composes the checked
real Cook-Levin local-block Bridge A package with the existing Route B
rank-logdet/transport constructors.

There are now two routes:

* the legacy pocket-family route, which still requires the explicit
  rank-realization equality from the real local-block gadget to the analytic
  `cookLevinPocketLocalGadgetFamily` surface;
* the real-local route, which bypasses that equality and threads the
  polynomial local-block gadget family through the generic Route B
  `gadgetFamily` interfaces directly.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

/-! ## Real-local route, bypassing the pocket-family equality -/

/-- Analytic Route B rank core from real Cook-Levin local-block Bridge A data.

This is the honest bypass for the `hrealizesPocket` comparison: the
`gadgetFamily` used by the rank/log-det lower package is the forgotten
rank-only family of the actual real local-block polynomials, not the matrix
`pocketFamily` surface. -/
theorem routeBAnalyticRankCoreOutput_of_cookLevinLocalBlockQBridgeAData_rankLogDet
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (data :
      CookLevinLocalBlockQBridgeAData
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi)
    (halpha0 : 0 < alpha0)
    {theta normBound logDet delta rankLogRate : Real} {rankA : Nat}
    {eigenvalues : Fin N -> Real}
    (htheta : 0 < theta) (hnorm : 0 < normBound)
    (hspec :
      BridgeBSpectralHypotheses theta normBound logDet rankA eigenvalues)
    (hlower :
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 kappa G chi Phi
        (cookLevinLocalBlockQ_routeBLocalGadgetFamily_of_data
          M n hn2 htb hns alpha beta alpha0 kappa G chi Phi data)
        rankLogRate logDet delta) :
    RouteBAnalyticRankCoreOutput
      alpha beta alpha0 kappa G chi Phi
      (cookLevinLocalBlockQ_routeBLocalGadgetFamily_of_data
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi data)
      (bridgeBLogCapacity theta normBound) delta rankA := by
  exact
    routeBAnalyticRankCoreOutput_of_hypotheses
      alpha beta alpha0 kappa G chi Phi
      (cookLevinLocalBlockQ_routeBLocalGadgetFamily_of_data
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi data)
      halpha0
      (cookLevinLocalBlockQ_routeB_hGadgetRank_of_data
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi data)
      (bridgeBLogCapacity_pos htheta hnorm)
      (bridgeA_logDet_lower_from_rank_budget
        alpha beta alpha0 kappa G chi Phi
        (cookLevinLocalBlockQ_routeBLocalGadgetFamily_of_data
          M n hn2 htb hns alpha beta alpha0 kappa G chi Phi data)
        halpha0
        (cookLevinLocalBlockQ_routeB_hGadgetRank_of_data
          M n hn2 htb hns alpha beta alpha0 kappa G chi Phi data)
        hlower)
      (bridgeB_logdet_upper_from_spectral_hypotheses
        (N := N) (theta := theta) (normBound := normBound)
        (logDet := logDet) (rankA := rankA)
        (eigenvalues := eigenvalues) htheta hspec)

/-- Real Cook-Levin local-block Bridge A data feeds the final
`CookLevinRichProjectionTarget` through the generic Route B `gadgetFamily`
surface.

This theorem intentionally does not produce the older
`RouteBPerInstanceCertificate`, whose fields are specialized to
`cookLevinPocketLocalGadgetFamily`.  It replaces that pocket-specialized
surface by using the actual real local-block polynomial gadget family
throughout the analytic and functoriality hypotheses. -/
theorem cookLevinRichProjectionTarget_of_cookLevinLocalBlockQBridgeAData_realLocal_rankLogDet_transport
    {M : DTM} {n : Nat} {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (data :
      CookLevinLocalBlockQBridgeAData
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi)
    (halpha0 : 0 < alpha0)
    {theta normBound logDet delta rankLogRate : Real} {rankA : Nat}
    {eigenvalues : Fin N -> Real}
    (htheta : 0 < theta) (hnorm : 0 < normBound)
    (hspec :
      BridgeBSpectralHypotheses theta normBound logDet rankA eigenvalues)
    (hlower :
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 kappa G chi Phi
        (cookLevinLocalBlockQ_routeBLocalGadgetFamily_of_data
          M n hn2 htb hns alpha beta alpha0 kappa G chi Phi data)
        rankLogRate logDet delta)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hcompat :
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi)
    (hfun :
      RouteBMatrixToSATGaugeFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi
        (cookLevinLocalBlockQ_routeBLocalGadgetFamily_of_data
          M n hn2 htb hns alpha beta alpha0 kappa G chi Phi data)
        (bridgeBLogCapacity theta normBound) delta rankA Pi) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns := by
  exact
    cookLevinRichProjectionTarget_of_routeBMatrixFunctoriality
      M n hn hn2 htb hns
      alpha beta alpha0 kappa G chi Phi
      (cookLevinLocalBlockQ_routeBLocalGadgetFamily_of_data
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi data)
      (bridgeBLogCapacity theta normBound) delta rankA Pi
      (routeBAnalyticRankCoreOutput_of_cookLevinLocalBlockQBridgeAData_rankLogDet
        (M := M) (n := n) (hn2 := hn2) (htb := htb) (hns := hns)
        alpha beta alpha0 kappa G chi Phi data
        halpha0 htheta hnorm hspec hlower)
      hcompat hfun

/-! ## Legacy pocket-family route -/

/-- Real Cook-Levin local-block Bridge A data, together with the explicit
pocket-rank realization equality, gives the final per-instance Route B
certificate once the existing spectral, rank-logdet, and transport inputs are
provided. -/
theorem routeBPerInstanceCertificate_of_cookLevinLocalBlockQBridgeAData_rankLogDet_transport
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (data :
      CookLevinLocalBlockQBridgeAData
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi)
    (hrealizesPocket :
      forall v : Fin N,
        ((cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_of_data
          M n hn2 htb hns alpha beta alpha0 kappa G chi Phi data v).toLocalGadget).rank =
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN v).rank)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hgadgetN : 2 <= gadgetN)
    {theta normBound logDet delta rankLogRate : Real} {rankA : Nat}
    {eigenvalues : Fin N -> Real}
    (htheta : 0 < theta) (hnorm : 0 < normBound)
    (hspec :
      BridgeBSpectralHypotheses theta normBound logDet rankA eigenvalues)
    (hlower :
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        rankLogRate logDet delta)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hAdm : PallLean.Paper93.NFrame.AdmissibleGauge Pi)
    (hcompat :
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi)
    (htransport :
      RouteBFunctorialTransportCertificate M n hn2 htb hns Pi) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  exact
    routeBPerInstanceCertificate_of_bridgeA_rankLogDet_transport
      (M := M) (n := n) (hn2 := hn2) (htb := htb) (hns := hns)
      alpha beta alpha0 kappa gadgetN G chi Phi
      halpha halpha0 hgadgetN htheta hnorm hspec
      (routeBCompilerLocalBridgeA_of_cookLevinLocalBlockQBridgeAData
        M n hn2 htb hns alpha beta alpha0 kappa gadgetN G chi Phi
        data hrealizesPocket)
      hlower Pi hAdm hcompat htransport

/-- The `kappa = 1` specialization using the checked one-assign
Cook-Levin local-block Bridge A data. -/
theorem routeBPerInstanceCertificate_of_cookLevinLocalBlockQBridgeAData_one_assign_rankLogDet_transport
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {d : Nat}
    (alpha beta alpha0 : Real) (gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed n d)
    (chi : TseitinCharge n) (Phi : Fin n -> Real)
    (hrealizesPocket :
      forall v : Fin n,
        ((cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_one_assign
          M n hn2 htb hns alpha beta alpha0 G chi Phi v).toLocalGadget).rank =
        (cookLevinPocketLocalGadgetFamily n alpha 1 gadgetN v).rank)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hgadgetN : 2 <= gadgetN)
    {theta normBound logDet delta rankLogRate : Real} {rankA : Nat}
    {eigenvalues : Fin n -> Real}
    (htheta : 0 < theta) (hnorm : 0 < normBound)
    (hspec :
      BridgeBSpectralHypotheses theta normBound logDet rankA eigenvalues)
    (hlower :
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 1 G chi Phi
        (cookLevinPocketLocalGadgetFamily n alpha 1 gadgetN)
        rankLogRate logDet delta)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hAdm : PallLean.Paper93.NFrame.AdmissibleGauge Pi)
    (hcompat :
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi)
    (htransport :
      RouteBFunctorialTransportCertificate M n hn2 htb hns Pi) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  let data :=
    cookLevinLocalBlockQBridgeAData_one_assign
      M n hn2 htb hns alpha beta alpha0 G chi Phi
  exact
    routeBPerInstanceCertificate_of_cookLevinLocalBlockQBridgeAData_rankLogDet_transport
      (M := M) (n := n) (hn2 := hn2) (htb := htb) (hns := hns)
      alpha beta alpha0 1 gadgetN G chi Phi data
      (by
        intro v
        simpa [
          data,
          cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_one_assign,
          cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_of_data
        ] using hrealizesPocket v)
      halpha halpha0 hgadgetN htheta hnorm hspec
      hlower Pi hAdm hcompat htransport

/-! ## Axiom audit anchors -/

#print axioms routeBAnalyticRankCoreOutput_of_cookLevinLocalBlockQBridgeAData_rankLogDet
#print axioms cookLevinRichProjectionTarget_of_cookLevinLocalBlockQBridgeAData_realLocal_rankLogDet_transport
#print axioms routeBPerInstanceCertificate_of_cookLevinLocalBlockQBridgeAData_rankLogDet_transport
#print axioms routeBPerInstanceCertificate_of_cookLevinLocalBlockQBridgeAData_one_assign_rankLogDet_transport

end PallLean.Paper93.Paper283
