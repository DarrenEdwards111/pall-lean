import PallLean.Paper93.Paper283.RouteBFinalAssembly

/-!
# Route B lower log-det certificate constructors

This file strengthens the lower-logdet side of the final Route B per-instance
certificate.  The existing `RouteBPerInstanceCertificate` keeps the scalar
lower estimate

`delta * |activeSet| <= logDet`

as a field.  The constructors below discharge that field from the checked
Bridge A lower-logdet interfaces in `BridgeALogDetLower`.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open TuringMachine
open PaperFaithfulSeparation
open PallLean.Paper93.DeepMath.PathB

/-- Build the final Route B per-instance certificate when the lower log-det
input is supplied in Bridge A rank-budget form.

The spectral, admissibility, rank-compatibility, and matrix-to-SAT functorial
parts remain explicit. -/
theorem routeBPerInstanceCertificate_of_rank_logdet_lower
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hgadgetN : 2 <= gadgetN)
    {theta normBound logDet delta rankLogRate : Real} {rankA : Nat}
    {eigenvalues : Fin N -> Real}
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (htheta : 0 < theta) (hnorm : 0 < normBound)
    (hspec :
      BridgeBSpectralHypotheses theta normBound logDet rankA eigenvalues)
    (hlower :
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        rankLogRate logDet delta)
    (hAdm : PallLean.Paper93.NFrame.AdmissibleGauge Pi)
    (hcompat :
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi)
    (hfun :
      RouteBMatrixToSATGaugeFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        (bridgeBLogCapacity theta normBound) delta rankA Pi) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  refine
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, normBound, logDet, delta, rankA, eigenvalues, Pi,
      halpha, halpha0, hgadgetN, htheta, hnorm, hspec, ?_, hAdm,
      hcompat, hfun⟩
  exact bridgeA_cookLevin_logDet_lower_from_rank_budget
    alpha beta alpha0 kappa gadgetN G chi Phi
    halpha halpha0 hgadgetN hlower

/-- Build the final Route B per-instance certificate when the lower log-det
input is supplied by per-active-vertex Bridge A local contributions.

The spectral, admissibility, rank-compatibility, and matrix-to-SAT functorial
parts remain explicit. -/
theorem routeBPerInstanceCertificate_of_active_logdet_lower
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hgadgetN : 2 <= gadgetN)
    {theta normBound logDet delta : Real} {rankA : Nat}
    {eigenvalues : Fin N -> Real}
    (localLogDet : Fin N -> Real)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (htheta : 0 < theta) (hnorm : 0 < normBound)
    (hspec :
      BridgeBSpectralHypotheses theta normBound logDet rankA eigenvalues)
    (hlower :
      BridgeAActiveLogDetLowerHypotheses
        alpha beta alpha0 delta logDet G chi Phi localLogDet)
    (hAdm : PallLean.Paper93.NFrame.AdmissibleGauge Pi)
    (hcompat :
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi)
    (hfun :
      RouteBMatrixToSATGaugeFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        (bridgeBLogCapacity theta normBound) delta rankA Pi) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  refine
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, normBound, logDet, delta, rankA, eigenvalues, Pi,
      halpha, halpha0, hgadgetN, htheta, hnorm, hspec, ?_, hAdm,
      hcompat, hfun⟩
  exact bridgeA_logDet_lower_from_active_contributions
    alpha beta alpha0 delta logDet G chi Phi localLogDet hlower

/-! ## Axiom audit anchors -/

#print axioms routeBPerInstanceCertificate_of_rank_logdet_lower
#print axioms routeBPerInstanceCertificate_of_active_logdet_lower

end PallLean.Paper93.Paper283
