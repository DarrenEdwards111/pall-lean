import PallLean.Paper93.Paper283.RouteBBridgeAIntegration
import PallLean.Paper93.Paper283.BridgeASquareHelperExact

/-!
# Route B integration for the exact square-helper local polynomial

`BridgeASquareHelperExact` proves the concrete arbitrary-`kappa` local
polynomial rank equality

`mlBlockedSpdpRank ... (squareHelperQ kappa gadgetN) = kappa * gadgetN`.

This file connects that theorem to the active Route B Bridge A surface.  The
result is not a claim that the full Cook-Levin compiler has been refactored to
emit `squareHelperQ` syntactically.  It proves the currently exposed
compiler-pocket rank is realized by this exact SPDP local polynomial package,
and uses that realization to discharge `RouteBCompilerLocalBridgeA`.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

namespace BridgeAGeneralizedNonzeroWitness

/-- The exact square-helper local polynomial realizes the checked
Cook-Levin pocket rank used by the active Route B Bridge A surface. -/
theorem squareHelper_mlBlockedSpdpRank_eq_cookLevinPocketLocalGadget_rank
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N)
    (halpha : 0 < alpha) (hgadgetN : 1 <= gadgetN) :
    mlBlockedSpdpRank
        (discretePartition (squareHelperVarCount kappa gadgetN))
        kappa kappa (squareHelperQ kappa gadgetN) =
      ((cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN) v).rank :=
  (squareHelper_perVertexCompilerSPDPData
    alpha beta alpha0 kappa gadgetN G chi Phi v halpha hgadgetN).rank_eq_pocket

/-- The square-helper local polynomial gives the per-vertex compiler-local
Bridge A theorem consumed by Route B. -/
theorem routeBCompilerLocalBridgeA_of_squareHelperExact
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha : 0 < alpha) (hgadgetN : 2 <= gadgetN) :
    RouteBCompilerLocalBridgeA alpha beta alpha0 kappa gadgetN G chi Phi := by
  intro v _hE
  have hgadgetN_one : 1 <= gadgetN := by omega
  have hident :=
    squareHelper_mlBlockedSpdpRank_eq_cookLevinPocketLocalGadget_rank
      alpha beta alpha0 kappa gadgetN G chi Phi v halpha hgadgetN_one
  have hml :
      kappa <=
        mlBlockedSpdpRank
          (discretePartition (squareHelperVarCount kappa gadgetN))
          kappa kappa (squareHelperQ kappa gadgetN) := by
    rw [squareHelperExactRankTarget_closed kappa gadgetN]
    exact Nat.le_mul_of_pos_right kappa (by omega)
  simpa [hident] using hml

/-- Lower-logdet field with the per-vertex Bridge A rank input discharged by
the exact square-helper local polynomial. -/
theorem routeB_lowerLogDet_of_squareHelperExact_rankLogDet
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hgadgetN : 2 <= gadgetN)
    {rankLogRate logDet delta : Real}
    (hlower :
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        rankLogRate logDet delta) :
    delta *
        ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
          Real) <= logDet :=
  routeB_lowerLogDet_of_compilerLocalBridgeA_rankLogDet
    alpha beta alpha0 kappa gadgetN G chi Phi
    halpha0
    (routeBCompilerLocalBridgeA_of_squareHelperExact
      alpha beta alpha0 kappa gadgetN G chi Phi halpha hgadgetN)
    hlower

/-- Route B per-instance certificate constructor with Bridge A's local
compiler-rank input discharged by `squareHelperQ`.  The analytic lower-logdet,
projection compatibility, and SAT/SPDP transport certificates remain explicit. -/
theorem routeBPerInstanceCertificate_of_squareHelperExact_rankLogDet_transport
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
      (routeBCompilerLocalBridgeA_of_squareHelperExact
        alpha beta alpha0 kappa gadgetN G chi Phi halpha hgadgetN)
      hlower Pi hAdm hcompat htransport

/-- Finite-row/P-window Route B constructor with Bridge A's local rank input
discharged by the exact square-helper local polynomial. -/
theorem routeBPerInstanceCertificate_of_richerFiniteRows_squareHelperExact
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
    (htheta : 0 < theta) (hnorm : 0 < normBound)
    (hspec :
      BridgeBSpectralHypotheses theta normBound logDet rankA eigenvalues)
    (hlower :
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        rankLogRate logDet delta)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hrowRank : m <= rankA)
    (hcontain :
      RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows))
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (i : Fin m)
    (hrow :
      rows i =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  exact
    routeBPerInstanceCertificate_of_richerFiniteRows_bridgeA_rankLogDet
      (M := M) (n := n) (hn2 := hn2) (htb := htb) (hns := hns)
      alpha beta alpha0 kappa gadgetN G chi Phi
      halpha halpha0 hgadgetN htheta hnorm hspec
      (routeBCompilerLocalBridgeA_of_squareHelperExact
        alpha beta alpha0 kappa gadgetN G chi Phi halpha hgadgetN)
      hlower rows hrowRank hcontain cover Q i hrow hextract hsource

/-! ## Axiom audit anchors -/

#print axioms squareHelper_mlBlockedSpdpRank_eq_cookLevinPocketLocalGadget_rank
#print axioms routeBCompilerLocalBridgeA_of_squareHelperExact
#print axioms routeB_lowerLogDet_of_squareHelperExact_rankLogDet
#print axioms routeBPerInstanceCertificate_of_squareHelperExact_rankLogDet_transport
#print axioms routeBPerInstanceCertificate_of_richerFiniteRows_squareHelperExact

end BridgeAGeneralizedNonzeroWitness

end PallLean.Paper93.Paper283
