import PallLean.Paper93.Paper283.RouteBFinalAssembly
import PallLean.Paper93.Paper283.RouteBRicherGaugeRankBudget

/-!
# Route B Bridge A integration

This file isolates the paper-faithful Bridge A input in the active Route B
certificate path.

The load-bearing hypothesis is the per-vertex local-gadget theorem

`alpha0 <= localEnergy alpha beta G chi Phi v ->
  kappa <= (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN v).rank`.

Together with the existing rank-logdet lower package, this is exactly what
turns the Bridge A active-set rank budget into the scalar lower-logdet field
consumed by `RouteBPerInstanceCertificate`.  The finite-row specialization at
the end threads the same Bridge A input through the current P-window transport
path for richer Route B gauges.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

/-- The per-vertex Bridge A theorem for the compiler-given Cook-Levin pocket
local gadget family. -/
def RouteBCompilerLocalBridgeA {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) : Prop :=
  forall v : Fin N,
    alpha0 <= localEnergy alpha beta G chi Phi v ->
      kappa <=
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN v).rank

/-- Bridge A, in per-vertex compiler-local form, is exactly the missing input
needed to turn a rank-logdet package into Route B's scalar lower-logdet field. -/
theorem routeB_lowerLogDet_of_compilerLocalBridgeA_rankLogDet
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha0 : 0 < alpha0)
    (hBridgeA :
      RouteBCompilerLocalBridgeA alpha beta alpha0 kappa gadgetN G chi Phi)
    {rankLogRate logDet delta : Real}
    (hlower :
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        rankLogRate logDet delta) :
    delta *
        ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
          Real) <= logDet :=
  bridgeA_logDet_lower_from_rank_budget
    alpha beta alpha0 kappa G chi Phi
    (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
    halpha0 hBridgeA hlower

/-- Route B per-instance certificate constructor with Bridge A supplied as the
explicit per-vertex compiler-local theorem rather than hidden behind the
checked uniform pocket-rank shortcut. -/
theorem routeBPerInstanceCertificate_of_bridgeA_rankLogDet_transport
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
    (hBridgeA :
      RouteBCompilerLocalBridgeA alpha beta alpha0 kappa gadgetN G chi Phi)
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
  refine
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, normBound, logDet, delta, rankA, eigenvalues, Pi,
      halpha, halpha0, hgadgetN, htheta, hnorm, hspec, ?_,
      hAdm, hcompat, ?_⟩
  · exact
      routeB_lowerLogDet_of_compilerLocalBridgeA_rankLogDet
        alpha beta alpha0 kappa gadgetN G chi Phi
        halpha0 hBridgeA hlower
  · exact
      routeBMatrixToSATGaugeFunctoriality_of_transportCertificate
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        (bridgeBLogCapacity theta normBound) delta rankA Pi
        htransport

/-- Finite-row/P-window specialization of the Bridge A integration theorem.

The P-window cover appears only through the primitive finite-row transport
certificate.  Bridge A supplies the lower-logdet field via the per-vertex
compiler-local rank theorem above. -/
theorem routeBPerInstanceCertificate_of_richerFiniteRows_bridgeA_rankLogDet
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
    (hBridgeA :
      RouteBCompilerLocalBridgeA alpha beta alpha0 kappa gadgetN G chi Phi)
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
    routeBPerInstanceCertificate_of_bridgeA_rankLogDet_transport
      (M := M) (n := n) (hn2 := hn2) (htb := htb) (hns := hns)
      alpha beta alpha0 kappa gadgetN G chi Phi
      halpha halpha0 hgadgetN htheta hnorm hspec
      hBridgeA hlower
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
      (routeBRicherFiniteRowsCandidateGauge_admissible
        M n hn2 htb hns rows)
      (routeBRicherFiniteRowsCandidateGauge_rankCompatible_of_rowCount_le
        M n hn2 htb hns rankA rows hrowRank)
      (routeBRicherFiniteRowsCandidateGauge_transportCertificate
        M n hn2 htb hns rows hcontain cover Q i hrow hextract hsource)

/-! ## Axiom audit anchors -/

#print axioms RouteBCompilerLocalBridgeA
#print axioms routeB_lowerLogDet_of_compilerLocalBridgeA_rankLogDet
#print axioms routeBPerInstanceCertificate_of_bridgeA_rankLogDet_transport
#print axioms routeBPerInstanceCertificate_of_richerFiniteRows_bridgeA_rankLogDet

end PallLean.Paper93.Paper283
