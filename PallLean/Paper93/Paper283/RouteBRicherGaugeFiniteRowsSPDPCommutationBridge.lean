import PallLean.Paper93.Paper283.RouteBRicherGaugeFiniteRowsSPDPFrontier

/-!
# Finite-row SPDP map-preimage from generator commutation

This file adds the focused bridge from finite-row generator commutation to the
map-preimage SPDP surface consumed by the finite-row Route B certificate.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.BridgeB
open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Finite-row specialization of generator commutation, stated directly in
terms of the concrete Route B SPDP generator row. -/
def RouteBRicherGaugeFiniteRowsSPDPGeneratorCommutation
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) : Prop :=
  forall (spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    routeBSPDPGeneratorRow M n hn2 htb hns
        ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)) p)
        S shift =
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows))
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)

/-- The general richer-gauge generator commutation criterion specializes to
the finite-row concrete generator-row commutation condition. -/
theorem routeBRicherGaugeFiniteRowsSPDPGeneratorCommutation_of_generatorCommutation
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcomm :
      RouteBRicherGaugeGeneratorCommutation M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)) :
    RouteBRicherGaugeFiniteRowsSPDPGeneratorCommutation
      M n hn2 htb hns rows := by
  intro spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm
  exact hcomm spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm

/-- Finite-row generator commutation supplies the map-preimage witness needed
for SPDP image containment. -/
theorem routeBRicherGaugeFiniteRowsSPDPMapPreimage_of_generatorRowCommutation
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcomm :
      RouteBRicherGaugeFiniteRowsSPDPGeneratorCommutation
        M n hn2 htb hns rows) :
    RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns rows := by
  constructor
  intro spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm
  refine
    ⟨routeBSPDPGeneratorRow M n hn2 htb hns p S shift, ?_, ?_⟩
  · exact
      Submodule.subset_span
        ⟨S, shift, hSlen, hshiftDegree, hshiftVars, hadm, rfl⟩
  · exact (hcomm spdpKappa ell p S shift
      hSlen hshiftDegree hshiftVars hadm).symm

/-- General richer-gauge generator commutation gives the finite-row
map-preimage SPDP surface. -/
theorem routeBRicherGaugeFiniteRowsSPDPMapPreimage_of_generatorCommutation
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcomm :
      RouteBRicherGaugeGeneratorCommutation M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)) :
    RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns rows :=
  routeBRicherGaugeFiniteRowsSPDPMapPreimage_of_generatorRowCommutation
    M n hn2 htb hns rows
    (routeBRicherGaugeFiniteRowsSPDPGeneratorCommutation_of_generatorCommutation
      M n hn2 htb hns rows hcomm)

/-- Concrete finite-row Route B assembly with the SPDP side discharged by
finite-row generator commutation. -/
theorem routeBPerInstanceCertificate_of_finiteRowsSPDPGeneratorCommutation_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hN : 1 <= N) (hrowCount : m <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (hcomm :
      RouteBRicherGaugeFiniteRowsSPDPGeneratorCommutation
        M n hn2 htb hns rows)
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
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_finiteRowsSPDPMapPreimage_deltaEqRateKappa
    (N := N) (d := d)
    M n hn2 htb hns alpha beta alpha0 kappa gadgetN G chi Phi
    rows hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    (routeBRicherGaugeFiniteRowsSPDPMapPreimage_of_generatorRowCommutation
      M n hn2 htb hns rows hcomm)
    cover Q i hrow hextract hsource

/-- Concrete finite-row Route B assembly with the SPDP side discharged by the
general richer-gauge generator commutation criterion. -/
theorem routeBPerInstanceCertificate_of_finiteRowsSPDPGeneralCommutation_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hN : 1 <= N) (hrowCount : m <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (hcomm :
      RouteBRicherGaugeGeneratorCommutation M n hn2 htb hns
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
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_finiteRowsSPDPGeneratorCommutation_deltaEqRateKappa
    (N := N) (d := d)
    M n hn2 htb hns alpha beta alpha0 kappa gadgetN G chi Phi
    rows hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    (routeBRicherGaugeFiniteRowsSPDPGeneratorCommutation_of_generatorCommutation
      M n hn2 htb hns rows hcomm)
    cover Q i hrow hextract hsource

/-! ## Axiom audit anchors -/

#print axioms RouteBRicherGaugeFiniteRowsSPDPGeneratorCommutation
#print axioms routeBRicherGaugeFiniteRowsSPDPGeneratorCommutation_of_generatorCommutation
#print axioms routeBRicherGaugeFiniteRowsSPDPMapPreimage_of_generatorRowCommutation
#print axioms routeBRicherGaugeFiniteRowsSPDPMapPreimage_of_generatorCommutation
#print axioms routeBPerInstanceCertificate_of_finiteRowsSPDPGeneratorCommutation_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_finiteRowsSPDPGeneralCommutation_deltaEqRateKappa

end PallLean.Paper93.Paper283
