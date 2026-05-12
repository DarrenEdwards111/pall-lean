import PallLean.Paper93.Paper283.RouteBRicherGaugeConcreteWImport

/-!
# Prepended finite-row map-preimage reduction

This file specializes the corrected finite-row SPDP map-preimage route to the
gauge whose first selected row is the concrete Cook-Levin NP identity-minor
witness and whose remaining rows are an arbitrary richer tail.

The result is a precise split of the remaining finite-row SPDP work:

* prove closure of the prepended head row under SPDP generator rows;
* prove closure of the richer tail rows under the same generators;
* prove the unprojected SPDP preimage condition.

Together these imply the concrete corrected Route B certificate without asking
for generator commutation with the arbitrary complement chosen by
`finiteRowsCandidateGauge`.
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
open PallLean.Paper93
open PallLean.Paper93.Spanning
open PallLean.Paper93.Wiring (concreteW)

attribute [local instance] Classical.dec

/-- Row closure for the concrete-NP-prepended finite rows splits into the
head-row closure and the richer tail-row closure. -/
theorem routeBRicherConcreteNPPrependedRows_rowClosure_of_head_tail
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hhead :
      forall (spdpKappa ell : Nat)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ->
        shift.totalDegree <= ell ->
        shift.vars <= S.toFinset ->
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ->
        routeBSPDPGeneratorRow M n hn2 htb hns
            (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) S shift
          ∈ finiteRowsSubmodule
              (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))
    (htail :
      forall (spdpKappa ell : Nat)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ->
        shift.totalDegree <= ell ->
        shift.vars <= S.toFinset ->
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ->
        forall i : Fin m,
          routeBSPDPGeneratorRow M n hn2 htb hns (tail i) S shift
            ∈ finiteRowsSubmodule
                (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)) :
    RouteBRicherGaugeFiniteRowsSPDPRowClosure M n hn2 htb hns
      (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail) := by
  constructor
  intro spdpKappa ell S shift hSlen hshiftDegree hshiftVars hadm i
  refine Fin.cases ?_ ?_ i
  · simpa [routeBRicherConcreteNPPrependedRows] using
      hhead spdpKappa ell S shift hSlen hshiftDegree hshiftVars hadm
  · intro j
    simpa [routeBRicherConcreteNPPrependedRows] using
      htail spdpKappa ell S shift hSlen hshiftDegree hshiftVars hadm j

/-- The concrete-NP-prepended finite rows satisfy the map-preimage SPDP
surface once row closure and the unprojected preimage side are supplied. -/
theorem routeBRicherConcreteNPPrependedRows_mapPreimage_of_head_tail_unprojectedPreimage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hhead :
      forall (spdpKappa ell : Nat)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ->
        shift.totalDegree <= ell ->
        shift.vars <= S.toFinset ->
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ->
        routeBSPDPGeneratorRow M n hn2 htb hns
            (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) S shift
          ∈ finiteRowsSubmodule
              (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))
    (htail :
      forall (spdpKappa ell : Nat)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ->
        shift.totalDegree <= ell ->
        shift.vars <= S.toFinset ->
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ->
        forall i : Fin m,
          routeBSPDPGeneratorRow M n hn2 htb hns (tail i) S shift
            ∈ finiteRowsSubmodule
                (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPUnprojectedPreimage M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)) :
    RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns
      (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail) :=
  routeBRicherGaugeFiniteRowsSPDPMapPreimage_of_unprojectedPreimage
    M n hn2 htb hns
    (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)
    (routeBRicherGaugeFiniteRowsSPDPClosure_of_rowClosure
      M n hn2 htb hns
      (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)
      (routeBRicherConcreteNPPrependedRows_rowClosure_of_head_tail
        M n hn2 htb hns tail hhead htail))
    preimage

/-- Corrected concrete Route B certificate with the finite-row map-preimage
side split into head closure, tail closure, and unprojected preimage.

This is the direct working surface for the next gauge-transport round: it
keeps the NP row concrete, consumes concreteW row embeddings for the P-window
cover, and avoids arbitrary-complement generator commutation. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_headTailRowClosure_unprojectedPreimage_rowEmbeddings_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hN : 1 <= N) (hrowCount : m + 1 <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (hhead :
      forall (spdpKappa ell : Nat)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ->
        shift.totalDegree <= ell ->
        shift.vars <= S.toFinset ->
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ->
        routeBSPDPGeneratorRow M n hn2 htb hns
            (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) S shift
          ∈ finiteRowsSubmodule
              (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))
    (htail :
      forall (spdpKappa ell : Nat)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ->
        shift.totalDegree <= ell ->
        shift.vars <= S.toFinset ->
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ->
        forall i : Fin m,
          routeBSPDPGeneratorRow M n hn2 htb hns (tail i) S shift
            ∈ finiteRowsSubmodule
                (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPUnprojectedPreimage M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_rowEmbeddings_deltaEqRateKappa
    (N := N) (d := d)
    M n hn hn2 htb hns hn4 alpha beta alpha0 kappa gadgetN G chi Phi
    tail hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    (routeBRicherConcreteNPPrependedRows_mapPreimage_of_head_tail_unprojectedPreimage
      M n hn2 htb hns tail hhead htail preimage)
    hRowEmbeddings

/-- Same prepended-row SPDP split as
`routeBPerInstanceCertificate_of_prependedConcreteNP_headTailRowClosure_unprojectedPreimage_rowEmbeddings_deltaEqRateKappa`,
but with the P-side concreteW row-embedding input discharged through the
current direct branch-shape/transport/H4/I1-I2-I3 import adapter. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_headTailRowClosure_unprojectedPreimage_importedConcreteW_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hN : 1 <= N) (hrowCount : m + 1 <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (hhead :
      forall (spdpKappa ell : Nat)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ->
        shift.totalDegree <= ell ->
        shift.vars <= S.toFinset ->
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ->
        routeBSPDPGeneratorRow M n hn2 htb hns
            (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) S shift
          ∈ finiteRowsSubmodule
              (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))
    (htail :
      forall (spdpKappa ell : Nat)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ->
        shift.totalDegree <= ell ->
        shift.vars <= S.toFinset ->
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ->
        forall i : Fin m,
          routeBSPDPGeneratorRow M n hn2 htb hns (tail i) S shift
            ∈ finiteRowsSubmodule
                (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPUnprojectedPreimage M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))
    (hShape : CookLevinDirectBranchShapeWitnesses M n hn2 htb hns hn4)
    (hTransport : CookLevinConcreteWCanonicalRowTransport M n hn2 htb hns hn4)
    (hDeriv :
      DerivClosurePerType (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hI1 : ConcreteWProductGrouping n hn4)
    (hI2 : ConcreteWShiftClosure n hn4)
    (hI3 : ConcreteWMlprojClosure n hn4) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_importedConcreteW_deltaEqRateKappa
    (N := N) (d := d)
    M n hn hn2 htb hns hn4 alpha beta alpha0 kappa gadgetN G chi Phi
    tail hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    (routeBRicherConcreteNPPrependedRows_mapPreimage_of_head_tail_unprojectedPreimage
      M n hn2 htb hns tail hhead htail preimage)
    hShape hTransport hDeriv hI1 hI2 hI3

/-! ## Axiom audit anchors -/

#print axioms routeBRicherConcreteNPPrependedRows_rowClosure_of_head_tail
#print axioms routeBRicherConcreteNPPrependedRows_mapPreimage_of_head_tail_unprojectedPreimage
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_headTailRowClosure_unprojectedPreimage_rowEmbeddings_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_headTailRowClosure_unprojectedPreimage_importedConcreteW_deltaEqRateKappa

end PallLean.Paper93.Paper283
