import PallLean.Paper93.Paper283.BridgeAKappaTwoFourIdentitiesAssembled
import PallLean.Paper93.Paper283.BridgeAKappaGeneralRouteBFinal

/-!
# κ = 2 real local-block integration for Bridge A / Route B

This file consumes the closed theorem
`cookLevinLocalBlockQ_rank_two_le_real_kappaTwo` and turns it into the
Bridge A data surface used by the Route B integration layer.

The result is deliberately routed through the *real local-block* gadget
family.  The closed κ = 2 theorem proves

`2 <= mlBlockedSpdpRank ... 2 2 (cookLevinLocalBlockQ ...)`.

It does not prove the equality demanded by the legacy pocket-family adapter

`real local-block SPDP rank = (cookLevinPocketLocalGadgetFamily ...).rank`.

Consequently the final theorem below bypasses the pocket-family interface and
feeds the actual real local-block gadget family into the generic Route B
`gadgetFamily` arguments.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open TuringMachine
open PaperFaithfulSeparation
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-! ## Section A: κ = 2 Bridge A data from interior compiler blocks -/

/-- Selected κ = 2 interior compiler block for each Route B vertex.  The
index proof is immediate from the closed theorem's stronger interior side
condition `3 * k + 3 < n`. -/
noncomputable def kappaTwoInteriorBlockOfVertex
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (_G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (blockIndex : Fin N -> Nat)
    (hk2 : forall v : Fin N, 3 * blockIndex v + 3 < n) :
    Fin N -> Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks :=
  fun v => ⟨blockIndex v, by
    have hkv := hk2 v
    rw [cook_levin_numBlocks]
    omega⟩

/-- Energy-to-rank target for κ = 2, using the closed real local theorem at
each selected interior block.  The local energy hypothesis is not used here:
the κ = 2 rank lower bound is unconditional for every interior block. -/
theorem cookLevinLocalBlockQEnergyToRankTarget_two_of_interiorBlockIndices
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (blockIndex : Fin N -> Nat)
    (hk1 : forall v : Fin N, 1 <= blockIndex v)
    (hk2 : forall v : Fin N, 3 * blockIndex v + 3 < n) :
    CookLevinLocalBlockQEnergyToRankTarget
      M n hn htb hns alpha beta alpha0 2 G chi Phi
      (kappaTwoInteriorBlockOfVertex M n hn htb hns G blockIndex hk2) := by
  intro v _henergy
  simpa [kappaTwoInteriorBlockOfVertex] using
    (cookLevinLocalBlockQ_rank_two_le_real_kappaTwo
      M n hn htb hns (blockIndex v) (hk1 v) (hk2 v))

/-- Closed κ = 2 `CookLevinLocalBlockQBridgeAData` for selected interior
compiler blocks. -/
noncomputable def cookLevinLocalBlockQBridgeAData_two_of_interiorBlockIndices
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (blockIndex : Fin N -> Nat)
    (hk1 : forall v : Fin N, 1 <= blockIndex v)
    (hk2 : forall v : Fin N, 3 * blockIndex v + 3 < n) :
    CookLevinLocalBlockQBridgeAData
      M n hn htb hns alpha beta alpha0 2 G chi Phi where
  blockOfVertex :=
    kappaTwoInteriorBlockOfVertex M n hn htb hns G blockIndex hk2
  energy_to_spdpRank :=
    cookLevinLocalBlockQEnergyToRankTarget_two_of_interiorBlockIndices
      M n hn htb hns alpha beta alpha0 G chi Phi blockIndex hk1 hk2

/-! ## Section B: real local-block Route B gadget family -/

/-- Polynomial-bearing real local-block gadget family obtained from the closed
κ = 2 interior-block data. -/
noncomputable def cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_two_of_interiorBlockIndices
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (blockIndex : Fin N -> Nat)
    (hk1 : forall v : Fin N, 1 <= blockIndex v)
    (hk2 : forall v : Fin N, 3 * blockIndex v + 3 < n) :
    forall v : Fin N,
      BridgeAPolynomialLocalGadget
        alpha beta alpha0 2 G chi Phi v :=
  cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_of_data
    M n hn htb hns alpha beta alpha0 2 G chi Phi
    (cookLevinLocalBlockQBridgeAData_two_of_interiorBlockIndices
      M n hn htb hns alpha beta alpha0 G chi Phi blockIndex hk1 hk2)

/-- Rank-only real local-block gadget family obtained by forgetting the
polynomial payload of the closed κ = 2 local-block family. -/
noncomputable def cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_of_interiorBlockIndices
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (blockIndex : Fin N -> Nat)
    (hk1 : forall v : Fin N, 1 <= blockIndex v)
    (hk2 : forall v : Fin N, 3 * blockIndex v + 3 < n) :
    forall v : Fin N, LocalGadget N v :=
  cookLevinLocalBlockQ_routeBLocalGadgetFamily_of_data
    M n hn htb hns alpha beta alpha0 2 G chi Phi
    (cookLevinLocalBlockQBridgeAData_two_of_interiorBlockIndices
      M n hn htb hns alpha beta alpha0 G chi Phi blockIndex hk1 hk2)

/-- Pointwise Bridge A rank hypothesis for the real local-block κ = 2 gadget
family. -/
theorem cookLevinLocalBlockQ_routeB_hGadgetRank_two_of_interiorBlockIndices
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (blockIndex : Fin N -> Nat)
    (hk1 : forall v : Fin N, 1 <= blockIndex v)
    (hk2 : forall v : Fin N, 3 * blockIndex v + 3 < n) :
    forall v : Fin N,
      alpha0 <= localEnergy alpha beta G chi Phi v ->
        (2 : Nat) <=
          (cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_of_interiorBlockIndices
            M n hn htb hns alpha beta alpha0 G chi Phi
            blockIndex hk1 hk2 v).rank := by
  exact
    cookLevinLocalBlockQ_routeB_hGadgetRank_of_data
      M n hn htb hns alpha beta alpha0 2 G chi Phi
      (cookLevinLocalBlockQBridgeAData_two_of_interiorBlockIndices
        M n hn htb hns alpha beta alpha0 G chi Phi blockIndex hk1 hk2)

/-- Active-set rank budget for the real local-block κ = 2 gadget family. -/
theorem cookLevinLocalBlockQ_routeB_activeSet_rank_budget_two_of_interiorBlockIndices
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha0 : 0 < alpha0)
    (blockIndex : Fin N -> Nat)
    (hk1 : forall v : Fin N, 1 <= blockIndex v)
    (hk2 : forall v : Fin N, 3 * blockIndex v + 3 < n) :
    (activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card * 2 <=
      ∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
        (cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_of_interiorBlockIndices
          M n hn htb hns alpha beta alpha0 G chi Phi
          blockIndex hk1 hk2 v).rank := by
  exact
    bridgeA_activeSet_rank_budget
      alpha beta alpha0 2 G chi Phi
      (cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_of_interiorBlockIndices
        M n hn htb hns alpha beta alpha0 G chi Phi blockIndex hk1 hk2)
      halpha0
      (cookLevinLocalBlockQ_routeB_hGadgetRank_two_of_interiorBlockIndices
        M n hn htb hns alpha beta alpha0 G chi Phi blockIndex hk1 hk2)

/-! ## Section C: Route B target through the real local-block family -/

/-- Final target theorem for the κ = 2 real-local path.

The rank/log-det lower package and the Route B functoriality package are both
stated for
`cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_of_interiorBlockIndices`.
This is the replacement for the legacy `hrealizesPocket` route: no equality
with `cookLevinPocketLocalGadgetFamily` is assumed. -/
theorem cookLevinRichProjectionTarget_of_kappaTwoInteriorBlocks_realLocal_rankLogDet_transport
    {M : TuringMachine.DTM} {n : Nat} {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {N d : Nat}
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (blockIndex : Fin N -> Nat)
    (hk1 : forall v : Fin N, 1 <= blockIndex v)
    (hk2 : forall v : Fin N, 3 * blockIndex v + 3 < n)
    (halpha0 : 0 < alpha0)
    {theta normBound logDet delta rankLogRate : Real} {rankA : Nat}
    {eigenvalues : Fin N -> Real}
    (htheta : 0 < theta) (hnorm : 0 < normBound)
    (hspec :
      BridgeBSpectralHypotheses theta normBound logDet rankA eigenvalues)
    (hlower :
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 2 G chi Phi
        (cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_of_interiorBlockIndices
          M n hn2 htb hns alpha beta alpha0 G chi Phi blockIndex hk1 hk2)
        rankLogRate logDet delta)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hcompat :
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi)
    (hfun :
      RouteBMatrixToSATGaugeFunctoriality
        M n hn2 htb hns alpha beta alpha0 2 G chi Phi
        (cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_of_interiorBlockIndices
          M n hn2 htb hns alpha beta alpha0 G chi Phi blockIndex hk1 hk2)
        (bridgeBLogCapacity theta normBound) delta rankA Pi) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns := by
  exact
    cookLevinRichProjectionTarget_of_cookLevinLocalBlockQBridgeAData_realLocal_rankLogDet_transport
      (M := M) (n := n) (hn := hn) (hn2 := hn2) (htb := htb) (hns := hns)
      alpha beta alpha0 2 G chi Phi
      (cookLevinLocalBlockQBridgeAData_two_of_interiorBlockIndices
        M n hn2 htb hns alpha beta alpha0 G chi Phi blockIndex hk1 hk2)
      halpha0 htheta hnorm hspec
      (by
        simpa [cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_of_interiorBlockIndices]
          using hlower)
      Pi hcompat
      (by
        simpa [cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_of_interiorBlockIndices]
          using hfun)

/-! ## Axiom audit anchors -/

#print axioms kappaTwoInteriorBlockOfVertex
#print axioms cookLevinLocalBlockQEnergyToRankTarget_two_of_interiorBlockIndices
#print axioms cookLevinLocalBlockQBridgeAData_two_of_interiorBlockIndices
#print axioms cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_two_of_interiorBlockIndices
#print axioms cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_of_interiorBlockIndices
#print axioms cookLevinLocalBlockQ_routeB_hGadgetRank_two_of_interiorBlockIndices
#print axioms cookLevinLocalBlockQ_routeB_activeSet_rank_budget_two_of_interiorBlockIndices
#print axioms cookLevinRichProjectionTarget_of_kappaTwoInteriorBlocks_realLocal_rankLogDet_transport

end PallLean.Paper93.Paper283
