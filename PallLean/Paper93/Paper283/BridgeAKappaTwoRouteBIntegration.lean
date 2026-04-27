import PallLean.Paper93.Paper283.BridgeAKappaTwoFourIdentitiesAssembled
import PallLean.Paper93.Paper283.BridgeAKappaGeneralRouteBFinal
import PallLean.Paper93.Paper283.BridgeBShiftedEigenvalueCFC
import PallLean.Paper93.Paper283.RouteBFunctorialTransportCertificate
import PallLean.Paper93.Paper283.RouteBRicherGaugeConcreteMultilinearTail
import PallLean.Paper93.Paper283.RouteBRicherGaugeRankBudget

set_option exponentiation.threshold 1000

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

/-! ## Section D: fixed κ = 2 interior block and transport-certificate surface -/

/-- The default κ = 2 compiler block selection.  At paper scale, block `1` is
strictly interior because `3 * 1 + 3 < n` follows from `n >= 2^804`. -/
def kappaTwoDefaultBlockIndex {N : Nat} : Fin N -> Nat :=
  fun _ => 1

/-- Lower interior bound for the default κ = 2 block selection. -/
theorem kappaTwoDefaultBlockIndex_hk1 {N : Nat} :
    forall v : Fin N, 1 <= kappaTwoDefaultBlockIndex (N := N) v := by
  intro v
  simp [kappaTwoDefaultBlockIndex]

/-- Upper interior bound for the default κ = 2 block selection at paper scale. -/
theorem kappaTwoDefaultBlockIndex_hk2 {N n : Nat} (hn : n >= 2 ^ 804) :
    forall v : Fin N, 3 * kappaTwoDefaultBlockIndex (N := N) v + 3 < n := by
  intro v
  have hpow : (7 : Nat) <= 2 ^ 804 := by
    have h7 : (7 : Nat) <= 2 ^ 3 := by norm_num
    have hmono : (2 : Nat) ^ 3 <= 2 ^ 804 :=
      Nat.pow_le_pow_right
        (by norm_num : (2 : Nat) > 0)
        (by norm_num : 3 <= 804)
    exact le_trans h7 hmono
  have hn7 : (7 : Nat) <= n := le_trans hpow hn
  simp [kappaTwoDefaultBlockIndex]
  omega

/-- Closed κ = 2 Bridge A data using the default paper-scale interior block. -/
noncomputable def cookLevinLocalBlockQBridgeAData_two_defaultInteriorBlock
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) :
    CookLevinLocalBlockQBridgeAData
      M n hn2 htb hns alpha beta alpha0 2 G chi Phi :=
  cookLevinLocalBlockQBridgeAData_two_of_interiorBlockIndices
    M n hn2 htb hns alpha beta alpha0 G chi Phi
    (kappaTwoDefaultBlockIndex (N := N))
    (kappaTwoDefaultBlockIndex_hk1 (N := N))
    (kappaTwoDefaultBlockIndex_hk2 (N := N) (n := n) hn)

/-- Polynomial-bearing real local-block gadget family for the default κ = 2
paper-scale interior block. -/
noncomputable def cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_two_defaultInteriorBlock
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) :
    forall v : Fin N,
      BridgeAPolynomialLocalGadget
        alpha beta alpha0 2 G chi Phi v :=
  cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_two_of_interiorBlockIndices
    M n hn2 htb hns alpha beta alpha0 G chi Phi
    (kappaTwoDefaultBlockIndex (N := N))
    (kappaTwoDefaultBlockIndex_hk1 (N := N))
    (kappaTwoDefaultBlockIndex_hk2 (N := N) (n := n) hn)

/-- Rank-only real local-block gadget family for the default κ = 2 paper-scale
interior block. -/
noncomputable def cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_defaultInteriorBlock
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) :
    forall v : Fin N, LocalGadget N v :=
  cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_of_interiorBlockIndices
    M n hn2 htb hns alpha beta alpha0 G chi Phi
    (kappaTwoDefaultBlockIndex (N := N))
    (kappaTwoDefaultBlockIndex_hk1 (N := N))
    (kappaTwoDefaultBlockIndex_hk2 (N := N) (n := n) hn)

/-- Final κ = 2 Route B target with the default interior block and the
primitive transport certificate as the only SAT-side descent input.

This is the Codex-2 wiring surface: spectral/rank-logdet hypotheses are stated
for the real local-block gadget family, while concrete projection descent can
arrive later as `RouteBFunctorialTransportCertificate`. -/
theorem cookLevinRichProjectionTarget_of_kappaTwoDefaultInteriorBlock_realLocal_transportCertificate
    {M : TuringMachine.DTM} {n : Nat} {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {N d : Nat}
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha0 : 0 < alpha0)
    {theta normBound logDet delta rankLogRate : Real} {rankA : Nat}
    {eigenvalues : Fin N -> Real}
    (htheta : 0 < theta) (hnorm : 0 < normBound)
    (hspec :
      BridgeBSpectralHypotheses theta normBound logDet rankA eigenvalues)
    (hlower :
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 2 G chi Phi
        (cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_defaultInteriorBlock
          M n hn hn2 htb hns alpha beta alpha0 G chi Phi)
        rankLogRate logDet delta)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hcompat :
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi)
    (htransport :
      RouteBFunctorialTransportCertificate M n hn2 htb hns Pi) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns := by
  exact
    cookLevinRichProjectionTarget_of_kappaTwoInteriorBlocks_realLocal_rankLogDet_transport
      (M := M) (n := n) (hn := hn) (hn2 := hn2) (htb := htb) (hns := hns)
      alpha beta alpha0 G chi Phi
      (kappaTwoDefaultBlockIndex (N := N))
      (kappaTwoDefaultBlockIndex_hk1 (N := N))
      (kappaTwoDefaultBlockIndex_hk2 (N := N) (n := n) hn)
      halpha0 htheta hnorm hspec
      (by
        simpa [cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_defaultInteriorBlock]
          using hlower)
      Pi hcompat
      (by
        simpa [cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_defaultInteriorBlock]
          using
            (routeBMatrixToSATGaugeFunctoriality_of_transportCertificate
              M n hn2 htb hns alpha beta alpha0 2 G chi Phi
              (cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_defaultInteriorBlock
                M n hn hn2 htb hns alpha beta alpha0 G chi Phi)
              (bridgeBLogCapacity theta normBound) delta rankA Pi htransport))

/-- Existential per-instance certificate for the default κ = 2 real-local
Route B path.  This is intentionally not the legacy pocket-family certificate:
the rank/logdet lower hypothesis is over the actual real local-block gadget
family, and SAT-side descent is packaged by `RouteBFunctorialTransportCertificate`. -/
def KappaTwoRealLocalRouteBPerInstanceCertificate
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  ∃ (N d : Nat)
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (theta normBound logDet delta rankLogRate : Real) (rankA : Nat)
    (eigenvalues : Fin N -> Real)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)),
      0 < alpha0 ∧
      0 < theta ∧ 0 < normBound ∧
      BridgeBSpectralHypotheses theta normBound logDet rankA eigenvalues ∧
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 2 G chi Phi
        (cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_defaultInteriorBlock
          M n hn hn2 htb hns alpha beta alpha0 G chi Phi)
        rankLogRate logDet delta ∧
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi ∧
      RouteBFunctorialTransportCertificate M n hn2 htb hns Pi

/-- Certificate form of the default κ = 2 real-local Route B target. -/
theorem cookLevinRichProjectionTarget_of_kappaTwoRealLocalRouteBCertificate
    {M : TuringMachine.DTM} {n : Nat} {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (cert : KappaTwoRealLocalRouteBPerInstanceCertificate M n hn hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns := by
  rcases cert with
    ⟨N, d, alpha, beta, alpha0, G, chi, Phi,
      theta, normBound, logDet, delta, rankLogRate, rankA, eigenvalues, Pi,
      halpha0, htheta, hnorm, hspec, hlower, hcompat, htransport⟩
  exact
    cookLevinRichProjectionTarget_of_kappaTwoDefaultInteriorBlock_realLocal_transportCertificate
      (M := M) (n := n) (hn := hn) (hn2 := hn2) (htb := htb) (hns := hns)
      alpha beta alpha0 G chi Phi halpha0 htheta hnorm hspec hlower
      Pi hcompat htransport

/-! ## Section E: concrete multilinear-tail certificate constructors -/

/-- Direct component packer for the default κ = 2 real-local Route B
certificate.  This keeps the certificate surface explicit while avoiding any
legacy pocket-family rank realization assumption. -/
theorem kappaTwoRealLocalRouteBCertificate_of_components
    {M : TuringMachine.DTM} {n : Nat} {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {N d : Nat}
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha0 : 0 < alpha0)
    {theta normBound logDet delta rankLogRate : Real} {rankA : Nat}
    {eigenvalues : Fin N -> Real}
    (htheta : 0 < theta) (hnorm : 0 < normBound)
    (hspec :
      BridgeBSpectralHypotheses theta normBound logDet rankA eigenvalues)
    (hlower :
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 2 G chi Phi
        (cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_defaultInteriorBlock
          M n hn hn2 htb hns alpha beta alpha0 G chi Phi)
        rankLogRate logDet delta)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hcompat :
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi)
    (htransport :
      RouteBFunctorialTransportCertificate M n hn2 htb hns Pi) :
    KappaTwoRealLocalRouteBPerInstanceCertificate M n hn hn2 htb hns :=
  ⟨N, d, alpha, beta, alpha0, G, chi, Phi,
    theta, normBound, logDet, delta, rankLogRate, rankA, eigenvalues, Pi,
    halpha0, htheta, hnorm, hspec, hlower, hcompat, htransport⟩

/-- Concrete multilinear-tail gauge constructor for the default κ = 2
real-local certificate, conditional on the exact SPDP containment/P-window
inputs for that selected projection.

The projection rank field is discharged from the finite row-count budget; the
NP identity-minor field is discharged by the concrete prepended Cook-Levin
witness row. -/
theorem kappaTwoRealLocalRouteBCertificate_of_concreteMultilinearTail_containment
    {M : TuringMachine.DTM} {n : Nat} {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {N d : Nat}
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha0 : 0 < alpha0)
    {theta normBound logDet delta rankLogRate : Real} {rankA : Nat}
    {eigenvalues : Fin N -> Real}
    (htheta : 0 < theta) (hnorm : 0 < normBound)
    (hspec :
      BridgeBSpectralHypotheses theta normBound logDet rankA eigenvalues)
    (hlower :
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 2 G chi Phi
        (cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_defaultInteriorBlock
          M n hn hn2 htb hns alpha beta alpha0 G chi Phi)
        rankLogRate logDet delta)
    (hrowRank :
      routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1 <= rankA)
    (hcontain :
      RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearGauge M n hn2 htb hns))
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns) :
    KappaTwoRealLocalRouteBPerInstanceCertificate M n hn hn2 htb hns := by
  let Pi := routeBRicherConcreteNPPrependedMultilinearGauge M n hn2 htb hns
  have hcompat :
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi := by
    simpa [Pi, routeBRicherConcreteNPPrependedMultilinearGauge] using
      routeBRicherFiniteRowsCandidateGauge_rankCompatible_of_rowCount_le
        M n hn2 htb hns rankA
        (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns)
        hrowRank
  have htransport :
      RouteBFunctorialTransportCertificate M n hn2 htb hns Pi := by
    simpa [Pi, routeBRicherConcreteNPPrependedMultilinearGauge] using
      routeBRicherFiniteRowsCandidateGauge_transportCertificate
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns)
        (by
          simpa [Pi, routeBRicherConcreteNPPrependedMultilinearGauge]
            using hcontain)
        cover
        (routeBRicherConcreteNPWitnessQ M n hn2 htb hns)
        0
        (by
          simpa [routeBRicherConcreteNPPrependedMultilinearRows] using
            routeBRicherConcreteNPPrependedRows_zero_eq_embed
              M n hn2 htb hns
              (routeBRicherMultilinearTailRows M n hn2 htb hns))
        (routeBRicherConcreteNP_extracts_compiled_for_rows
          M n hn2 htb hns
          (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns))
        (routeBRicherConcreteNPWitnessQ_sourceIdentityMinorLowerBound
          M n hn hn2 htb hns)
  exact
    kappaTwoRealLocalRouteBCertificate_of_components
      (M := M) (n := n) (hn := hn) (hn2 := hn2) (htb := htb) (hns := hns)
      alpha beta alpha0 G chi Phi halpha0 htheta hnorm hspec hlower
      Pi hcompat htransport

/-- Projection-descent version of the concrete multilinear-tail κ = 2
real-local certificate.  The only projection-specific missing theorem here is
`RouteBRicherConcreteNPPrependedMultilinearProjectionDescent`; everything else
is wired through checked finite-row transport. -/
theorem kappaTwoRealLocalRouteBCertificate_of_concreteMultilinearTail_projectionDescent
    {M : TuringMachine.DTM} {n : Nat} {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {N d : Nat}
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha0 : 0 < alpha0)
    {theta normBound logDet delta rankLogRate : Real} {rankA : Nat}
    {eigenvalues : Fin N -> Real}
    (htheta : 0 < theta) (hnorm : 0 < normBound)
    (hspec :
      BridgeBSpectralHypotheses theta normBound logDet rankA eigenvalues)
    (hlower :
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 2 G chi Phi
        (cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_defaultInteriorBlock
          M n hn hn2 htb hns alpha beta alpha0 G chi Phi)
        rankLogRate logDet delta)
    (hrowRank :
      routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1 <= rankA)
    (hdesc :
      RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns)
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns) :
    KappaTwoRealLocalRouteBPerInstanceCertificate M n hn hn2 htb hns :=
  kappaTwoRealLocalRouteBCertificate_of_concreteMultilinearTail_containment
    (M := M) (n := n) (hn := hn) (hn2 := hn2) (htb := htb) (hns := hns)
    alpha beta alpha0 G chi Phi halpha0 htheta hnorm hspec hlower hrowRank
    (routeBRicherConcreteNPPrependedMultilinearGauge_spdpSubspaceContainment_of_projectionDescent
      M n hn2 htb hns hdesc)
    cover

/-- No concrete projection escape is the equivalent missing condition for the
projection-descent branch. -/
theorem kappaTwoRealLocalRouteBCertificate_of_concreteMultilinearTail_noProjectionEscape
    {M : TuringMachine.DTM} {n : Nat} {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {N d : Nat}
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha0 : 0 < alpha0)
    {theta normBound logDet delta rankLogRate : Real} {rankA : Nat}
    {eigenvalues : Fin N -> Real}
    (htheta : 0 < theta) (hnorm : 0 < normBound)
    (hspec :
      BridgeBSpectralHypotheses theta normBound logDet rankA eigenvalues)
    (hlower :
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 2 G chi Phi
        (cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_defaultInteriorBlock
          M n hn hn2 htb hns alpha beta alpha0 G chi Phi)
        rankLogRate logDet delta)
    (hrowRank :
      routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1 <= rankA)
    (hnoEscape :
      ¬ RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns)
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns) :
    KappaTwoRealLocalRouteBPerInstanceCertificate M n hn hn2 htb hns :=
  kappaTwoRealLocalRouteBCertificate_of_concreteMultilinearTail_projectionDescent
    (M := M) (n := n) (hn := hn) (hn2 := hn2) (htb := htb) (hns := hns)
    alpha beta alpha0 G chi Phi halpha0 htheta hnorm hspec hlower hrowRank
    (routeBRicherConcreteNPPrependedMultilinearProjectionDescent_of_no_projectionEscapeWitness
      M n hn2 htb hns hnoEscape)
    cover

/-- PSD/eigenvalue-floor constructor for the concrete multilinear-tail κ = 2
real-local certificate.  Bridge B spectral hypotheses and Bridge A log-det
lower hypotheses are both filled by existing real-local-compatible lemmas.

The remaining non-analytic inputs are explicit and minimal: row-count rank
budget, projection descent, and an unprojected P-window finite-span cover. -/
theorem kappaTwoRealLocalRouteBCertificate_of_concreteMultilinearTail_eigenvalueFloor_projectionDescent
    {M : TuringMachine.DTM} {n : Nat} {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {N d : Nat}
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {theta delta rankLogRate lambdaFloor : Real}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (S : Finset (Fin N))
    (htheta : 0 < theta)
    (halpha0 : 0 < alpha0)
    (hrate_nonneg : 0 <= rankLogRate)
    (hdelta_rate : delta <= rankLogRate * (2 : Real))
    (hlambdaFloor_nonneg : 0 <= lambdaFloor)
    (hfloor : ∀ i ∈ S, lambdaFloor <= hA.1.eigenvalues i)
    (hbudget :
      rankLogRate *
          ((∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
            (cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_defaultInteriorBlock
              M n hn hn2 htb hns alpha beta alpha0 G chi Phi v).rank) :
            Real) <=
        (S.card : Real) * Real.log (1 + theta * lambdaFloor))
    (hrowRank :
      routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1 <= A.rank)
    (hdesc :
      RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns)
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns) :
    KappaTwoRealLocalRouteBPerInstanceCertificate M n hn hn2 htb hns :=
  kappaTwoRealLocalRouteBCertificate_of_concreteMultilinearTail_projectionDescent
    (M := M) (n := n) (hn := hn) (hn2 := hn2) (htb := htb) (hns := hns)
    (theta := theta)
    (normBound := routeBEigenvalueSumNormBound A hA)
    (logDet := Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det))
    (delta := delta) (rankLogRate := rankLogRate)
    (rankA := A.rank) (eigenvalues := hA.1.eigenvalues)
    alpha beta alpha0 G chi Phi halpha0 htheta
    (routeBEigenvalueSumNormBound_pos A hA)
    (bridgeB_spectral_hypotheses_of_posSemidef_autoNorm A hA htheta)
    (bridgeA_rankLogDetLowerHypotheses_of_shifted_logdet_eigenvalue_floor_on_finset
      alpha beta alpha0 2 G chi Phi
      (cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_defaultInteriorBlock
        M n hn hn2 htb hns alpha beta alpha0 G chi Phi)
      A hA S htheta hrate_nonneg hdelta_rate
      hlambdaFloor_nonneg hfloor hbudget)
    hrowRank hdesc cover

/-! ## Axiom audit anchors -/

#print axioms kappaTwoInteriorBlockOfVertex
#print axioms cookLevinLocalBlockQEnergyToRankTarget_two_of_interiorBlockIndices
#print axioms cookLevinLocalBlockQBridgeAData_two_of_interiorBlockIndices
#print axioms cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_two_of_interiorBlockIndices
#print axioms cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_of_interiorBlockIndices
#print axioms cookLevinLocalBlockQ_routeB_hGadgetRank_two_of_interiorBlockIndices
#print axioms cookLevinLocalBlockQ_routeB_activeSet_rank_budget_two_of_interiorBlockIndices
#print axioms cookLevinRichProjectionTarget_of_kappaTwoInteriorBlocks_realLocal_rankLogDet_transport
#print axioms kappaTwoDefaultBlockIndex
#print axioms kappaTwoDefaultBlockIndex_hk1
#print axioms kappaTwoDefaultBlockIndex_hk2
#print axioms cookLevinLocalBlockQBridgeAData_two_defaultInteriorBlock
#print axioms cookLevinLocalBlockQ_routeBPolynomialLocalGadgetFamily_two_defaultInteriorBlock
#print axioms cookLevinLocalBlockQ_routeBLocalGadgetFamily_two_defaultInteriorBlock
#print axioms cookLevinRichProjectionTarget_of_kappaTwoDefaultInteriorBlock_realLocal_transportCertificate
#print axioms KappaTwoRealLocalRouteBPerInstanceCertificate
#print axioms cookLevinRichProjectionTarget_of_kappaTwoRealLocalRouteBCertificate
#print axioms kappaTwoRealLocalRouteBCertificate_of_components
#print axioms kappaTwoRealLocalRouteBCertificate_of_concreteMultilinearTail_containment
#print axioms kappaTwoRealLocalRouteBCertificate_of_concreteMultilinearTail_projectionDescent
#print axioms kappaTwoRealLocalRouteBCertificate_of_concreteMultilinearTail_noProjectionEscape
#print axioms kappaTwoRealLocalRouteBCertificate_of_concreteMultilinearTail_eigenvalueFloor_projectionDescent

end PallLean.Paper93.Paper283
