import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCanonicalStrictGodMoveRoute
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTheorem207SameSheetLegacyPort

/-!
# Paper God-Move transport bridge

This module names the clean active seam from the paper God-Move / `TΦ`
transport proof into the current canonical strict port.  It deliberately avoids
importing the archived Step4/unsafe wrappers.

The mathematical obligation is the per-observer transport witness below: the
paper God-Move lower bound on the extracted sheet, plus the same-target
transport/no-loss inequality into the strict live-boundary rank.  Once such
witnesses are supplied uniformly, the existing canonical strict route closes
mechanically.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Per-observer paper God-Move transport witness.

This is the constructive content expected from the paper proof: a satisfiable
encoded hard instance, the realised N-frame/PAC/amplituhedron payloads, a
God-Move extracted sheet rank with the binomial NP lower bound, and the `TΦ`
transport/no-loss inequality into the exact strict live-boundary endpoint.
-/
structure PaperGodMoveTransportWitness
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (L : StrictDynamicNFrameLagrangianObserver enc) where
  input : Fin n -> Bool
  formula : ThreeCNF
  encoded : enc.Encodes input formula
  formula_satisfiable : formula.IsSatisfiable
  time : Nat
  state : Nat
  state_matches : state = L.toTrajectory.stateCode n input time
  nframe_lagrangian_payload : Prop
  nframe_lagrangian_payload_realized : nframe_lagrangian_payload
  pac_holographic_payload : Prop
  pac_holographic_payload_realized : pac_holographic_payload
  amplituhedron_payload : Prop
  amplituhedron_payload_realized : amplituhedron_payload
  godMoveExtractedSheetRank : Nat
  godMove_np_lower :
    Nat.choose (n / 3) (Nat.log 2 n) <= godMoveExtractedSheetRank
  tPhi_transport_to_liveBoundary :
    godMoveExtractedSheetRank <= L.toTrajectory.liveBoundaryRank n input time

/-- The paper God-Move transport witness is exactly enough to inhabit the
current direct-paper Theorem-207 witness socket. -/
noncomputable def theorem207DirectPaperWitness_of_paperGodMoveTransport
    {enc : ThreeCNFEncoding}
    {n : Nat}
    {L : StrictDynamicNFrameLagrangianObserver enc}
    (W : PaperGodMoveTransportWitness enc n L) :
    Theorem207DirectPaperWitness enc n L where
  input := W.input
  formula := W.formula
  encoded := W.encoded
  formula_satisfiable := W.formula_satisfiable
  time := W.time
  state := W.state
  state_matches := W.state_matches
  nframe_lagrangian_payload := W.nframe_lagrangian_payload
  nframe_lagrangian_payload_realized := W.nframe_lagrangian_payload_realized
  pac_holographic_payload := W.pac_holographic_payload
  pac_holographic_payload_realized := W.pac_holographic_payload_realized
  amplituhedron_payload := W.amplituhedron_payload
  amplituhedron_payload_realized := W.amplituhedron_payload_realized
  extractedSheetRank := W.godMoveExtractedSheetRank
  sheet_rank_lower := W.godMove_np_lower
  sheet_rank_le_liveBoundary := W.tPhi_transport_to_liveBoundary

/-- Legacy same-sheet strict realization is one concrete way to produce the
clean paper God-Move transport witness.  This is the direct bridge from the
older named same-sheet SPDP target into the new `TΦ`/live-boundary witness
socket. -/
noncomputable def paperGodMoveTransportWitness_of_sameSheetStrictRealization
    {enc : ThreeCNFEncoding}
    {n : Nat}
    {L : StrictDynamicNFrameLagrangianObserver enc}
    (R : Theorem207SameSheetStrictRealization enc n L) :
    PaperGodMoveTransportWitness enc n L where
  input := R.input
  formula := R.formula
  encoded := R.encoded
  formula_satisfiable := R.formula_satisfiable
  time := R.time
  state := R.state
  state_matches := R.state_matches
  nframe_lagrangian_payload := R.nframe_lagrangian_payload
  nframe_lagrangian_payload_realized := R.nframe_lagrangian_payload_realized
  pac_holographic_payload := R.pac_holographic_payload
  pac_holographic_payload_realized := R.pac_holographic_payload_realized
  amplituhedron_payload := R.amplituhedron_payload
  amplituhedron_payload_realized := R.amplituhedron_payload_realized
  godMoveExtractedSheetRank :=
    MultilinearSPDP.mlBlockedSpdpRank
      (cook_levin_compilation L.M n R.hn2 R.htb R.hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (GlobalGodMoveGauge.theorem207_same_sheet_poly
        L.M n R.hn804 R.hn2 R.htb R.hns R.hdec)
  godMove_np_lower :=
    GlobalGodMoveGauge.theorem207_same_sheet_np_side_lower_bound
      L.M n R.hn804 R.hn2 R.htb R.hns R.hdec
  tPhi_transport_to_liveBoundary := R.same_sheet_rank_le_liveBoundary

/-- Uniform paper God-Move transport port for the canonical low-action class.
This is the clean theorem that the paper proof should discharge. -/
def PaperGodMoveTransportPort
    (enc : ThreeCNFEncoding) : Prop :=
  forall c : Nat, exists n : Nat,
    n >= 2 ^ 20 /\
    4 * (c + 1) <= Nat.log 2 n /\
    forall L : CanonicalStrictGodMoveSATObserver enc,
      L.k <= c ->
      Nonempty (PaperGodMoveTransportWitness enc n L.base)

/-- The older same-sheet strict realization contract implies the new clean
paper God-Move transport port for the canonical low-action class.  This is not
the unsafe Step4 route; it only repackages same-sheet realization witnesses into
the new transport witness socket. -/
theorem paperGodMoveTransportPort_of_sameSheetStrictRealization
    (enc : ThreeCNFEncoding)
    (H : UniversalTheorem207SameSheetStrictRealization enc) :
    PaperGodMoveTransportPort enc := by
  intro c
  rcases H c with ⟨n, hn20, hlog, Hn⟩
  refine ⟨n, hn20, hlog, ?_⟩
  intro L _hLk
  rcases Hn L.base with ⟨R⟩
  exact ⟨paperGodMoveTransportWitness_of_sameSheetStrictRealization R⟩

/-- The clean bridge: paper God-Move transport witnesses feed the existing
canonical strict port without using the no-decider/vacuity direction. -/
theorem canonicalStrictGodMovePort_of_paperGodMoveTransportPort
    (enc : ThreeCNFEncoding)
    (H : PaperGodMoveTransportPort enc) :
    CanonicalStrictGodMovePort enc := by
  intro c
  rcases H c with ⟨n, hn20, hlog, Hn⟩
  refine ⟨n, hn20, hlog, ?_⟩
  intro L hLk
  rcases Hn L hLk with ⟨W⟩
  exact ⟨theorem207DirectPaperWitness_of_paperGodMoveTransport W⟩

/-- End-to-end canonical strict no-decider readout from the paper God-Move
transport port. -/
theorem no_DTMDecidesSATWithEncoding_of_paperGodMoveTransportPort
    (enc : ThreeCNFEncoding)
    (H : PaperGodMoveTransportPort enc) :
    Not (exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M) :=
  no_DTMDecidesSATWithEncoding_of_canonicalStrictGodMovePort enc
    (canonicalStrictGodMovePort_of_paperGodMoveTransportPort enc H)

/-- Standard-bridge readout from the paper God-Move transport port. -/
theorem standardPvsNP_of_paperGodMoveTransportPort
    {enc : ThreeCNFEncoding}
    (B : CanonicalStrictStandardBridge enc)
    (H : PaperGodMoveTransportPort enc) :
    B.standardPvsNP :=
  standardPvsNP_of_canonicalStrictGodMovePort B
    (canonicalStrictGodMovePort_of_paperGodMoveTransportPort enc H)

#print axioms theorem207DirectPaperWitness_of_paperGodMoveTransport
#print axioms paperGodMoveTransportWitness_of_sameSheetStrictRealization
#print axioms paperGodMoveTransportPort_of_sameSheetStrictRealization
#print axioms canonicalStrictGodMovePort_of_paperGodMoveTransportPort
#print axioms no_DTMDecidesSATWithEncoding_of_paperGodMoveTransportPort
#print axioms standardPvsNP_of_paperGodMoveTransportPort

end PallLean.Paper93.DeepMath.PathB
