import PallLean.Paper93.DeepMath.PathB.StrictFaithfulTrajectoryObserver

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

structure StrictDynamicNFrameLagrangianObserver
    (enc : ThreeCNFEncoding) where
  M : TuringMachine.DTM
  configActionRank : Nat -> Nat
  decides : DTMDecidesSATWithEncoding enc M

noncomputable def StrictDynamicNFrameLagrangianObserver.toTrajectory
    {enc : ThreeCNFEncoding}
    (L : StrictDynamicNFrameLagrangianObserver enc) :
    TrajectoryObserverMachine :=
  strictFaithfulTrajectoryObserver L.M L.configActionRank

theorem StrictDynamicNFrameLagrangianObserver.toTrajectory_faithful
    {enc : ThreeCNFEncoding}
    (L : StrictDynamicNFrameLagrangianObserver enc) :
    StrictFaithfulSATObserverClass enc L.toTrajectory := by
  exact ⟨L.M, L.configActionRank, L.decides, rfl⟩

structure StrictDynamicNFrameLagrangianLiveMinor
    (enc : ThreeCNFEncoding)
    (L : StrictDynamicNFrameLagrangianObserver enc)
    (n : Nat) where
  input : Fin n -> Bool
  formula : ThreeCNF
  encoded : enc.Encodes input formula
  formula_satisfiable : formula.IsSatisfiable
  time : Nat
  state : Nat
  state_matches : state = L.toTrajectory.stateCode n input time
  liveActionRank : Nat
  nframe_lagrangian_payload : Prop
  nframe_lagrangian_payload_realized : nframe_lagrangian_payload
  pac_holographic_payload : Prop
  pac_holographic_payload_realized : pac_holographic_payload
  amplituhedron_payload : Prop
  amplituhedron_payload_realized : amplituhedron_payload
  liveActionRank_eq_boundary :
    liveActionRank = L.toTrajectory.liveBoundaryRank n input time
  rank_lower : Nat.choose (n / 3) (Nat.log 2 n) <= liveActionRank

noncomputable def StrictDynamicNFrameLagrangianLiveMinor.toTrajectoryMinor
    {enc : ThreeCNFEncoding}
    {L : StrictDynamicNFrameLagrangianObserver enc}
    {n : Nat}
    (minor : StrictDynamicNFrameLagrangianLiveMinor enc L n) :
    TrajectoryGodMoveBoundaryMinor enc L.toTrajectory n where
  input := minor.input
  formula := minor.formula
  encoded := minor.encoded
  formula_satisfiable := minor.formula_satisfiable
  time := minor.time
  state := minor.state
  state_matches := minor.state_matches
  liveRank := minor.liveActionRank
  phase_holographic_payload := minor.pac_holographic_payload
  phase_payload_realized := minor.pac_holographic_payload_realized
  godmove_amplituhedron_payload :=
    minor.nframe_lagrangian_payload ∧ minor.amplituhedron_payload
  godmove_payload_realized :=
    ⟨minor.nframe_lagrangian_payload_realized,
      minor.amplituhedron_payload_realized⟩
  rank_lower := minor.rank_lower
  rank_le_boundary := by rw [minor.liveActionRank_eq_boundary]

def StrictDynamicNFrameLagrangianExtractionAt
    (enc : ThreeCNFEncoding) (n : Nat) : Prop :=
  forall L : StrictDynamicNFrameLagrangianObserver enc,
    Nonempty (StrictDynamicNFrameLagrangianLiveMinor enc L n)

def UniversalStrictDynamicNFrameLagrangianExtraction
    (enc : ThreeCNFEncoding) : Prop :=
  forall c : Nat, exists n : Nat,
    n >= 2 ^ 20 /\
    4 * (c + 1) <= Nat.log 2 n /\
    StrictDynamicNFrameLagrangianExtractionAt enc n

theorem strictFaithfulExtraction_of_universalStrictDynamicNFrameLagrangianExtraction
    (enc : ThreeCNFEncoding)
    (hextract : UniversalStrictDynamicNFrameLagrangianExtraction enc) :
    UniversalTrajectorySATGodMoveExtraction enc (StrictFaithfulSATObserverClass enc) := by
  intro c
  rcases hextract c with ⟨n, hn20, hlog, hextract_at⟩
  refine ⟨n, hn20, hlog, ?_⟩
  intro T hT
  rcases hT with ⟨M, configActionRank, hdec, rfl⟩
  let L : StrictDynamicNFrameLagrangianObserver enc :=
    { M := M, configActionRank := configActionRank, decides := hdec }
  rcases hextract_at L with ⟨minor⟩
  exact ⟨by
    simpa [StrictDynamicNFrameLagrangianObserver.toTrajectory, L] using
      minor.toTrajectoryMinor⟩

end PallLean.Paper93.DeepMath.PathB
