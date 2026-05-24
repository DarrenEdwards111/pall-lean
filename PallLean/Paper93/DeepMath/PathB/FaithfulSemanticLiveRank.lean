import PallLean.Paper93.DeepMath.PathB.FaithfulLiveMinorObstruction

/-!
# Semantic live-rank correction

`FaithfulOperationalTrajectoryObserverDecidesSAT` is too broad: it lets a DTM
be paired with an arbitrary `stateContextRank`, including the constant-zero
function.  The live-minor discharge therefore cannot target that class.

This file installs the corrected socket.  A SAT trajectory is now presented
together with a semantic predicate saying that its state-context rank is the
real PAC/N-frame live boundary accounting.  The hard theorem becomes a uniform
semantic live-minor discharge: at the extraction scale, every semantically
valid rank accounting carries a certified live boundary object.  Such a
certificate converts mechanically into the existing
`TrajectoryGodMoveBoundaryMinor`.

The point is sharp: any successful semantic discharge automatically excludes
the zero-rank presentation.  So the zero-rank escape is removed by the semantic
validity predicate, not by hiding the obstruction.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- A semantic validity predicate for faithful live-rank accounting.

The intended instantiation is: `LiveRankSemantics M rank` means `rank` is the
actual PAC / holography / amplituhedron / N-frame live boundary rank associated
to the DTM trajectory of `M`, not an arbitrary accounting function. -/
abbrev FaithfulLiveRankSemanticsPredicate : Type :=
  TuringMachine.DTM -> (Nat -> Nat) -> Prop

/-- The semantically corrected faithful SAT observer class.

Compared with `FaithfulSATObserverClass`, this class keeps the DTM-backed
faithful presentation but also requires the chosen `stateContextRank` to satisfy
the supplied PAC/N-frame live-rank semantics. -/
def FaithfulSemanticSATObserverClass
    (enc : ThreeCNFEncoding)
    (LiveRankSemantics : FaithfulLiveRankSemanticsPredicate)
    (T : TrajectoryObserverMachine) : Prop :=
  exists M : TuringMachine.DTM, exists stateContextRank : Nat -> Nat,
    DTMDecidesSATWithEncoding enc M /\
      LiveRankSemantics M stateContextRank /\
        T = faithfulTrajectoryObserver M stateContextRank

/-- Semantic faithful observers are ordinary faithful observers after forgetting
the semantic live-rank validity proof. -/
theorem FaithfulSATObserverClass_of_semantic
    {enc : ThreeCNFEncoding}
    {LiveRankSemantics : FaithfulLiveRankSemanticsPredicate}
    {T : TrajectoryObserverMachine}
    (hT : FaithfulSemanticSATObserverClass enc LiveRankSemantics T) :
    FaithfulSATObserverClass enc T := by
  rcases hT with ⟨M, stateContextRank, hdec, _hsem, hT_eq⟩
  exact ⟨M, stateContextRank, hdec, hT_eq⟩

/-- A certified semantic live boundary at one length.

This is the concrete object that PAC / holography / amplituhedron / N-frame
semantics must produce.  Its fields are intentionally aligned with
`TrajectoryGodMoveBoundaryMinor`, but the rank upper bound is stated against
the faithful DTM state-context rank, so fake rank functions are exposed
immediately. -/
structure FaithfulSemanticLiveBoundaryAt
    (enc : ThreeCNFEncoding)
    (M : TuringMachine.DTM)
    (stateContextRank : Nat -> Nat)
    (n : Nat) : Type where
  input : Fin n -> Bool
  formula : ThreeCNF
  encoded : enc.Encodes input formula
  formula_satisfiable : formula.IsSatisfiable
  time : Nat
  state : Nat
  state_matches :
    state =
      (faithfulTrajectoryObserver M stateContextRank).stateCode n input time
  liveRank : Nat
  phase_holographic_payload : Prop
  phase_payload_realized : phase_holographic_payload
  godmove_amplituhedron_payload : Prop
  godmove_payload_realized : godmove_amplituhedron_payload
  nframe_boundary_payload : Prop
  nframe_payload_realized : nframe_boundary_payload
  pac_boundary_payload : Prop
  pac_payload_realized : pac_boundary_payload
  rank_lower :
    Nat.choose (n / 3) (Nat.log 2 n) <= liveRank
  rank_le_stateContext :
    liveRank <= FaithfulStateRankAt M stateContextRank n input time

/-- A semantic live-boundary certificate is exactly enough to build the existing
trajectory God-Move boundary minor. -/
def FaithfulSemanticLiveBoundaryAt.toTrajectoryMinor
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM}
    {stateContextRank : Nat -> Nat}
    {n : Nat}
    (cert : FaithfulSemanticLiveBoundaryAt enc M stateContextRank n) :
    TrajectoryGodMoveBoundaryMinor enc
      (faithfulTrajectoryObserver M stateContextRank) n where
  input := cert.input
  formula := cert.formula
  encoded := cert.encoded
  formula_satisfiable := cert.formula_satisfiable
  time := cert.time
  state := cert.state
  state_matches := cert.state_matches
  liveRank := cert.liveRank
  phase_holographic_payload := cert.phase_holographic_payload
  phase_payload_realized := cert.phase_payload_realized
  godmove_amplituhedron_payload := cert.godmove_amplituhedron_payload
  godmove_payload_realized := cert.godmove_payload_realized
  rank_lower := cert.rank_lower
  rank_le_boundary := by
    change cert.liveRank <=
      FaithfulStateRankAt M stateContextRank n cert.input cert.time
    exact cert.rank_le_stateContext

/-- Nonempty semantic live-boundary certificates yield nonempty trajectory
minors. -/
theorem trajectoryMinor_of_semanticLiveBoundaryAt
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM}
    {stateContextRank : Nat -> Nat}
    {n : Nat}
    (hcert : Nonempty
      (FaithfulSemanticLiveBoundaryAt enc M stateContextRank n)) :
    Nonempty (TrajectoryGodMoveBoundaryMinor enc
      (faithfulTrajectoryObserver M stateContextRank) n) := by
  rcases hcert with ⟨cert⟩
  exact ⟨cert.toTrajectoryMinor⟩

/-- A positive-scale semantic live-boundary certificate cannot be carried by
the zero-rank presentation. -/
theorem no_semanticLiveBoundaryAt_of_zeroRankFaithfulObserver
    {enc : ThreeCNFEncoding}
    (M : TuringMachine.DTM)
    {n : Nat}
    (hchoose_pos : 0 < Nat.choose (n / 3) (Nat.log 2 n)) :
    Not (Nonempty
      (FaithfulSemanticLiveBoundaryAt enc M zeroStateContextRank n)) := by
  intro hcert
  exact
    (no_trajectoryMinor_of_zeroRankFaithfulObserver
      (enc := enc) M hchoose_pos)
      (trajectoryMinor_of_semanticLiveBoundaryAt hcert)

/-- Uniform semantic live-minor discharge.

This is the corrected hard theorem.  It no longer quantifies over arbitrary
rank accounting functions; it quantifies only over state-context ranks that
satisfy the supplied live-rank semantics predicate. -/
def UniformFaithfulSemanticLiveMinorDischarge
    (enc : ThreeCNFEncoding)
    (LiveRankSemantics : FaithfulLiveRankSemanticsPredicate) : Prop :=
  forall c : Nat, exists n : Nat,
    n >= 2 ^ 20 /\
      4 * (c + 1) <= Nat.log 2 n /\
        forall (M : TuringMachine.DTM) (stateContextRank : Nat -> Nat),
          DTMDecidesSATWithEncoding enc M ->
            LiveRankSemantics M stateContextRank ->
              Nonempty
                (FaithfulSemanticLiveBoundaryAt enc M stateContextRank n)

/-- The corrected semantic discharge implies universal extraction for the
semantically corrected faithful SAT observer class. -/
theorem universalSemanticFaithfulExtraction_of_uniformSemanticLiveMinorDischarge
    (enc : ThreeCNFEncoding)
    (LiveRankSemantics : FaithfulLiveRankSemanticsPredicate)
    (hdischarge :
      UniformFaithfulSemanticLiveMinorDischarge enc LiveRankSemantics) :
    UniversalTrajectorySATGodMoveExtraction enc
      (FaithfulSemanticSATObserverClass enc LiveRankSemantics) := by
  intro c
  rcases hdischarge c with ⟨n, hn20, hlog, hcert_at⟩
  refine ⟨n, hn20, hlog, ?_⟩
  intro T hT
  rcases hT with ⟨M, stateContextRank, hdec, hsem, rfl⟩
  exact trajectoryMinor_of_semanticLiveBoundaryAt
    (hcert_at M stateContextRank hdec hsem)

/-- The corrected semantic discharge gives the dynamic lower bound for the
semantic faithful observer class. -/
theorem semanticFaithful_dynamicSATLowerBound_of_uniformSemanticLiveMinorDischarge
    (enc : ThreeCNFEncoding)
    (LiveRankSemantics : FaithfulLiveRankSemanticsPredicate)
    (hdischarge :
      UniformFaithfulSemanticLiveMinorDischarge enc LiveRankSemantics) :
    DynamicCEW.NP_side_lower_bound
      (TrajectoryObserverWidths
        (FaithfulSemanticSATObserverClass enc LiveRankSemantics)) :=
  NP_side_lower_bound_of_universalTrajectorySATGodMoveExtraction
    enc (FaithfulSemanticSATObserverClass enc LiveRankSemantics)
    (universalSemanticFaithfulExtraction_of_uniformSemanticLiveMinorDischarge
      enc LiveRankSemantics hdischarge)

/-- Successful semantic discharge forces the live-rank semantics predicate to
exclude zero-rank presentations of SAT deciders. -/
theorem uniformSemanticLiveMinorDischarge_excludes_zeroRankPresentations
    (enc : ThreeCNFEncoding)
    (LiveRankSemantics : FaithfulLiveRankSemanticsPredicate)
    (hdischarge :
      UniformFaithfulSemanticLiveMinorDischarge enc LiveRankSemantics) :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        Not (LiveRankSemantics M zeroStateContextRank) := by
  intro M hdec hzero_sem
  rcases hdischarge 0 with ⟨n, hn20, hlog, hcert_at⟩
  have hgap :
      n ^ 0 < Nat.choose (n / 3) (Nat.log 2 n) :=
    arithmetic_gap_for_exponent 0 n hn20 hlog
  have hchoose_pos :
      0 < Nat.choose (n / 3) (Nat.log 2 n) := by
    have hn_pow_pos : 0 < n ^ 0 := by simp
    exact lt_trans hn_pow_pos hgap
  exact
    (no_semanticLiveBoundaryAt_of_zeroRankFaithfulObserver
      (enc := enc) M hchoose_pos)
      (hcert_at M zeroStateContextRank hdec hzero_sem)

/-- Presentation hypothesis for moving from operational SAT observers to the
semantically corrected faithful class. -/
def PaperMainSemanticFaithfulObserverPresentation
    (enc : ThreeCNFEncoding)
    (LiveRankSemantics : FaithfulLiveRankSemanticsPredicate) : Prop :=
  forall T : TrajectoryObserverMachine,
    OperationalTrajectoryObserverDecidesSAT enc T ->
      FaithfulSemanticSATObserverClass enc LiveRankSemantics T

/-- A semantic faithful lower bound plus semantic presentation gives the
paper-main dynamic SAT lower bound. -/
theorem paperMain_dynamicSATLowerBound_of_semanticFaithfulLowerBound_and_presentation
    (enc : ThreeCNFEncoding)
    (LiveRankSemantics : FaithfulLiveRankSemanticsPredicate)
    (hlower :
      DynamicCEW.NP_side_lower_bound
        (TrajectoryObserverWidths
          (FaithfulSemanticSATObserverClass enc LiveRankSemantics)))
    (hpresent :
      PaperMainSemanticFaithfulObserverPresentation enc LiveRankSemantics) :
    PaperMainDynamicSATLowerBound enc := by
  intro c
  rcases hlower c with ⟨n, hnot_semantic⟩
  refine ⟨n, ?_⟩
  intro hcew
  rcases hcew with ⟨w, hw_decides, hw_bound⟩
  rcases hw_decides with ⟨T, hdec, hwidth_eq⟩
  exact hnot_semantic
    ⟨w, ⟨T, hpresent T hdec, hwidth_eq⟩, hw_bound⟩

/-- Corrected final paper-main closure package.

The old closure package asked for live-minor extraction on all faithful
presentations, including fake zero-rank presentations.  This package asks for
semantic presentation and semantic live-minor discharge instead. -/
structure FaithfulSemanticPaperMainClosureWiring
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (LiveRankSemantics : FaithfulLiveRankSemanticsPredicate) : Prop where
  p_side_calibration : PaperMainPObserverCalibration PDecider
  semantic_presentation :
    PaperMainSemanticFaithfulObserverPresentation enc LiveRankSemantics
  semantic_live_minor_discharge :
    UniformFaithfulSemanticLiveMinorDischarge enc LiveRankSemantics

/-- The corrected closure package gives the paper-main dynamic SAT lower bound. -/
theorem paperMain_dynamicSATLowerBound_of_semanticClosureWiring
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (LiveRankSemantics : FaithfulLiveRankSemanticsPredicate)
    (wiring :
      FaithfulSemanticPaperMainClosureWiring enc PDecider LiveRankSemantics) :
    PaperMainDynamicSATLowerBound enc :=
  paperMain_dynamicSATLowerBound_of_semanticFaithfulLowerBound_and_presentation
    enc LiveRankSemantics
    (semanticFaithful_dynamicSATLowerBound_of_uniformSemanticLiveMinorDischarge
      enc LiveRankSemantics wiring.semantic_live_minor_discharge)
    wiring.semantic_presentation

/-- Final paper-main observer separation criterion from the corrected semantic
closure package. -/
theorem paperMain_observerSeparationCriterion_of_semanticClosureWiring
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (LiveRankSemantics : FaithfulLiveRankSemanticsPredicate)
    (wiring :
      FaithfulSemanticPaperMainClosureWiring enc PDecider LiveRankSemantics) :
    PaperMainObserverSeparationCriterion enc PDecider :=
  ⟨wiring.p_side_calibration,
    paperMain_dynamicSATLowerBound_of_semanticClosureWiring
      enc PDecider LiveRankSemantics wiring⟩

#print axioms universalSemanticFaithfulExtraction_of_uniformSemanticLiveMinorDischarge
#print axioms semanticFaithful_dynamicSATLowerBound_of_uniformSemanticLiveMinorDischarge
#print axioms uniformSemanticLiveMinorDischarge_excludes_zeroRankPresentations
#print axioms paperMain_observerSeparationCriterion_of_semanticClosureWiring

end PallLean.Paper93.DeepMath.PathB
