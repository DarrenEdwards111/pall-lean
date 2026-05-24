import PallLean.Paper93.DeepMath.PathB.FaithfulTrajectoryObserver

/-!
# Dynamic N-frame/Lagrangian invariant frontier

This file records the viable positive pivot identified from `paper/main.tex`:
the N-frame/Lagrangian object must be used as a **dynamic trajectory invariant**,
not as the old static SPDP-rank proxy of one compiled polynomial.

The invariant below is tied to an actual DTM-backed observer trajectory.  Its
live action rank is read from the current run state through a state-context
rank accounting function, and its width is the finite trajectory supremum
already defined in `FaithfulTrajectoryObserver`.

No P-vs-NP lower bound is asserted here.  The new mathematical target is the
universal dynamic N-frame/Lagrangian extraction theorem:

  every polynomial-time SAT observer has a live time/state at which the
  N-frame/Lagrangian boundary carries the binomial-size minor.

Once that theorem is supplied, the existing dynamic-CEW bridge mechanically
produces the SAT observer-width lower bound.  This is the positive version of
the pivot, with the hard content isolated at the trajectory level.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-! ## Dynamic Lagrangian observers -/

/-- A DTM-backed SAT observer with a dynamic N-frame/Lagrangian state-rank
accounting function.

The field `stateActionRank` is the proposed live Lagrangian invariant: it is
evaluated on the actual DTM run state, not on a preselected static polynomial.
The induced observer is the faithful trajectory observer whose width is the
maximum of this live quantity over all inputs and times at length `n`. -/
structure DynamicNFrameLagrangianObserver
    (enc : ThreeCNFEncoding) where
  M : TuringMachine.DTM
  stateActionRank : Nat -> Nat
  decides : DTMDecidesSATWithEncoding enc M

/-- Forget the dynamic Lagrangian observer to its faithful trajectory observer. -/
noncomputable def DynamicNFrameLagrangianObserver.toTrajectory
    {enc : ThreeCNFEncoding}
    (L : DynamicNFrameLagrangianObserver enc) :
    TrajectoryObserverMachine :=
  faithfulTrajectoryObserver L.M L.stateActionRank

/-- Dynamic Lagrangian observers are faithful operational SAT observers. -/
theorem DynamicNFrameLagrangianObserver.toTrajectory_faithful
    {enc : ThreeCNFEncoding}
    (L : DynamicNFrameLagrangianObserver enc) :
    FaithfulSATObserverClass enc L.toTrajectory := by
  exact ⟨L.M, L.stateActionRank, L.decides, rfl⟩

/-! ## Live N-frame/Lagrangian minor -/

/-- A live N-frame/Lagrangian minor extracted from one trajectory state.

This is the strengthened positive target.  The minor is located at a concrete
input, formula, time, and state of a DTM-backed observer.  The payload fields
are where PAC/holography/amplituhedron/positroid analysis must land; the rank
fields are the only data needed by the dynamic-CEW lower-bound bridge.

The equality `liveActionRank_eq_boundary` makes explicit that this is the
observer's live dynamic Lagrangian invariant, not a separate static SPDP proxy. -/
structure DynamicNFrameLagrangianLiveMinor
    (enc : ThreeCNFEncoding)
    (L : DynamicNFrameLagrangianObserver enc)
    (n : Nat) where
  input : Fin n -> Bool
  formula : ThreeCNF
  encoded : enc.Encodes input formula
  formula_satisfiable : formula.IsSatisfiable
  time : Nat
  state : Nat
  state_matches :
    state = L.toTrajectory.stateCode n input time
  liveActionRank : Nat
  nframe_lagrangian_payload : Prop
  nframe_lagrangian_payload_realized : nframe_lagrangian_payload
  pac_holographic_payload : Prop
  pac_holographic_payload_realized : pac_holographic_payload
  amplituhedron_payload : Prop
  amplituhedron_payload_realized : amplituhedron_payload
  liveActionRank_eq_boundary :
    liveActionRank = L.toTrajectory.liveBoundaryRank n input time
  rank_lower :
    Nat.choose (n / 3) (Nat.log 2 n) <= liveActionRank

/-- A dynamic N-frame/Lagrangian live minor is a trajectory God-Move boundary
minor for the induced faithful trajectory observer. -/
noncomputable def DynamicNFrameLagrangianLiveMinor.toTrajectoryMinor
    {enc : ThreeCNFEncoding}
    {L : DynamicNFrameLagrangianObserver enc}
    {n : Nat}
    (minor : DynamicNFrameLagrangianLiveMinor enc L n) :
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
  rank_le_boundary := by
    rw [minor.liveActionRank_eq_boundary]

/-! ## The non-circular lower-bound target -/

/-- Fixed-length dynamic N-frame/Lagrangian extraction theorem.

This is not a statement about one static compiled polynomial.  It quantifies
over DTM-backed SAT observers and extracts a live minor from their trajectories. -/
def DynamicNFrameLagrangianExtractionAt
    (enc : ThreeCNFEncoding) (n : Nat) : Prop :=
  forall L : DynamicNFrameLagrangianObserver enc,
    Nonempty (DynamicNFrameLagrangianLiveMinor enc L n)

/-- Exponent-parametric dynamic N-frame/Lagrangian SAT lower-bound theorem.

This is the precise theorem that PAC/holography/amplituhedron/Ramanujan
geometry must prove to make the observer route positive. -/
def UniversalDynamicNFrameLagrangianExtraction
    (enc : ThreeCNFEncoding) : Prop :=
  forall c : Nat, exists n : Nat,
    n >= 2 ^ 20 /\
    4 * (c + 1) <= Nat.log 2 n /\
    DynamicNFrameLagrangianExtractionAt enc n

/-- The dynamic N-frame/Lagrangian extraction theorem discharges the faithful
trajectory God-Move extraction target.

This is the main wiring theorem of the pivot: once the Lagrangian invariant
really produces live trajectory minors for every SAT observer, the older
trajectory/DCEW bridge can consume them without returning to static SPDP rank. -/
theorem faithfulExtraction_of_dynamicNFrameLagrangianExtraction
    (enc : ThreeCNFEncoding)
    (hextract : UniversalDynamicNFrameLagrangianExtraction enc) :
    UniversalFaithfulSATObserverGodMoveExtraction enc := by
  intro c
  rcases hextract c with ⟨n, hn20, hlog, hextract_at⟩
  refine ⟨n, hn20, hlog, ?_⟩
  intro T hT
  rcases hT with ⟨M, stateActionRank, hdec, rfl⟩
  let L : DynamicNFrameLagrangianObserver enc :=
    { M := M, stateActionRank := stateActionRank, decides := hdec }
  rcases hextract_at L with ⟨minor⟩
  exact ⟨by
    simpa [DynamicNFrameLagrangianObserver.toTrajectory, L] using
      minor.toTrajectoryMinor⟩

/-- Therefore the dynamic N-frame/Lagrangian extraction theorem proves the
dynamic SAT lower bound for faithful observers. -/
theorem faithful_dynamicSATLowerBound_of_dynamicNFrameLagrangianExtraction
    (enc : ThreeCNFEncoding)
    (hextract : UniversalDynamicNFrameLagrangianExtraction enc) :
    DynamicCEW.NP_side_lower_bound
      (TrajectoryObserverWidths (FaithfulSATObserverClass enc)) :=
  faithful_dynamicSATLowerBound_of_universalFaithfulExtraction enc
    (faithfulExtraction_of_dynamicNFrameLagrangianExtraction enc hextract)

/-- Full paper-main dynamic SAT lower bound, once operational observers are
presented faithfully.

This is still conditional on the actual new lower-bound theorem
`UniversalDynamicNFrameLagrangianExtraction`; the file does not assume or prove
that theorem. -/
theorem paperMain_dynamicSATLowerBound_of_dynamicNFrameLagrangianExtraction
    (enc : ThreeCNFEncoding)
    (hextract : UniversalDynamicNFrameLagrangianExtraction enc)
    (hpresent : PaperMainFaithfulObserverPresentation enc) :
    PaperMainDynamicSATLowerBound enc :=
  paperMain_dynamicSATLowerBound_of_faithfulLowerBound_and_presentation
    enc
    (faithful_dynamicSATLowerBound_of_dynamicNFrameLagrangianExtraction
      enc hextract)
    hpresent

/-- Complete positive-program surface for the dynamic Lagrangian pivot.

The three fields correspond to the honest requirements:
* P-side dynamic calibration;
* faithful presentation of operational observers;
* the new SAT-side dynamic N-frame/Lagrangian extraction theorem.
-/
structure DynamicNFrameLagrangianPositiveProgram
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop) : Prop where
  p_side_dynamic_calibration : PaperMainPObserverCalibration PDecider
  faithful_presentation : PaperMainFaithfulObserverPresentation enc
  sat_dynamic_lagrangian_extraction :
    UniversalDynamicNFrameLagrangianExtraction enc

/-- A completed dynamic N-frame/Lagrangian positive program gives exactly the
paper-main observer separation criterion. -/
theorem paperMain_observerSeparationCriterion_of_dynamicNFrameLagrangianProgram
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (program : DynamicNFrameLagrangianPositiveProgram enc PDecider) :
    PaperMainObserverSeparationCriterion enc PDecider :=
  ⟨program.p_side_dynamic_calibration,
    paperMain_dynamicSATLowerBound_of_dynamicNFrameLagrangianExtraction
      enc
      program.sat_dynamic_lagrangian_extraction
      program.faithful_presentation⟩

/-! ## Kernel-only axiom trace -/

#print axioms DynamicNFrameLagrangianObserver.toTrajectory_faithful
#print axioms DynamicNFrameLagrangianLiveMinor.toTrajectoryMinor
#print axioms faithfulExtraction_of_dynamicNFrameLagrangianExtraction
#print axioms faithful_dynamicSATLowerBound_of_dynamicNFrameLagrangianExtraction
#print axioms paperMain_dynamicSATLowerBound_of_dynamicNFrameLagrangianExtraction
#print axioms paperMain_observerSeparationCriterion_of_dynamicNFrameLagrangianProgram

end PallLean.Paper93.DeepMath.PathB
