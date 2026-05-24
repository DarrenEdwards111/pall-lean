import PallLean.Paper93.DeepMath.PathB.FiniteControlLiveRankObstruction

/-!
# Full-configuration live-rank correction

`FaithfulStateRankAt` ranks only the finite control state
`(TuringMachine.run ...).state.val`.  `FiniteControlLiveRankObstruction`
proves that this carrier is too small: every such rank is bounded by a fixed
finite-control maximum, independent of the input length.

This file installs the next faithful carrier.  A live-rank accounting function
may now inspect the full live DTM configuration at length `n`: finite control
state, head position, and tape contents.  This is still tied to an actual DTM
trajectory, but it is no longer forced through a finite state-code bottleneck.

No SAT lower bound is proved here.  The file gives the corrected socket: a
uniform semantic live-minor discharge over full configurations would imply the
existing observer separation criterion.  It also proves that if the new socket
is instantiated by merely projecting back to finite control, the old obstruction
returns immediately.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- A live-rank accounting function for the full configuration of a fixed DTM.

The argument includes the input length because the configuration type itself is
length indexed through `TuringMachine.tapeSize M n`. -/
abbrev FullConfigurationContextRank (M : TuringMachine.DTM) : Type :=
  (n : Nat) ->
    TuringMachine.Configuration M (TuringMachine.tapeSize M n) -> Nat

/-- The finite-control rank accounting embedded into the full-configuration
carrier.  This is the degenerate case that the old obstruction rules out. -/
def finiteControlFullConfigurationContextRank
    (M : TuringMachine.DTM) (stateContextRank : Nat -> Nat) :
    FullConfigurationContextRank M :=
  fun _ config => stateContextRank config.state.val

/-- Full-configuration live rank at a concrete time.  Outside the declared DTM
time window, the bounded-run context is zero. -/
noncomputable def FaithfulFullConfigurationRankAt
    (M : TuringMachine.DTM)
    (configContextRank : FullConfigurationContextRank M)
    (n : Nat) (input : Fin n -> Bool) (t : Nat) : Nat :=
  if hn : n >= 1 then
    if _ : t < TuringMachine.timeSteps M n + 1 then
      configContextRank n
        (TuringMachine.run M n t
          (TuringMachine.initialConfig M n hn input))
    else
      0
  else
    0

/-- Canonical full-configuration faithful width: the maximum full-configuration
rank over all length-`n` inputs and all times in the DTM's polynomial time
window. -/
noncomputable def FaithfulFullConfigurationTrajectoryWidth
    (M : TuringMachine.DTM)
    (configContextRank : FullConfigurationContextRank M) :
    DynamicCEW.ObserverWidth :=
  fun n =>
    if hn : n >= 1 then
      Finset.univ.sup (fun input : Fin n -> Bool =>
        Finset.univ.sup
          (fun t : Fin (TuringMachine.timeSteps M n + 1) =>
            configContextRank n
              (TuringMachine.run M n t.val
                (TuringMachine.initialConfig M n hn input))))
    else
      0

/-- The canonical full-configuration width bounds every full-configuration live
rank point. -/
theorem FaithfulFullConfigurationRankAt_le_width
    (M : TuringMachine.DTM)
    (configContextRank : FullConfigurationContextRank M)
    (n : Nat) (input : Fin n -> Bool) (t : Nat) :
    FaithfulFullConfigurationRankAt M configContextRank n input t <=
      FaithfulFullConfigurationTrajectoryWidth M configContextRank n := by
  classical
  unfold FaithfulFullConfigurationRankAt
    FaithfulFullConfigurationTrajectoryWidth
  by_cases hn : n >= 1
  · by_cases ht : t < TuringMachine.timeSteps M n + 1
    · rw [dif_pos hn, dif_pos ht, dif_pos hn]
      let tf : Fin (TuringMachine.timeSteps M n + 1) := ⟨t, ht⟩
      have htime :
          configContextRank n
              (TuringMachine.run M n t
                (TuringMachine.initialConfig M n hn input)) <=
            Finset.univ.sup
              (fun tf' : Fin (TuringMachine.timeSteps M n + 1) =>
                configContextRank n
                  (TuringMachine.run M n tf'.val
                    (TuringMachine.initialConfig M n hn input))) := by
        simpa [tf] using
          (Finset.le_sup
            (s := (Finset.univ :
              Finset (Fin (TuringMachine.timeSteps M n + 1))))
            (f := fun tf' : Fin (TuringMachine.timeSteps M n + 1) =>
              configContextRank n
                (TuringMachine.run M n tf'.val
                  (TuringMachine.initialConfig M n hn input)))
            (b := tf)
            (hb := by simp))
      have hinput :
          Finset.univ.sup
              (fun tf' : Fin (TuringMachine.timeSteps M n + 1) =>
                configContextRank n
                  (TuringMachine.run M n tf'.val
                    (TuringMachine.initialConfig M n hn input))) <=
            Finset.univ.sup (fun input' : Fin n -> Bool =>
              Finset.univ.sup
                (fun tf' : Fin (TuringMachine.timeSteps M n + 1) =>
                  configContextRank n
                    (TuringMachine.run M n tf'.val
                      (TuringMachine.initialConfig M n hn input')))) := by
        exact
          Finset.le_sup
            (s := (Finset.univ : Finset (Fin n -> Bool)))
            (f := fun input' : Fin n -> Bool =>
              Finset.univ.sup
                (fun tf' : Fin (TuringMachine.timeSteps M n + 1) =>
                  configContextRank n
                    (TuringMachine.run M n tf'.val
                      (TuringMachine.initialConfig M n hn input'))))
            (b := input)
            (hb := by simp)
      exact le_trans htime hinput
    · rw [dif_pos hn, dif_neg ht, dif_pos hn]
      exact Nat.zero_le _
  · rw [dif_neg hn, dif_neg hn]

/-- Full-configuration faithful observer generated by a DTM and a real
configuration-rank accounting function. -/
noncomputable def faithfulFullConfigurationTrajectoryObserver
    (M : TuringMachine.DTM)
    (configContextRank : FullConfigurationContextRank M) :
    TrajectoryObserverMachine where
  width := FaithfulFullConfigurationTrajectoryWidth M configContextRank
  acceptsInput := fun n input =>
    if hn : n >= 1 then TuringMachine.accepts M n hn input else False
  stateCode := fun n input t =>
    if hn : n >= 1 then
      (TuringMachine.run M n t
        (TuringMachine.initialConfig M n hn input)).state.val
    else
      0
  liveBoundaryRank := FaithfulFullConfigurationRankAt M configContextRank
  liveBoundaryRank_le_width :=
    FaithfulFullConfigurationRankAt_le_width M configContextRank

/-- The full-configuration observer is realized by its generating DTM. -/
theorem faithfulFullConfigurationTrajectoryObserver_realizes
    (M : TuringMachine.DTM)
    (configContextRank : FullConfigurationContextRank M) :
    DTMRealizesTrajectoryObserver M
      (faithfulFullConfigurationTrajectoryObserver M configContextRank) := by
  constructor
  · intro n hn input
    simp [faithfulFullConfigurationTrajectoryObserver, hn]
  · intro n hn input t
    simp [faithfulFullConfigurationTrajectoryObserver, hn]

/-- Full-configuration faithful operational SAT observers. -/
def FaithfulFullConfigurationOperationalTrajectoryObserverDecidesSAT
    (enc : ThreeCNFEncoding) (T : TrajectoryObserverMachine) : Prop :=
  exists M : TuringMachine.DTM,
    exists configContextRank : FullConfigurationContextRank M,
      DTMDecidesSATWithEncoding enc M /\
        T = faithfulFullConfigurationTrajectoryObserver M configContextRank

/-- Full-configuration faithful observers are operational SAT observers. -/
theorem OperationalTrajectoryObserverDecidesSAT_of_fullConfigurationFaithful
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine}
    (hT : FaithfulFullConfigurationOperationalTrajectoryObserverDecidesSAT
      enc T) :
    OperationalTrajectoryObserverDecidesSAT enc T := by
  rcases hT with ⟨M, configContextRank, hdec, rfl⟩
  exact ⟨M, hdec,
    faithfulFullConfigurationTrajectoryObserver_realizes
      M configContextRank⟩

/-- The old finite-control live rank is exactly the full-configuration live rank
obtained by projecting each configuration to its finite control state. -/
theorem FaithfulFullConfigurationRankAt_finiteControl_eq
    (M : TuringMachine.DTM) (stateContextRank : Nat -> Nat)
    (n : Nat) (input : Fin n -> Bool) (t : Nat) :
    FaithfulFullConfigurationRankAt M
        (finiteControlFullConfigurationContextRank M stateContextRank)
        n input t =
      FaithfulStateRankAt M stateContextRank n input t := by
  rfl

/-- Same equivalence at the trajectory-width level. -/
theorem FaithfulFullConfigurationTrajectoryWidth_finiteControl_eq
    (M : TuringMachine.DTM) (stateContextRank : Nat -> Nat) :
    FaithfulFullConfigurationTrajectoryWidth M
        (finiteControlFullConfigurationContextRank M stateContextRank) =
      FaithfulTrajectoryWidth M stateContextRank := by
  rfl

/-- Semantic validity predicate for full-configuration rank accounting. -/
abbrev FaithfulFullConfigurationLiveRankSemanticsPredicate : Type :=
  (M : TuringMachine.DTM) -> FullConfigurationContextRank M -> Prop

/-- Semantically corrected full-configuration SAT observer class. -/
def FaithfulFullConfigurationSemanticSATObserverClass
    (enc : ThreeCNFEncoding)
    (LiveRankSemantics :
      FaithfulFullConfigurationLiveRankSemanticsPredicate)
    (T : TrajectoryObserverMachine) : Prop :=
  exists M : TuringMachine.DTM,
    exists configContextRank : FullConfigurationContextRank M,
      DTMDecidesSATWithEncoding enc M /\
        LiveRankSemantics M configContextRank /\
          T = faithfulFullConfigurationTrajectoryObserver
            M configContextRank

/-- A certified semantic live boundary at one length, with the upper bound
stated against the full live configuration rank. -/
structure FaithfulFullConfigurationSemanticLiveBoundaryAt
    (enc : ThreeCNFEncoding)
    (M : TuringMachine.DTM)
    (configContextRank : FullConfigurationContextRank M)
    (n : Nat) : Type where
  input : Fin n -> Bool
  formula : ThreeCNF
  encoded : enc.Encodes input formula
  formula_satisfiable : formula.IsSatisfiable
  time : Nat
  state : Nat
  state_matches :
    state =
      (faithfulFullConfigurationTrajectoryObserver
        M configContextRank).stateCode n input time
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
  rank_le_configContext :
    liveRank <= FaithfulFullConfigurationRankAt
      M configContextRank n input time

/-- A full-configuration semantic certificate builds the existing trajectory
God-Move boundary minor. -/
def FaithfulFullConfigurationSemanticLiveBoundaryAt.toTrajectoryMinor
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM}
    {configContextRank : FullConfigurationContextRank M}
    {n : Nat}
    (cert :
      FaithfulFullConfigurationSemanticLiveBoundaryAt
        enc M configContextRank n) :
    TrajectoryGodMoveBoundaryMinor enc
      (faithfulFullConfigurationTrajectoryObserver
        M configContextRank) n where
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
  rank_le_boundary := cert.rank_le_configContext

/-- Nonempty full-configuration semantic certificates yield nonempty trajectory
minors. -/
theorem trajectoryMinor_of_fullConfigurationSemanticLiveBoundaryAt
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM}
    {configContextRank : FullConfigurationContextRank M}
    {n : Nat}
    (hcert : Nonempty
      (FaithfulFullConfigurationSemanticLiveBoundaryAt
        enc M configContextRank n)) :
    Nonempty (TrajectoryGodMoveBoundaryMinor enc
      (faithfulFullConfigurationTrajectoryObserver
        M configContextRank) n) := by
  rcases hcert with ⟨cert⟩
  exact ⟨cert.toTrajectoryMinor⟩

/-- Uniform full-configuration semantic live-minor discharge.

This is the corrected hard theorem.  Unlike the finite-control socket, this
statement is not refuted just by the finiteness of the DTM control state set.
It still remains the real SAT lower-bound theorem. -/
def UniformFaithfulFullConfigurationSemanticLiveMinorDischarge
    (enc : ThreeCNFEncoding)
    (LiveRankSemantics :
      FaithfulFullConfigurationLiveRankSemanticsPredicate) : Prop :=
  forall c : Nat, exists n : Nat,
    n >= 2 ^ 20 /\
      4 * (c + 1) <= Nat.log 2 n /\
        forall (M : TuringMachine.DTM)
            (configContextRank : FullConfigurationContextRank M),
          DTMDecidesSATWithEncoding enc M ->
            LiveRankSemantics M configContextRank ->
              Nonempty
                (FaithfulFullConfigurationSemanticLiveBoundaryAt
                  enc M configContextRank n)

/-- The corrected full-configuration discharge implies universal extraction for
the full-configuration semantic faithful SAT observer class. -/
theorem universalFullConfigurationSemanticFaithfulExtraction_of_discharge
    (enc : ThreeCNFEncoding)
    (LiveRankSemantics :
      FaithfulFullConfigurationLiveRankSemanticsPredicate)
    (hdischarge :
      UniformFaithfulFullConfigurationSemanticLiveMinorDischarge
        enc LiveRankSemantics) :
    UniversalTrajectorySATGodMoveExtraction enc
      (FaithfulFullConfigurationSemanticSATObserverClass
        enc LiveRankSemantics) := by
  intro c
  rcases hdischarge c with ⟨n, hn20, hlog, hcert_at⟩
  refine ⟨n, hn20, hlog, ?_⟩
  intro T hT
  rcases hT with ⟨M, configContextRank, hdec, hsem, rfl⟩
  exact trajectoryMinor_of_fullConfigurationSemanticLiveBoundaryAt
    (hcert_at M configContextRank hdec hsem)

/-- The full-configuration semantic discharge gives the dynamic SAT lower bound
for the full-configuration semantic faithful class. -/
theorem fullConfigurationSemanticFaithful_dynamicSATLowerBound_of_discharge
    (enc : ThreeCNFEncoding)
    (LiveRankSemantics :
      FaithfulFullConfigurationLiveRankSemanticsPredicate)
    (hdischarge :
      UniformFaithfulFullConfigurationSemanticLiveMinorDischarge
        enc LiveRankSemantics) :
    DynamicCEW.NP_side_lower_bound
      (TrajectoryObserverWidths
        (FaithfulFullConfigurationSemanticSATObserverClass
          enc LiveRankSemantics)) :=
  NP_side_lower_bound_of_universalTrajectorySATGodMoveExtraction
    enc
    (FaithfulFullConfigurationSemanticSATObserverClass
      enc LiveRankSemantics)
    (universalFullConfigurationSemanticFaithfulExtraction_of_discharge
      enc LiveRankSemantics hdischarge)

/-- Presentation hypothesis for moving from operational SAT observers to the
full-configuration semantic faithful class. -/
def PaperMainFullConfigurationSemanticFaithfulObserverPresentation
    (enc : ThreeCNFEncoding)
    (LiveRankSemantics :
      FaithfulFullConfigurationLiveRankSemanticsPredicate) : Prop :=
  forall T : TrajectoryObserverMachine,
    OperationalTrajectoryObserverDecidesSAT enc T ->
      FaithfulFullConfigurationSemanticSATObserverClass
        enc LiveRankSemantics T

/-- Full-configuration semantic closure package. -/
structure FaithfulFullConfigurationSemanticPaperMainClosureWiring
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (LiveRankSemantics :
      FaithfulFullConfigurationLiveRankSemanticsPredicate) : Prop where
  p_side_calibration : PaperMainPObserverCalibration PDecider
  semantic_presentation :
    PaperMainFullConfigurationSemanticFaithfulObserverPresentation
      enc LiveRankSemantics
  semantic_live_minor_discharge :
    UniformFaithfulFullConfigurationSemanticLiveMinorDischarge
      enc LiveRankSemantics

/-- A full-configuration semantic faithful lower bound plus presentation gives
the paper-main dynamic SAT lower bound. -/
theorem paperMain_dynamicSATLowerBound_of_fullConfigurationSemanticLowerBound_and_presentation
    (enc : ThreeCNFEncoding)
    (LiveRankSemantics :
      FaithfulFullConfigurationLiveRankSemanticsPredicate)
    (hlower :
      DynamicCEW.NP_side_lower_bound
        (TrajectoryObserverWidths
          (FaithfulFullConfigurationSemanticSATObserverClass
            enc LiveRankSemantics)))
    (hpresent :
      PaperMainFullConfigurationSemanticFaithfulObserverPresentation
        enc LiveRankSemantics) :
    PaperMainDynamicSATLowerBound enc := by
  intro c
  rcases hlower c with ⟨n, hnot_fullConfiguration⟩
  refine ⟨n, ?_⟩
  intro hcew
  rcases hcew with ⟨w, hw_decides, hw_bound⟩
  rcases hw_decides with ⟨T, hdec, hwidth_eq⟩
  exact hnot_fullConfiguration
    ⟨w, ⟨T, hpresent T hdec, hwidth_eq⟩, hw_bound⟩

/-- The full-configuration closure package gives the paper-main dynamic SAT
lower bound. -/
theorem paperMain_dynamicSATLowerBound_of_fullConfigurationSemanticClosureWiring
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (LiveRankSemantics :
      FaithfulFullConfigurationLiveRankSemanticsPredicate)
    (wiring :
      FaithfulFullConfigurationSemanticPaperMainClosureWiring
        enc PDecider LiveRankSemantics) :
    PaperMainDynamicSATLowerBound enc :=
  paperMain_dynamicSATLowerBound_of_fullConfigurationSemanticLowerBound_and_presentation
    enc LiveRankSemantics
    (fullConfigurationSemanticFaithful_dynamicSATLowerBound_of_discharge
      enc LiveRankSemantics wiring.semantic_live_minor_discharge)
    wiring.semantic_presentation

/-- Final paper-main observer separation criterion from the corrected
full-configuration semantic closure package. -/
theorem paperMain_observerSeparationCriterion_of_fullConfigurationSemanticClosureWiring
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (LiveRankSemantics :
      FaithfulFullConfigurationLiveRankSemanticsPredicate)
    (wiring :
      FaithfulFullConfigurationSemanticPaperMainClosureWiring
        enc PDecider LiveRankSemantics) :
    PaperMainObserverSeparationCriterion enc PDecider :=
  ⟨wiring.p_side_calibration,
    paperMain_dynamicSATLowerBound_of_fullConfigurationSemanticClosureWiring
      enc PDecider LiveRankSemantics wiring⟩

/-- If a full-configuration boundary uses only the finite-control projection,
the finite-control obstruction still forbids a binomial-size certificate. -/
theorem no_fullConfigurationSemanticLiveBoundaryAt_of_finiteControlProjection
    {enc : ThreeCNFEncoding}
    (M : TuringMachine.DTM)
    (stateContextRank : Nat -> Nat)
    {n : Nat}
    (hchoose :
      finiteControlStateContextRankMax M stateContextRank <
        Nat.choose (n / 3) (Nat.log 2 n)) :
    Not (Nonempty
      (FaithfulFullConfigurationSemanticLiveBoundaryAt enc M
        (finiteControlFullConfigurationContextRank M stateContextRank)
        n)) := by
  intro hcert
  rcases hcert with ⟨cert⟩
  have hlive_le_state :
      cert.liveRank <=
        FaithfulStateRankAt M stateContextRank n cert.input cert.time := by
    simpa [FaithfulFullConfigurationRankAt_finiteControl_eq]
      using cert.rank_le_configContext
  have hlive_le_max :
      cert.liveRank <=
        finiteControlStateContextRankMax M stateContextRank :=
    le_trans hlive_le_state
      (FaithfulStateRankAt_le_finiteControlStateContextRankMax
        M stateContextRank n cert.input cert.time)
  have hchoose_le_max :
      Nat.choose (n / 3) (Nat.log 2 n) <=
        finiteControlStateContextRankMax M stateContextRank :=
    le_trans cert.rank_lower hlive_le_max
  exact (not_le_of_gt hchoose) hchoose_le_max

/-- Therefore a successful full-configuration discharge must reject the
degenerate finite-control projection of any SAT-deciding presentation. -/
theorem fullConfigurationDischarge_excludes_finiteControlProjectionPresentations
    {enc : ThreeCNFEncoding}
    {LiveRankSemantics :
      FaithfulFullConfigurationLiveRankSemanticsPredicate}
    {M : TuringMachine.DTM}
    {stateContextRank : Nat -> Nat}
    (hdec : DTMDecidesSATWithEncoding enc M)
    (hsem :
      LiveRankSemantics M
        (finiteControlFullConfigurationContextRank M stateContextRank)) :
    Not
      (UniformFaithfulFullConfigurationSemanticLiveMinorDischarge
        enc LiveRankSemantics) := by
  intro hdischarge
  let C := finiteControlStateContextRankMax M stateContextRank
  rcases hdischarge C with ⟨n, hn20, hlog, hcert_at⟩
  have hn2 : n >= 2 := by
    exact le_trans (by norm_num : 2 <= 2 ^ 20) hn20
  have hC_le_npow : C <= n ^ C :=
    finiteControlRankMax_le_pow_of_large_length C n hn2
  have hgap : n ^ C < Nat.choose (n / 3) (Nat.log 2 n) :=
    arithmetic_gap_for_exponent C n hn20 hlog
  have hC_lt_choose :
      C < Nat.choose (n / 3) (Nat.log 2 n) :=
    lt_of_le_of_lt hC_le_npow hgap
  exact
    (no_fullConfigurationSemanticLiveBoundaryAt_of_finiteControlProjection
      (enc := enc) M stateContextRank hC_lt_choose)
      (hcert_at M
        (finiteControlFullConfigurationContextRank M stateContextRank)
        hdec hsem)

#print axioms FaithfulFullConfigurationRankAt_le_width
#print axioms faithfulFullConfigurationTrajectoryObserver_realizes
#print axioms universalFullConfigurationSemanticFaithfulExtraction_of_discharge
#print axioms fullConfigurationSemanticFaithful_dynamicSATLowerBound_of_discharge
#print axioms no_fullConfigurationSemanticLiveBoundaryAt_of_finiteControlProjection
#print axioms fullConfigurationDischarge_excludes_finiteControlProjectionPresentations

end PallLean.Paper93.DeepMath.PathB
