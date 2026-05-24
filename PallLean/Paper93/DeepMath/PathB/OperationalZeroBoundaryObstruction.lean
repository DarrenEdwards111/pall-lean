import PallLean.Paper93.DeepMath.PathB.ObserverTrajectoryDCEW

/-!
# Operational zero-boundary obstruction

The raw operational trajectory class ties acceptance and state code to a DTM,
but it does not tie `width` or `liveBoundaryRank` to the actual live
configuration data.  Therefore any SAT-deciding DTM can be presented as an
operational trajectory observer with identically zero boundary rank.

This records the exact obstruction: the universal operational live-minor
extraction theorem cannot be proved from the current operational predicate
alone.  The proof target must use a faithful/semantic live-rank predicate that
computes boundary rank from the actual observer state, not an arbitrary field.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- The degenerate operational trajectory observer realized by `M`: acceptance
and state code are the real DTM behavior, while width and live boundary rank
are identically zero. -/
noncomputable def zeroBoundaryOperationalTrajectoryObserver
    (M : TuringMachine.DTM) : TrajectoryObserverMachine where
  width := fun _ => 0
  acceptsInput := fun n input =>
    if hn : n >= 1 then TuringMachine.accepts M n hn input else False
  stateCode := fun n input t =>
    if hn : n >= 1 then
      (TuringMachine.run M n t
        (TuringMachine.initialConfig M n hn input)).state.val
    else
      0
  liveBoundaryRank := fun _ _ _ => 0
  liveBoundaryRank_le_width := by
    intro n input t
    rfl

/-- The zero-boundary observer is still operationally realized by the DTM. -/
theorem zeroBoundaryOperationalTrajectoryObserver_realizes
    (M : TuringMachine.DTM) :
    DTMRealizesTrajectoryObserver M
      (zeroBoundaryOperationalTrajectoryObserver M) := by
  constructor
  · intro n hn input
    simp [zeroBoundaryOperationalTrajectoryObserver, hn]
  · intro n hn input t
    simp [zeroBoundaryOperationalTrajectoryObserver, hn]

/-- If `M` decides SAT under the encoding, its zero-boundary trajectory
presentation is an operational SAT observer. -/
theorem zeroBoundaryOperationalTrajectoryObserver_decidesSAT
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM}
    (hdec : DTMDecidesSATWithEncoding enc M) :
    OperationalTrajectoryObserverDecidesSAT enc
      (zeroBoundaryOperationalTrajectoryObserver M) :=
  ⟨M, hdec, zeroBoundaryOperationalTrajectoryObserver_realizes M⟩

/-- Bounded-time version of the same zero-boundary operational presentation. -/
theorem zeroBoundaryOperationalTrajectoryObserver_decidesSATAtMost
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM}
    (hdec : DTMDecidesSATWithEncoding enc M) :
    OperationalTrajectoryObserverDecidesSATAtMost enc M.timeBound
      (zeroBoundaryOperationalTrajectoryObserver M) :=
  ⟨M, ⟨hdec, le_rfl⟩,
    zeroBoundaryOperationalTrajectoryObserver_realizes M⟩

/-- A positive-rank trajectory minor cannot live in the zero-boundary
operational presentation. -/
theorem no_trajectoryMinor_of_zeroBoundaryOperationalObserver
    {enc : ThreeCNFEncoding}
    (M : TuringMachine.DTM)
    {n : Nat}
    (hchoose_pos : 0 < Nat.choose (n / 3) (Nat.log 2 n)) :
    Not (Nonempty (TrajectoryGodMoveBoundaryMinor enc
      (zeroBoundaryOperationalTrajectoryObserver M) n)) := by
  intro hminor
  rcases hminor with ⟨minor⟩
  have hminor_width :
      Nat.choose (n / 3) (Nat.log 2 n) <=
        (zeroBoundaryOperationalTrajectoryObserver M).width n :=
    observer_width_lower_of_trajectory_minor minor
  have hchoose_le_zero :
      Nat.choose (n / 3) (Nat.log 2 n) <= 0 := by
    simpa [zeroBoundaryOperationalTrajectoryObserver] using hminor_width
  exact (not_le_of_gt hchoose_pos) hchoose_le_zero

/-- Therefore, if a SAT-deciding DTM exists, fixed-length operational
extraction fails at every positive binomial scale. -/
theorem not_operationalTrajectoryExtractionAt_of_zeroBoundaryDecider
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM}
    {n : Nat}
    (hdec : DTMDecidesSATWithEncoding enc M)
    (hchoose_pos : 0 < Nat.choose (n / 3) (Nat.log 2 n)) :
    Not (TrajectorySATGodMoveExtractionAt enc
      (OperationalTrajectoryObserverDecidesSAT enc) n) := by
  intro hextract
  exact
    (no_trajectoryMinor_of_zeroBoundaryOperationalObserver
      (enc := enc) M hchoose_pos)
      (hextract (zeroBoundaryOperationalTrajectoryObserver M)
        (zeroBoundaryOperationalTrajectoryObserver_decidesSAT hdec))

/-- Bounded-time version: the same obstruction hits the `timeBound <= e`
class at `e = M.timeBound`. -/
theorem not_operationalTrajectoryExtractionAtMostAt_of_zeroBoundaryDecider
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM}
    {n : Nat}
    (hdec : DTMDecidesSATWithEncoding enc M)
    (hchoose_pos : 0 < Nat.choose (n / 3) (Nat.log 2 n)) :
    Not (TrajectorySATGodMoveExtractionAt enc
      (OperationalTrajectoryObserverDecidesSATAtMost enc M.timeBound) n) := by
  intro hextract
  exact
    (no_trajectoryMinor_of_zeroBoundaryOperationalObserver
      (enc := enc) M hchoose_pos)
      (hextract (zeroBoundaryOperationalTrajectoryObserver M)
        (zeroBoundaryOperationalTrajectoryObserver_decidesSATAtMost hdec))

/-- Hence the universal operational extraction theorem itself is already a
no-polynomial-time-SAT theorem in this repository's DTM model. -/
theorem not_universalOperationalTrajectoryExtraction_of_zeroBoundaryDecider
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM}
    (hdec : DTMDecidesSATWithEncoding enc M) :
    Not (UniversalOperationalTrajectorySATGodMoveExtraction enc) := by
  intro hextract
  rcases hextract 0 with ⟨n, hn20, hlog, hextract_at⟩
  have hgap :
      n ^ 0 < Nat.choose (n / 3) (Nat.log 2 n) :=
    arithmetic_gap_for_exponent 0 n hn20 hlog
  have hchoose_pos :
      0 < Nat.choose (n / 3) (Nat.log 2 n) := by
    have hn_pow_pos : 0 < n ^ 0 := by simp
    exact lt_trans hn_pow_pos hgap
  exact
    (not_operationalTrajectoryExtractionAt_of_zeroBoundaryDecider
      (enc := enc) (M := M) hdec hchoose_pos)
      hextract_at

/-- Any proof of the universal operational extraction field would already
prove that no DTM decides SAT under the encoding. -/
theorem no_DTMDecidesSATWithEncoding_of_universalOperationalTrajectoryExtraction
    (enc : ThreeCNFEncoding)
    (hextract : UniversalOperationalTrajectorySATGodMoveExtraction enc) :
    Not (exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) := by
  intro hM
  rcases hM with ⟨M, hdec⟩
  exact
    (not_universalOperationalTrajectoryExtraction_of_zeroBoundaryDecider
      (enc := enc) (M := M) hdec)
      hextract

/-- The exponent-parametric extraction target is obstructed in the same way:
the candidate observer supplies its own finite time exponent. -/
theorem not_timeExponentParametricExtraction_of_zeroBoundaryDecider
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM}
    (hdec : DTMDecidesSATWithEncoding enc M) :
    Not (TimeExponentParametricOperationalTrajectoryExtraction enc) := by
  intro hextract
  rcases hextract M.timeBound 0 with ⟨n, hn20, hlog, hextract_at⟩
  have hgap :
      n ^ 0 < Nat.choose (n / 3) (Nat.log 2 n) :=
    arithmetic_gap_for_exponent 0 n hn20 hlog
  have hchoose_pos :
      0 < Nat.choose (n / 3) (Nat.log 2 n) := by
    have hn_pow_pos : 0 < n ^ 0 := by simp
    exact lt_trans hn_pow_pos hgap
  exact
    (not_operationalTrajectoryExtractionAtMostAt_of_zeroBoundaryDecider
      (enc := enc) (M := M) hdec hchoose_pos)
      hextract_at

/-- Consequently, the exponent-parametric geometric engine also contains the
whole no-polynomial-time-SAT lower bound as a field unless the observer class
is semantically strengthened. -/
theorem no_DTMDecidesSATWithEncoding_of_timeExponentParametricExtraction
    (enc : ThreeCNFEncoding)
    (hextract : TimeExponentParametricOperationalTrajectoryExtraction enc) :
    Not (exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) := by
  intro hM
  rcases hM with ⟨M, hdec⟩
  exact
    (not_timeExponentParametricExtraction_of_zeroBoundaryDecider
      (enc := enc) (M := M) hdec)
      hextract

theorem no_DTMDecidesSATWithEncoding_of_NFramePACHolographyEngine
    (enc : ThreeCNFEncoding)
    (engine : NFramePACHolographyAmplituhedronRamanujanEngine enc) :
    Not (exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) :=
  no_DTMDecidesSATWithEncoding_of_universalOperationalTrajectoryExtraction
    enc engine.polytime_observer_extraction

theorem no_DTMDecidesSATWithEncoding_of_timeExponentParametricEngine
    (enc : ThreeCNFEncoding)
    (engine :
      TimeExponentParametricNFramePACHolographyAmplituhedronRamanujanEngine
        enc) :
    Not (exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) :=
  no_DTMDecidesSATWithEncoding_of_timeExponentParametricExtraction
    enc engine.time_exponent_observer_extraction

#print axioms not_universalOperationalTrajectoryExtraction_of_zeroBoundaryDecider
#print axioms no_DTMDecidesSATWithEncoding_of_universalOperationalTrajectoryExtraction
#print axioms not_timeExponentParametricExtraction_of_zeroBoundaryDecider
#print axioms no_DTMDecidesSATWithEncoding_of_timeExponentParametricExtraction
#print axioms no_DTMDecidesSATWithEncoding_of_NFramePACHolographyEngine
#print axioms no_DTMDecidesSATWithEncoding_of_timeExponentParametricEngine

end PallLean.Paper93.DeepMath.PathB
