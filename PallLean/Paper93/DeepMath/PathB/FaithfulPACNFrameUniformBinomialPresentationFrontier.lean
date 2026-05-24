import PallLean.Paper93.DeepMath.PathB.FaithfulPACNFrameLiveMinorFrontier

/-!
# Uniform binomial presentation frontier

After `FaithfulPACNFrameLiveMinorFrontier`, the live-minor discharge is
mechanical once an observer is presented with uniform binomial PAC/N-frame
live-rank semantics.  The remaining nontrivial theorem is therefore the
semantic presentation theorem into that uniform binomial semantics.

This file records the final frontier: if a polynomial-time SAT DTM exists, its
constant-rank-one faithful observer is an operational SAT observer, but it
cannot be presented with uniform binomial PAC/N-frame live-rank semantics.  So
the remaining presentation theorem is already the P-vs-NP lower bound in this
route.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- A constant-one faithful observer cannot carry a trajectory God-Move minor at
an extraction scale: the live boundary is at most one, while the binomial lower
bound is larger than one. -/
theorem no_trajectoryMinor_of_oneRankFaithfulObserver
    {enc : ThreeCNFEncoding}
    (M : TuringMachine.DTM)
    {n : Nat}
    (hn20 : n >= 2 ^ 20)
    (hlog : 4 * (0 + 1) <= Nat.log 2 n) :
    Not (Nonempty (TrajectoryGodMoveBoundaryMinor enc
      (faithfulTrajectoryObserver M oneStateContextRank) n)) := by
  intro hminor
  rcases hminor with ⟨minor⟩
  have hlive_le_one : minor.liveRank <= 1 := by
    exact le_trans minor.rank_le_boundary
      (FaithfulStateRankAt_oneStateContextRank_le_one
        M n minor.input minor.time)
  have hchoose_le_one :
      Nat.choose (n / 3) (Nat.log 2 n) <= 1 :=
    le_trans minor.rank_lower hlive_le_one
  have hchoose_gt_one :
      1 < Nat.choose (n / 3) (Nat.log 2 n) := by
    simpa using arithmetic_gap_for_exponent 0 n hn20 hlog
  exact (not_le_of_gt hchoose_gt_one) hchoose_le_one

/-- The constant-rank-one faithful observer cannot belong to the semantic SAT
class for the uniform binomial PAC/N-frame semantics. -/
theorem not_oneRankPresentation_in_uniformBinomialSemanticSATObserverClass
    {enc : ThreeCNFEncoding}
    (M : TuringMachine.DTM) :
    Not (FaithfulSemanticSATObserverClass enc
      (FaithfulPACNFrameUniformBinomialLiveRankSemantics enc)
      (faithfulTrajectoryObserver M oneStateContextRank)) := by
  intro hT
  rcases hT with ⟨M', stateContextRank, _hdec', hsem, hT_eq⟩
  let n := extractionScaleLength 0
  have hn20 : n >= 2 ^ 20 := extractionScaleLength_ge_2pow20 0
  have hlog : 4 * (0 + 1) <= Nat.log 2 n :=
    extractionScaleLength_log_ge 0
  have hcert :
      Nonempty
        (FaithfulSemanticLiveBoundaryAt enc M' stateContextRank n) :=
    hsem 0 n hn20 hlog
  have hminor' :
      Nonempty (TrajectoryGodMoveBoundaryMinor enc
        (faithfulTrajectoryObserver M' stateContextRank) n) :=
    trajectoryMinor_of_semanticLiveBoundaryAt hcert
  have hminor_one :
      Nonempty (TrajectoryGodMoveBoundaryMinor enc
        (faithfulTrajectoryObserver M oneStateContextRank) n) := by
    simpa [hT_eq] using hminor'
  exact
    (no_trajectoryMinor_of_oneRankFaithfulObserver
      (enc := enc) M hn20 hlog) hminor_one

/-- If a SAT-deciding DTM exists, the semantic presentation theorem into the
uniform binomial PAC/N-frame semantics is false: apply the presentation theorem
to the constant-rank-one faithful observer of that DTM. -/
theorem not_uniformBinomialPACNFramePresentation_of_decider
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM}
    (hdec : DTMDecidesSATWithEncoding enc M) :
    Not (PaperMainSemanticFaithfulObserverPresentation enc
      (FaithfulPACNFrameUniformBinomialLiveRankSemantics enc)) := by
  intro hpresent
  let T : TrajectoryObserverMachine :=
    faithfulTrajectoryObserver M oneStateContextRank
  have hfaithful : FaithfulSATObserverClass enc T := by
    refine ⟨M, oneStateContextRank, hdec, ?_⟩
    rfl
  have hoperational : OperationalTrajectoryObserverDecidesSAT enc T :=
    OperationalTrajectoryObserverDecidesSAT_of_faithful hfaithful
  exact
    (not_oneRankPresentation_in_uniformBinomialSemanticSATObserverClass
      (enc := enc) M)
      (hpresent T hoperational)

/-- Equivalently, proving the remaining semantic presentation theorem into the
uniform binomial PAC/N-frame semantics already proves that no polynomial-time
DTM in this repository's model decides SAT. -/
theorem no_DTMDecidesSATWithEncoding_of_uniformBinomialPACNFramePresentation
    (enc : ThreeCNFEncoding)
    (hpresent :
      PaperMainSemanticFaithfulObserverPresentation enc
        (FaithfulPACNFrameUniformBinomialLiveRankSemantics enc)) :
    Not (exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) := by
  intro hM
  rcases hM with ⟨M, hdec⟩
  exact
    (not_uniformBinomialPACNFramePresentation_of_decider
      (enc := enc) (M := M) hdec)
      hpresent

/-- The final split-field closure theorem is therefore exact: its presentation
field is already a no-polynomial-time-SAT theorem. -/
theorem no_DTMDecidesSATWithEncoding_of_uniformBinomialPACNFrameFields
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (_hp : PaperMainPObserverCalibration PDecider)
    (hpresent :
      PaperMainSemanticFaithfulObserverPresentation enc
        (FaithfulPACNFrameUniformBinomialLiveRankSemantics enc)) :
    Not (exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) :=
  no_DTMDecidesSATWithEncoding_of_uniformBinomialPACNFramePresentation
    enc hpresent

#print axioms not_uniformBinomialPACNFramePresentation_of_decider
#print axioms no_DTMDecidesSATWithEncoding_of_uniformBinomialPACNFramePresentation
#print axioms no_DTMDecidesSATWithEncoding_of_uniformBinomialPACNFrameFields

end PallLean.Paper93.DeepMath.PathB
