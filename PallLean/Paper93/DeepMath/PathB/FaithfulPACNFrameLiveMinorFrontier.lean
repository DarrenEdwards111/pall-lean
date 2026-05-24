import PallLean.Paper93.DeepMath.PathB.FaithfulPACNFrameLiveRankSemantics

/-!
# PAC/N-frame live-minor frontier

The positive PAC/N-frame live-rank semantics removes the fake zero-rank
presentation, but it is still too weak to close the P-vs-NP route: constant
rank `1` satisfies the positive semantics and still cannot carry a binomial
God-Move minor at the extraction scale.

This file records that frontier formally and installs the next corrected
socket: a uniform binomial PAC/N-frame live-rank semantics.  Under that stronger
semantic predicate, the live-minor discharge is mechanical; the remaining
mathematical work moves to proving that actual polynomial-time SAT observers
satisfy the uniform binomial PAC/N-frame semantics.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Constant-one state-context rank accounting. -/
def oneStateContextRank : Nat -> Nat :=
  fun _ => 1

/-- Constant-one state-context rank is always at most one. -/
theorem FaithfulStateRankAt_oneStateContextRank_le_one
    (M : TuringMachine.DTM) (n : Nat) (input : Fin n -> Bool) (t : Nat) :
    FaithfulStateRankAt M oneStateContextRank n input t <= 1 := by
  unfold FaithfulStateRankAt oneStateContextRank
  by_cases hn : n >= 1
  · by_cases ht : t < TuringMachine.timeSteps M n + 1
    · simp [hn, ht]
    · simp [hn, ht]
  · simp [hn]

/-- At time zero and positive length, constant-one state-context rank is
actually one. -/
theorem FaithfulStateRankAt_oneStateContextRank_time_zero
    (M : TuringMachine.DTM) {n : Nat} (hn : n >= 1)
    (input : Fin n -> Bool) :
    FaithfulStateRankAt M oneStateContextRank n input 0 = 1 := by
  unfold FaithfulStateRankAt oneStateContextRank
  have ht : 0 < TuringMachine.timeSteps M n + 1 := Nat.succ_pos _
  simp [hn, ht]

/-- A canonical extraction-scale length for a polynomial exponent target. -/
def extractionScaleLength (c : Nat) : Nat :=
  2 ^ (4 * (c + 1) + 20)

/-- The canonical extraction-scale length is at least `2^20`. -/
theorem extractionScaleLength_ge_2pow20 (c : Nat) :
    extractionScaleLength c >= 2 ^ 20 := by
  unfold extractionScaleLength
  exact Nat.pow_le_pow_right
    (by norm_num : 1 <= 2)
    (by omega : 20 <= 4 * (c + 1) + 20)

/-- The canonical extraction-scale length has enough binary logarithm. -/
theorem extractionScaleLength_log_ge (c : Nat) :
    4 * (c + 1) <= Nat.log 2 (extractionScaleLength c) := by
  unfold extractionScaleLength
  have hpow :
      2 ^ (4 * (c + 1)) <= 2 ^ (4 * (c + 1) + 20) :=
    Nat.pow_le_pow_right
      (by norm_num : 1 <= 2)
      (by omega : 4 * (c + 1) <= 4 * (c + 1) + 20)
  exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow

/-- Constant-one rank still satisfies the positive PAC/N-frame semantics.  This
is why positivity alone cannot close the live-minor discharge. -/
theorem FaithfulPACNFrameLiveRankSemantics_oneStateContextRank
    (M : TuringMachine.DTM) :
    FaithfulPACNFrameLiveRankSemantics M oneStateContextRank := by
  refine FaithfulPACNFrameLiveRankSemantics_of_positive_stateContextRank ?_
  intro c
  let n := extractionScaleLength c
  have hn20 : n >= 2 ^ 20 := extractionScaleLength_ge_2pow20 c
  have hlog : 4 * (c + 1) <= Nat.log 2 n :=
    extractionScaleLength_log_ge c
  have hn1 : n >= 1 := by
    exact le_trans (by norm_num : 1 <= 2 ^ 20) hn20
  let input : Fin n -> Bool := fun _ => false
  refine ⟨n, input, 0, hn20, hlog, ?_⟩
  have hrank :
      FaithfulStateRankAt M oneStateContextRank n input 0 = 1 :=
    FaithfulStateRankAt_oneStateContextRank_time_zero M hn1 input
  rw [hrank]
  norm_num

/-- Constant-one rank cannot carry a semantic live-boundary certificate at an
extraction scale, because the binomial lower bound is already larger than one. -/
theorem no_semanticLiveBoundaryAt_of_oneRankFaithfulObserver
    {enc : ThreeCNFEncoding}
    (M : TuringMachine.DTM)
    {n : Nat}
    (hn20 : n >= 2 ^ 20)
    (hlog : 4 * (0 + 1) <= Nat.log 2 n) :
    Not (Nonempty
      (FaithfulSemanticLiveBoundaryAt enc M oneStateContextRank n)) := by
  intro hcert
  rcases hcert with ⟨cert⟩
  have hlive_le_one : cert.liveRank <= 1 := by
    exact le_trans cert.rank_le_stateContext
      (FaithfulStateRankAt_oneStateContextRank_le_one
        M n cert.input cert.time)
  have hchoose_le_one :
      Nat.choose (n / 3) (Nat.log 2 n) <= 1 :=
    le_trans cert.rank_lower hlive_le_one
  have hchoose_gt_one :
      1 < Nat.choose (n / 3) (Nat.log 2 n) := by
    simpa using arithmetic_gap_for_exponent 0 n hn20 hlog
  exact (not_le_of_gt hchoose_gt_one) hchoose_le_one

/-- Therefore the current positive PAC/N-frame semantics cannot discharge the
uniform binomial live-minor theorem in the presence of a SAT-deciding DTM. -/
theorem not_FaithfulPACNFrameSemanticLiveMinorDischarge_of_oneRankFaithfulDecider
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM}
    (hdec : DTMDecidesSATWithEncoding enc M) :
    Not (FaithfulPACNFrameSemanticLiveMinorDischarge enc) := by
  intro hdischarge
  rcases hdischarge 0 with ⟨n, hn20, hlog, hcert_at⟩
  exact
    (no_semanticLiveBoundaryAt_of_oneRankFaithfulObserver
      (enc := enc) M hn20 hlog)
      (hcert_at M oneStateContextRank hdec
        (FaithfulPACNFrameLiveRankSemantics_oneStateContextRank M))

/-! ## Corrected uniform binomial semantic socket -/

/-- Uniform binomial PAC/N-frame live-rank semantics.

This is stronger than the positive PAC/N-frame semantics: it says the semantic
rank accounting carries full `FaithfulSemanticLiveBoundaryAt` certificates at
every extraction scale.  With this predicate, the live-minor discharge becomes
pure wiring.
-/
def FaithfulPACNFrameUniformBinomialLiveRankSemantics
    (enc : ThreeCNFEncoding) : FaithfulLiveRankSemanticsPredicate :=
  fun M stateContextRank =>
    forall (c n : Nat),
      n >= 2 ^ 20 ->
        4 * (c + 1) <= Nat.log 2 n ->
          Nonempty
            (FaithfulSemanticLiveBoundaryAt enc M stateContextRank n)

/-- The uniform binomial PAC/N-frame semantics mechanically supplies the
semantic live-minor discharge. -/
theorem uniformSemanticLiveMinorDischarge_of_uniformBinomialPACNFrameSemantics
    (enc : ThreeCNFEncoding) :
    UniformFaithfulSemanticLiveMinorDischarge enc
      (FaithfulPACNFrameUniformBinomialLiveRankSemantics enc) := by
  intro c
  let n := extractionScaleLength c
  have hn20 : n >= 2 ^ 20 := extractionScaleLength_ge_2pow20 c
  have hlog : 4 * (c + 1) <= Nat.log 2 n :=
    extractionScaleLength_log_ge c
  refine ⟨n, hn20, hlog, ?_⟩
  intro M stateContextRank _hdec hsem
  exact hsem c n hn20 hlog

/-- Closure wiring specialized to the uniform binomial PAC/N-frame semantics. -/
abbrev FaithfulPACNFrameUniformBinomialSemanticPaperMainClosureWiring
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop) : Prop :=
  FaithfulSemanticPaperMainClosureWiring
    enc PDecider (FaithfulPACNFrameUniformBinomialLiveRankSemantics enc)

/-- Final observer separation from semantic presentation into the uniform
binomial PAC/N-frame semantics. -/
theorem paperMain_observerSeparationCriterion_of_uniformBinomialPACNFrameClosureWiring
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (wiring :
      FaithfulPACNFrameUniformBinomialSemanticPaperMainClosureWiring
        enc PDecider) :
    PaperMainObserverSeparationCriterion enc PDecider :=
  paperMain_observerSeparationCriterion_of_semanticClosureWiring
    enc PDecider
    (FaithfulPACNFrameUniformBinomialLiveRankSemantics enc)
    wiring

/-- Split-field version: once P-side calibration and semantic presentation into
the uniform binomial PAC/N-frame semantics are proved, the live-minor discharge
field is supplied mechanically by
`uniformSemanticLiveMinorDischarge_of_uniformBinomialPACNFrameSemantics`. -/
theorem paperMain_observerSeparationCriterion_of_uniformBinomialPACNFrameFields
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (hp : PaperMainPObserverCalibration PDecider)
    (hpresent :
      PaperMainSemanticFaithfulObserverPresentation enc
        (FaithfulPACNFrameUniformBinomialLiveRankSemantics enc)) :
    PaperMainObserverSeparationCriterion enc PDecider :=
  paperMain_observerSeparationCriterion_of_uniformBinomialPACNFrameClosureWiring
    enc PDecider
    ⟨hp, hpresent,
      uniformSemanticLiveMinorDischarge_of_uniformBinomialPACNFrameSemantics
        enc⟩

#print axioms FaithfulPACNFrameLiveRankSemantics_oneStateContextRank
#print axioms not_FaithfulPACNFrameSemanticLiveMinorDischarge_of_oneRankFaithfulDecider
#print axioms uniformSemanticLiveMinorDischarge_of_uniformBinomialPACNFrameSemantics
#print axioms paperMain_observerSeparationCriterion_of_uniformBinomialPACNFrameFields

end PallLean.Paper93.DeepMath.PathB
