import PallLean.Paper93.DeepMath.PathB.FaithfulPACHolographyBridge

/-!
# Faithful live-minor obstruction

The current faithful observer class still permits an arbitrary
`stateContextRank : Nat -> Nat`.  In particular, any DTM presentation can be
paired with the constant-zero rank accounting function.

That means the live-minor discharge cannot be proved from the present
definitions alone.  At a positive binomial scale, a faithful observer with
zero state-context rank has no live boundary room in which to place a
`TrajectoryGodMoveBoundaryMinor`.

This file records the obstruction formally.  It does not prove or assume a SAT
decider exists; it proves that if one exists, the present faithful extraction
target is refuted by the zero-rank faithful presentation of that same DTM.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- The degenerate state-context rank accounting still allowed by the current
faithful observer definition. -/
def zeroStateContextRank : Nat -> Nat :=
  fun _ => 0

/-- With zero state-context rank, every live faithful state has rank zero. -/
theorem FaithfulStateRankAt_zeroStateContextRank
    (M : TuringMachine.DTM) (n : Nat) (input : Fin n -> Bool) (t : Nat) :
    FaithfulStateRankAt M zeroStateContextRank n input t = 0 := by
  unfold FaithfulStateRankAt zeroStateContextRank
  by_cases hn : n >= 1
  · by_cases ht : t < TuringMachine.timeSteps M n + 1
    · simp [hn, ht]
    · simp [hn, ht]
  · simp [hn]

/-- The faithful width induced by zero state-context rank is identically zero. -/
theorem FaithfulTrajectoryWidth_zeroStateContextRank
    (M : TuringMachine.DTM) (n : Nat) :
    FaithfulTrajectoryWidth M zeroStateContextRank n = 0 := by
  classical
  unfold FaithfulTrajectoryWidth zeroStateContextRank
  by_cases hn : n >= 1
  · simp [hn]
  · simp [hn]

/-- The zero-rank faithful observer exposes zero live boundary rank everywhere. -/
theorem faithful_zeroRank_liveBoundaryRank_eq_zero
    (M : TuringMachine.DTM) (n : Nat) (input : Fin n -> Bool) (t : Nat) :
    (faithfulTrajectoryObserver M zeroStateContextRank).liveBoundaryRank
      n input t = 0 := by
  change FaithfulStateRankAt M zeroStateContextRank n input t = 0
  exact FaithfulStateRankAt_zeroStateContextRank M n input t

/-- The zero-rank faithful observer has zero width at every length. -/
theorem faithful_zeroRank_width_eq_zero
    (M : TuringMachine.DTM) (n : Nat) :
    (faithfulTrajectoryObserver M zeroStateContextRank).width n = 0 := by
  change FaithfulTrajectoryWidth M zeroStateContextRank n = 0
  exact FaithfulTrajectoryWidth_zeroStateContextRank M n

/-- A positive-rank trajectory minor cannot live inside a zero-rank faithful
observer. -/
theorem no_trajectoryMinor_of_zeroRankFaithfulObserver
    {enc : ThreeCNFEncoding} (M : TuringMachine.DTM) {n : Nat}
    (hchoose_pos : 0 < Nat.choose (n / 3) (Nat.log 2 n)) :
    Not (Nonempty (TrajectoryGodMoveBoundaryMinor enc
      (faithfulTrajectoryObserver M zeroStateContextRank) n)) := by
  intro hminor
  rcases hminor with ⟨minor⟩
  have hminor_width :
      Nat.choose (n / 3) (Nat.log 2 n) <=
        (faithfulTrajectoryObserver M zeroStateContextRank).width n :=
    observer_width_lower_of_trajectory_minor minor
  have hchoose_le_zero :
      Nat.choose (n / 3) (Nat.log 2 n) <= 0 := by
    simpa [faithful_zeroRank_width_eq_zero M n] using hminor_width
  exact (not_le_of_gt hchoose_pos) hchoose_le_zero

/-- If a SAT-deciding DTM exists, then its zero-rank faithful presentation
refutes fixed-length faithful extraction at every positive binomial scale. -/
theorem not_TrajectorySATGodMoveExtractionAt_of_zeroRankFaithfulDecider
    {enc : ThreeCNFEncoding} {M : TuringMachine.DTM} {n : Nat}
    (hdec : DTMDecidesSATWithEncoding enc M)
    (hchoose_pos : 0 < Nat.choose (n / 3) (Nat.log 2 n)) :
    Not (TrajectorySATGodMoveExtractionAt enc (FaithfulSATObserverClass enc) n) := by
  intro hextract
  let T : TrajectoryObserverMachine :=
    faithfulTrajectoryObserver M zeroStateContextRank
  have hfaithful : FaithfulSATObserverClass enc T := by
    refine ⟨M, zeroStateContextRank, hdec, ?_⟩
    rfl
  have hno :
      Not (Nonempty (TrajectoryGodMoveBoundaryMinor enc T n)) := by
    dsimp [T]
    exact no_trajectoryMinor_of_zeroRankFaithfulObserver
      (enc := enc) M hchoose_pos
  exact hno (hextract T hfaithful)

/-- Therefore, if a SAT-deciding DTM exists, the present universal faithful
extraction target is impossible: it can choose a large positive binomial scale,
but the zero-rank faithful presentation has no live boundary minor there. -/
theorem not_universalFaithfulSATObserverGodMoveExtraction_of_zeroRankFaithfulDecider
    {enc : ThreeCNFEncoding} {M : TuringMachine.DTM}
    (hdec : DTMDecidesSATWithEncoding enc M) :
    Not (UniversalFaithfulSATObserverGodMoveExtraction enc) := by
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
    (not_TrajectorySATGodMoveExtractionAt_of_zeroRankFaithfulDecider
      (enc := enc) (M := M) hdec hchoose_pos) hextract_at

/-- Equivalently, the present faithful extraction target already implies that
no DTM in the repository's polynomial-time DTM model decides SAT.  This is the
whole P-vs-NP lower bound sitting inside the live-minor discharge socket. -/
theorem no_DTMDecidesSATWithEncoding_of_universalFaithfulExtraction
    (enc : ThreeCNFEncoding)
    (hextract : UniversalFaithfulSATObserverGodMoveExtraction enc) :
    Not (exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) := by
  intro hM
  rcases hM with ⟨M, hdec⟩
  exact
    (not_universalFaithfulSATObserverGodMoveExtraction_of_zeroRankFaithfulDecider
      (enc := enc) (M := M) hdec) hextract

/-- The PAC/N-frame live-minor discharge inherits the same obstruction, because
the available PAC/N-frame surface is already proved. -/
theorem not_FaithfulPACHolographyLiveMinorDischarge_of_zeroRankFaithfulDecider
    {enc : ThreeCNFEncoding} {M : TuringMachine.DTM}
    (hdec : DTMDecidesSATWithEncoding enc M) :
    Not (FaithfulPACHolographyLiveMinorDischarge enc) := by
  intro hdischarge
  exact
    (not_universalFaithfulSATObserverGodMoveExtraction_of_zeroRankFaithfulDecider
      (enc := enc) (M := M) hdec)
      (hdischarge faithful_PAC_holography_amplituhedron_nframe_surface)

/-- Any proof of the current live-minor discharge would already prove that no
repository-polynomial-time DTM decides SAT. -/
theorem no_DTMDecidesSATWithEncoding_of_FaithfulPACHolographyLiveMinorDischarge
    (enc : ThreeCNFEncoding)
    (hdischarge : FaithfulPACHolographyLiveMinorDischarge enc) :
    Not (exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) := by
  exact no_DTMDecidesSATWithEncoding_of_universalFaithfulExtraction enc
    (hdischarge faithful_PAC_holography_amplituhedron_nframe_surface)

#print axioms not_universalFaithfulSATObserverGodMoveExtraction_of_zeroRankFaithfulDecider
#print axioms no_DTMDecidesSATWithEncoding_of_universalFaithfulExtraction
#print axioms not_FaithfulPACHolographyLiveMinorDischarge_of_zeroRankFaithfulDecider
#print axioms no_DTMDecidesSATWithEncoding_of_FaithfulPACHolographyLiveMinorDischarge

end PallLean.Paper93.DeepMath.PathB
