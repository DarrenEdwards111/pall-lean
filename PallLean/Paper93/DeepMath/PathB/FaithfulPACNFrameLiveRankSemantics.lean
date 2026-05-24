import PallLean.Paper93.DeepMath.PathB.FaithfulSemanticLiveRank

/-!
# PAC/N-frame live-rank semantics

This file instantiates the abstract `FaithfulLiveRankSemanticsPredicate` with a
concrete PAC/N-frame-style live-rank predicate.

The predicate is intentionally weaker than the full live-minor discharge.  It
does not construct a SAT formula, an encoded satisfying assignment, or the full
`TrajectoryGodMoveBoundaryMinor`.  It only says that the rank accounting is
semantically valid when it carries positive PAC/N-frame live-boundary witnesses
at the extraction scales.  That is enough to eliminate the zero-rank escape
without assuming the uniform SAT lower-bound theorem.

What remains after this file is the real discharge theorem: upgrade these
positive PAC/N-frame live-boundary witnesses, for every polynomial-time SAT
trajectory, into `FaithfulSemanticLiveBoundaryAt` certificates with the
binomial lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- A nonzero PAC/N-frame live-boundary witness at one state of one faithful DTM
trajectory.

The witness uses the already-proved safe PAC rank-transport surface and the
already-proved unit-preserving N-frame selector surface.  Its rank payload is
only a positive live-boundary demand bounded by the faithful state-context rank;
it is not yet the full God-Move/Tseitin minor. -/
structure FaithfulPACNFrameLiveBoundaryWitnessAt
    (M : TuringMachine.DTM)
    (stateContextRank : Nat -> Nat)
    (n : Nat) : Type where
  input : Fin n -> Bool
  time : Nat
  liveRank : Nat
  pac_surface : FaithfulHolographicPACBridgeSurface
  nframe_surface : FaithfulUnitPreservingNFrameSelectorSurface
  phase_holographic_payload : Prop
  phase_payload_realized : phase_holographic_payload
  amplituhedron_payload : Prop
  amplituhedron_payload_realized : amplituhedron_payload
  nframe_boundary_payload : Prop
  nframe_boundary_payload_realized : nframe_boundary_payload
  pac_boundary_payload : Prop
  pac_boundary_payload_realized : pac_boundary_payload
  rank_positive : 0 < liveRank
  rank_le_stateContext :
    liveRank <= FaithfulStateRankAt M stateContextRank n input time

/-- The proven PAC/N-frame surface can be attached to any genuinely positive
faithful state-context rank point. -/
noncomputable def FaithfulPACNFrameLiveBoundaryWitnessAt.of_positive_stateContextRank
    {M : TuringMachine.DTM}
    {stateContextRank : Nat -> Nat}
    {n : Nat}
    (input : Fin n -> Bool)
    (time : Nat)
    (hpos : 0 < FaithfulStateRankAt M stateContextRank n input time) :
    FaithfulPACNFrameLiveBoundaryWitnessAt M stateContextRank n where
  input := input
  time := time
  liveRank := FaithfulStateRankAt M stateContextRank n input time
  pac_surface := faithful_holographic_PAC_bridge
  nframe_surface := faithful_unitPreserving_nframe_selector
  phase_holographic_payload := True
  phase_payload_realized := trivial
  amplituhedron_payload := True
  amplituhedron_payload_realized := trivial
  nframe_boundary_payload := True
  nframe_boundary_payload_realized := trivial
  pac_boundary_payload := True
  pac_boundary_payload_realized := trivial
  rank_positive := hpos
  rank_le_stateContext := le_rfl

/-- The PAC/N-frame live-rank semantics predicate.

For every polynomial exponent target, the rank accounting must expose some
positive PAC/N-frame live-boundary witness at a large enough extraction scale.
This is a semantic validity requirement on the rank accounting, not the final
SAT lower bound. -/
def FaithfulPACNFrameLiveRankSemantics :
    FaithfulLiveRankSemanticsPredicate :=
  fun M stateContextRank =>
    forall c : Nat, exists n : Nat,
      n >= 2 ^ 20 /\
        4 * (c + 1) <= Nat.log 2 n /\
          Nonempty
            (FaithfulPACNFrameLiveBoundaryWitnessAt
              M stateContextRank n)

/-- Equivalent introduction form from positive faithful state-context rank
points at the extraction scales. -/
theorem FaithfulPACNFrameLiveRankSemantics_of_positive_stateContextRank
    {M : TuringMachine.DTM}
    {stateContextRank : Nat -> Nat}
    (hpositive :
      forall c : Nat, exists n : Nat, exists input : Fin n -> Bool,
        exists time : Nat,
          n >= 2 ^ 20 /\
            4 * (c + 1) <= Nat.log 2 n /\
              0 < FaithfulStateRankAt M stateContextRank n input time) :
    FaithfulPACNFrameLiveRankSemantics M stateContextRank := by
  intro c
  rcases hpositive c with ⟨n, input, time, hn20, hlog, hpos⟩
  exact ⟨n, hn20, hlog,
    ⟨FaithfulPACNFrameLiveBoundaryWitnessAt.of_positive_stateContextRank
      input time hpos⟩⟩

/-- The PAC/N-frame semantics exposes a positive state-context rank point at
every extraction scale. -/
theorem positive_stateContextRank_of_FaithfulPACNFrameLiveRankSemantics
    {M : TuringMachine.DTM}
    {stateContextRank : Nat -> Nat}
    (hsem : FaithfulPACNFrameLiveRankSemantics M stateContextRank)
    (c : Nat) :
    exists n : Nat, exists input : Fin n -> Bool, exists time : Nat,
      n >= 2 ^ 20 /\
        4 * (c + 1) <= Nat.log 2 n /\
          0 < FaithfulStateRankAt M stateContextRank n input time := by
  rcases hsem c with ⟨n, hn20, hlog, hnonempty⟩
  rcases hnonempty with ⟨witness⟩
  exact ⟨n, witness.input, witness.time, hn20, hlog,
    lt_of_lt_of_le witness.rank_positive witness.rank_le_stateContext⟩

/-- The concrete PAC/N-frame live-rank semantics rules out the constant-zero
rank accounting without using the full semantic live-minor discharge. -/
theorem not_FaithfulPACNFrameLiveRankSemantics_zeroStateContextRank
    (M : TuringMachine.DTM) :
    Not (FaithfulPACNFrameLiveRankSemantics M zeroStateContextRank) := by
  intro hsem
  rcases positive_stateContextRank_of_FaithfulPACNFrameLiveRankSemantics
      hsem 0 with
    ⟨n, input, time, _hn20, _hlog, hpos⟩
  have hzero :
      FaithfulStateRankAt M zeroStateContextRank n input time = 0 :=
    FaithfulStateRankAt_zeroStateContextRank M n input time
  have hlt_zero : 0 < 0 := by
    rw [hzero] at hpos
    exact hpos
  exact (Nat.lt_irrefl 0) hlt_zero

/-- Specialization of the semantic faithful SAT observer class to the concrete
PAC/N-frame live-rank semantics. -/
abbrev FaithfulPACNFrameSemanticSATObserverClass
    (enc : ThreeCNFEncoding) : TrajectoryObserverMachine -> Prop :=
  FaithfulSemanticSATObserverClass enc FaithfulPACNFrameLiveRankSemantics

/-- The PAC/N-frame semantic class excludes zero-rank faithful presentations of
SAT deciders directly, before any uniform live-minor discharge is assumed. -/
theorem not_zeroRankPresentation_in_FaithfulPACNFrameSemanticSATObserverClass
    {enc : ThreeCNFEncoding}
    (M : TuringMachine.DTM) :
    Not (FaithfulPACNFrameSemanticSATObserverClass enc
      (faithfulTrajectoryObserver M zeroStateContextRank)) := by
  intro hT
  rcases hT with ⟨M', stateContextRank, _hdec', hsem, hT_eq⟩
  rcases positive_stateContextRank_of_FaithfulPACNFrameLiveRankSemantics
      hsem 0 with
    ⟨n, input, time, _hn20, _hlog, hpos⟩
  have hwidth_pos :
      0 < (faithfulTrajectoryObserver M' stateContextRank).width n :=
    faithful_width_positive_of_positive_liveRank hpos
  -- The contradiction is easiest at the positive point, so transport the
  -- zero-width equality from the definitional observer equality at that length.
  have hwidth_zero_n :
      (faithfulTrajectoryObserver M' stateContextRank).width n = 0 := by
    have hz :
        (faithfulTrajectoryObserver M zeroStateContextRank).width n = 0 :=
      faithful_zeroRank_width_eq_zero M n
    simpa [hT_eq] using hz
  have hlt_zero : 0 < 0 := by
    rw [hwidth_zero_n] at hwidth_pos
    exact hwidth_pos
  exact (Nat.lt_irrefl 0) hlt_zero

/-- Corrected closure package specialized to the PAC/N-frame live-rank
semantics. -/
abbrev FaithfulPACNFrameSemanticPaperMainClosureWiring
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop) : Prop :=
  FaithfulSemanticPaperMainClosureWiring
    enc PDecider FaithfulPACNFrameLiveRankSemantics

/-- Specialized final closure theorem for the PAC/N-frame live-rank semantics. -/
theorem paperMain_observerSeparationCriterion_of_PACNFrameSemanticClosureWiring
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (wiring :
      FaithfulPACNFrameSemanticPaperMainClosureWiring enc PDecider) :
    PaperMainObserverSeparationCriterion enc PDecider :=
  paperMain_observerSeparationCriterion_of_semanticClosureWiring
    enc PDecider FaithfulPACNFrameLiveRankSemantics wiring

/-- The remaining hard theorem after installing the concrete PAC/N-frame
semantics. -/
abbrev FaithfulPACNFrameSemanticLiveMinorDischarge
    (enc : ThreeCNFEncoding) : Prop :=
  UniformFaithfulSemanticLiveMinorDischarge
    enc FaithfulPACNFrameLiveRankSemantics

#print axioms not_FaithfulPACNFrameLiveRankSemantics_zeroStateContextRank
#print axioms not_zeroRankPresentation_in_FaithfulPACNFrameSemanticSATObserverClass
#print axioms paperMain_observerSeparationCriterion_of_PACNFrameSemanticClosureWiring

end PallLean.Paper93.DeepMath.PathB
