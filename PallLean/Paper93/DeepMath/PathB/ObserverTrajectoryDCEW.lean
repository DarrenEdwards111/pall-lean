import PallLean.Paper93.DeepMath.PathB.ObserverGodMoveDCEWBridge

/-!
# Trajectory-level observer semantics for the DCEW route

This module strengthens the observer surface from an extensional accept/reject
object to an operational trajectory object.  The remaining lower-bound theorem
is now stated at the right level: a high-rank God-Move boundary minor must be
extracted from an actual live state of every DTM-backed SAT observer trajectory.

No SAT lower bound is assumed or proved here.  The file proves that the
trajectory extraction theorem would imply the dynamic SAT CEW lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- A trajectory observer carries the same input/output surface as
`ObserverMachine`, plus a live state code and live boundary rank at each time.

The live state is deliberately a `Nat`: this file only needs a stable handle
for trajectory-local predicates.  Concrete DTM/state encodings can refine this
later without changing the lower-bound bridge. -/
structure TrajectoryObserverMachine where
  width : DynamicCEW.ObserverWidth
  acceptsInput : (n : Nat) -> (Fin n -> Bool) -> Prop
  stateCode : (n : Nat) -> (Fin n -> Bool) -> Nat -> Nat
  liveBoundaryRank : (n : Nat) -> (Fin n -> Bool) -> Nat -> Nat
  liveBoundaryRank_le_width :
    forall (n : Nat) (input : Fin n -> Bool) (t : Nat),
      liveBoundaryRank n input t <= width n

/-- Forget a trajectory observer to the extensional observer surface. -/
def TrajectoryObserverMachine.toObserver
    (T : TrajectoryObserverMachine) : ObserverMachine where
  width := T.width
  acceptsInput := T.acceptsInput

/-- Width predicates induced by trajectory-observer classes. -/
def TrajectoryObserverWidths
    (Decides : TrajectoryObserverMachine -> Prop) :
    DynamicCEW.ObserverWidth -> Prop :=
  fun w => exists T : TrajectoryObserverMachine, Decides T /\ T.width = w

/-- A DTM realizes a trajectory observer's input/output behavior and state code.

This is the operational layer.  The observer may expose a richer boundary-rank
accounting than the DTM state value alone, but its acceptance behavior and basic
state trace must be backed by an actual DTM run. -/
def DTMRealizesTrajectoryObserver
    (M : TuringMachine.DTM) (T : TrajectoryObserverMachine) : Prop :=
  (forall {n : Nat} (hn : n >= 1) (input : Fin n -> Bool),
      T.acceptsInput n input <-> TuringMachine.accepts M n hn input) /\
  (forall {n : Nat} (hn : n >= 1) (input : Fin n -> Bool) (t : Nat),
      T.stateCode n input t =
        (TuringMachine.run M n t
          (TuringMachine.initialConfig M n hn input)).state.val)

/-- Operational SAT correctness for trajectory observers. -/
def OperationalTrajectoryObserverDecidesSAT
    (enc : ThreeCNFEncoding) (T : TrajectoryObserverMachine) : Prop :=
  exists M : TuringMachine.DTM,
    DTMDecidesSATWithEncoding enc M /\
      DTMRealizesTrajectoryObserver M T

/-- A DTM-backed trajectory observer forgets to a DTM-backed observer. -/
theorem OperationalObserverDecidesSAT_of_trajectory
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine}
    (hT : OperationalTrajectoryObserverDecidesSAT enc T) :
    OperationalObserverDecidesSAT enc T.toObserver := by
  rcases hT with ⟨M, hMdec, hrealizes⟩
  refine ⟨M, hMdec, ?_⟩
  intro n hn input
  exact hrealizes.1 hn input

/-- A trajectory-local God-Move / holographic boundary minor.

Unlike `GodMoveHolographicBoundaryMinor`, this object is tied to a concrete
encoded SAT instance, input, live time, and state code.  The final two rank
fields are exactly what the DCEW bridge consumes. -/
structure TrajectoryGodMoveBoundaryMinor
    (enc : ThreeCNFEncoding) (T : TrajectoryObserverMachine) (n : Nat) where
  input : Fin n -> Bool
  formula : ThreeCNF
  encoded : enc.Encodes input formula
  formula_satisfiable : formula.IsSatisfiable
  time : Nat
  state : Nat
  state_matches : state = T.stateCode n input time
  liveRank : Nat
  phase_holographic_payload : Prop
  phase_payload_realized : phase_holographic_payload
  godmove_amplituhedron_payload : Prop
  godmove_payload_realized : godmove_amplituhedron_payload
  rank_lower :
    Nat.choose (n / 3) (Nat.log 2 n) <= liveRank
  rank_le_boundary :
    liveRank <= T.liveBoundaryRank n input time

/-- A trajectory-local minor forces the observer width at that length. -/
theorem observer_width_lower_of_trajectory_minor
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    (minor : TrajectoryGodMoveBoundaryMinor enc T n) :
    Nat.choose (n / 3) (Nat.log 2 n) <= T.width n :=
  le_trans minor.rank_lower
    (le_trans minor.rank_le_boundary
      (T.liveBoundaryRank_le_width n minor.input minor.time))

/-- Fixed-length trajectory extraction theorem. -/
def TrajectorySATGodMoveExtractionAt
    (enc : ThreeCNFEncoding)
    (Decides : TrajectoryObserverMachine -> Prop)
    (n : Nat) : Prop :=
  forall T : TrajectoryObserverMachine, Decides T ->
    Nonempty (TrajectoryGodMoveBoundaryMinor enc T n)

/-- Exponent-parametric trajectory extraction theorem.

This is the current sharp proof target: for every polynomial exponent, there is
a length at which every operational SAT trajectory exposes a high-rank live
God-Move boundary minor. -/
def UniversalTrajectorySATGodMoveExtraction
    (enc : ThreeCNFEncoding)
    (Decides : TrajectoryObserverMachine -> Prop) : Prop :=
  forall c : Nat, exists n : Nat,
    n >= 2 ^ 20 /\
    4 * (c + 1) <= Nat.log 2 n /\
    TrajectorySATGodMoveExtractionAt enc Decides n

/-- Operational version of the trajectory extraction target. -/
def UniversalOperationalTrajectorySATGodMoveExtraction
    (enc : ThreeCNFEncoding) : Prop :=
  UniversalTrajectorySATGodMoveExtraction enc
    (OperationalTrajectoryObserverDecidesSAT enc)

/-! ## Polynomial-time observer target

In this repository `TuringMachine.DTM` is already a polynomial-time machine:
`TuringMachine.accepts M n hn input` only ranges over
`TuringMachine.timeSteps M n = n ^ M.timeBound`.  So the operational
trajectory predicate below is the polynomial-time SAT-observer class.  The
remaining theorem is not a brute-force SAT statement; it is the genuine
poly-time observer lower bound.
-/

/-- Explicit alias for the polynomial-time operational trajectory class.

This is definitionally the same predicate as
`OperationalTrajectoryObserverDecidesSAT`, because `TuringMachine.DTM` already
carries a polynomial time-bound exponent. -/
def PolyTimeOperationalTrajectoryObserverDecidesSAT
    (enc : ThreeCNFEncoding) (T : TrajectoryObserverMachine) : Prop :=
  OperationalTrajectoryObserverDecidesSAT enc T

theorem PolyTimeOperationalTrajectoryObserverDecidesSAT_iff
    (enc : ThreeCNFEncoding) (T : TrajectoryObserverMachine) :
    PolyTimeOperationalTrajectoryObserverDecidesSAT enc T ↔
      OperationalTrajectoryObserverDecidesSAT enc T :=
  Iff.rfl

/-- A single trajectory observer has polynomial width with exponent `c`. -/
def TrajectoryObserverHasPolyWidthExponent
    (T : TrajectoryObserverMachine) (c : Nat) : Prop :=
  forall n : Nat, T.width n <= n ^ c

/-- A trajectory observer class contains a SAT-deciding observer of width
bounded by exponent `c`. -/
def TrajectoryObserverSATPolyWidthAtMost
    (Decides : TrajectoryObserverMachine -> Prop) (c : Nat) : Prop :=
  exists T : TrajectoryObserverMachine,
    Decides T /\ TrajectoryObserverHasPolyWidthExponent T c

/-- Honest socket for any future PAC / holography / amplituhedron / Ramanujan /
N-frame package.

The field is deliberately the extraction theorem itself.  The surrounding
geometry only contributes to the P-vs-NP route once it proves this field for
all polynomial-time operational SAT observers. -/
structure NFramePACHolographyAmplituhedronRamanujanEngine
    (enc : ThreeCNFEncoding) : Prop where
  polytime_observer_extraction :
    UniversalOperationalTrajectorySATGodMoveExtraction enc

/-- At one length, trajectory extraction rules out that polynomial DCEW bound. -/
theorem not_DCEWatMost_at_exponent_of_trajectoryExtractionAt
    (enc : ThreeCNFEncoding)
    (Decides : TrajectoryObserverMachine -> Prop)
    (c n : Nat)
    (hn20 : n >= 2 ^ 20)
    (hlog : 4 * (c + 1) <= Nat.log 2 n)
    (hextract : TrajectorySATGodMoveExtractionAt enc Decides n) :
    Not (DynamicCEW.DCEWatMost (TrajectoryObserverWidths Decides) n (n ^ c)) := by
  intro hcew
  rcases hcew with ⟨w, hw_decides, hw_bound⟩
  rcases hw_decides with ⟨T, hdec, hwidth_eq⟩
  rcases hextract T hdec with ⟨minor⟩
  have hminor_width :
      Nat.choose (n / 3) (Nat.log 2 n) <= T.width n :=
    observer_width_lower_of_trajectory_minor minor
  have hminor_w :
      Nat.choose (n / 3) (Nat.log 2 n) <= w n := by
    simpa [hwidth_eq] using hminor_width
  have hupper :
      Nat.choose (n / 3) (Nat.log 2 n) <= n ^ c :=
    le_trans hminor_w hw_bound
  exact (not_le_of_gt (arithmetic_gap_for_exponent c n hn20 hlog)) hupper

/-- The trajectory extraction theorem implies the dynamic SAT CEW lower bound
for the corresponding trajectory-observer class. -/
theorem NP_side_lower_bound_of_universalTrajectorySATGodMoveExtraction
    (enc : ThreeCNFEncoding)
    (Decides : TrajectoryObserverMachine -> Prop)
    (hextract : UniversalTrajectorySATGodMoveExtraction enc Decides) :
    DynamicCEW.NP_side_lower_bound (TrajectoryObserverWidths Decides) := by
  intro c
  rcases hextract c with ⟨n, hn20, hlog, hextract_at⟩
  exact ⟨n,
    not_DCEWatMost_at_exponent_of_trajectoryExtractionAt
      enc Decides c n hn20 hlog hextract_at⟩

/-- Operational trajectory SAT version of the DCEW lower-bound bridge. -/
theorem NP_side_lower_bound_of_universalOperationalTrajectorySATGodMoveExtraction
    (enc : ThreeCNFEncoding)
    (hextract : UniversalOperationalTrajectorySATGodMoveExtraction enc) :
    DynamicCEW.NP_side_lower_bound
      (TrajectoryObserverWidths (OperationalTrajectoryObserverDecidesSAT enc)) :=
  NP_side_lower_bound_of_universalTrajectorySATGodMoveExtraction
    enc (OperationalTrajectoryObserverDecidesSAT enc) hextract

/-- Universal trajectory extraction rules out any polynomial-width observer in
the same trajectory class. -/
theorem not_TrajectoryObserverSATPolyWidthAtMost_of_universalTrajectoryExtraction
    (enc : ThreeCNFEncoding)
    (Decides : TrajectoryObserverMachine -> Prop)
    (hextract : UniversalTrajectorySATGodMoveExtraction enc Decides)
    (c : Nat) :
    Not (TrajectoryObserverSATPolyWidthAtMost Decides c) := by
  intro hpoly
  rcases hpoly with ⟨T, hdec, hwidth⟩
  rcases hextract c with ⟨n, hn20, hlog, hextract_at⟩
  have hcew :
      DynamicCEW.DCEWatMost (TrajectoryObserverWidths Decides) n (n ^ c) := by
    refine ⟨T.width, ⟨T, hdec, rfl⟩, ?_⟩
    exact hwidth n
  exact
    (not_DCEWatMost_at_exponent_of_trajectoryExtractionAt
      enc Decides c n hn20 hlog hextract_at) hcew

/-- Operational polynomial-time version: the universal extraction theorem is
exactly strong enough to rule out polynomial-width SAT observers. -/
theorem not_polyWidthSATObserver_of_universalOperationalTrajectoryExtraction
    (enc : ThreeCNFEncoding)
    (hextract : UniversalOperationalTrajectorySATGodMoveExtraction enc)
    (c : Nat) :
    Not (TrajectoryObserverSATPolyWidthAtMost
      (PolyTimeOperationalTrajectoryObserverDecidesSAT enc) c) := by
  simpa [UniversalOperationalTrajectorySATGodMoveExtraction,
    PolyTimeOperationalTrajectoryObserverDecidesSAT] using
    (not_TrajectoryObserverSATPolyWidthAtMost_of_universalTrajectoryExtraction
      enc (OperationalTrajectoryObserverDecidesSAT enc) hextract c)

/-- The named geometric engine closes the observer-width lower bound exactly
when it supplies the universal polynomial-time trajectory extraction theorem. -/
theorem NP_side_lower_bound_of_NFramePACHolographyAmplituhedronRamanujanEngine
    (enc : ThreeCNFEncoding)
    (engine : NFramePACHolographyAmplituhedronRamanujanEngine enc) :
    DynamicCEW.NP_side_lower_bound
      (TrajectoryObserverWidths
        (PolyTimeOperationalTrajectoryObserverDecidesSAT enc)) := by
  simpa [PolyTimeOperationalTrajectoryObserverDecidesSAT] using
    (NP_side_lower_bound_of_universalOperationalTrajectorySATGodMoveExtraction
      enc engine.polytime_observer_extraction)

/-- Paper-scale fixed-exponent version for trajectory observers. -/
theorem not_DCEWatMost_at_paperScale_200_of_trajectoryExtractionAt
    (enc : ThreeCNFEncoding)
    (Decides : TrajectoryObserverMachine -> Prop)
    (n : Nat)
    (hn804 : n >= 2 ^ 804)
    (hextract : TrajectorySATGodMoveExtractionAt enc Decides n) :
    Not (DynamicCEW.DCEWatMost (TrajectoryObserverWidths Decides) n (n ^ 200)) := by
  have hn20 : n >= 2 ^ 20 := by
    exact le_trans
      (Nat.pow_le_pow_right (by norm_num : 1 <= 2) (by omega : 20 <= 804))
      hn804
  have hlog : 4 * (200 + 1) <= Nat.log 2 n := by
    have hlog804 : 804 <= Nat.log 2 n :=
      Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn804
    omega
  exact not_DCEWatMost_at_exponent_of_trajectoryExtractionAt
    enc Decides 200 n hn20 hlog hextract

#print axioms NP_side_lower_bound_of_universalOperationalTrajectorySATGodMoveExtraction
#print axioms not_DCEWatMost_at_paperScale_200_of_trajectoryExtractionAt

end PallLean.Paper93.DeepMath.PathB
