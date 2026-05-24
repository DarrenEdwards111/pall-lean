import PallLean.Paper93.DeepMath.PathB.ObserverTrajectoryDCEW

/-!
# Canonical dynamic N-frame invariant test

This file tests the positive pivot where the live N-frame rank is no longer an
observer-supplied bookkeeping function such as `Nat -> Nat`.

The rank below is canonical and function-intrinsic for SAT: it is computed from
the encoded formula semantics.  If the input encodes a satisfiable formula, the
rank is the binomial boundary scale; otherwise it is zero.

This deliberately removes the previous zero-rank-presentation obstruction.  The
resulting extraction theorem is provable from encoding completeness alone, not
from the nonexistence of SAT deciders.  The price is also formalized: the
induced trajectory width is binomial by construction, so this saturated semantic
rank is not yet a P-side CEW calibration.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-! ## A concrete satisfiable formula family -/

/-- The empty-clause 3-CNF with one variable. -/
def trivialSatisfiableThreeCNF : ThreeCNF where
  numVars := 1
  clauses := []

/-- The trivial formula has encoding size `1`. -/
theorem trivialSatisfiableThreeCNF_encodingSize :
    trivialSatisfiableThreeCNF.encodingSize = 1 := by
  rfl

/-- The trivial formula is satisfiable. -/
theorem trivialSatisfiableThreeCNF_satisfiable :
    trivialSatisfiableThreeCNF.IsSatisfiable := by
  refine ⟨fun _ => true, ?_⟩
  intro c hc
  cases hc

/-! ## Canonical SAT-semantic live rank -/

/-- At length `n`, there is an encoded satisfiable formula. -/
def EncodedSatisfiableAt (enc : ThreeCNFEncoding) (n : Nat) : Prop :=
  exists input : Fin n -> Bool,
    exists φ : ThreeCNF, enc.Encodes input φ /\ φ.IsSatisfiable

/-- Completeness of the encoding supplies encoded satisfiable formulas at every
positive length. -/
theorem encodedSatisfiableAt_of_one_le
    (enc : ThreeCNFEncoding) {n : Nat} (hn : 1 <= n) :
    EncodedSatisfiableAt enc n := by
  have hsize : trivialSatisfiableThreeCNF.encodingSize <= n := by
    simpa [trivialSatisfiableThreeCNF_encodingSize] using hn
  rcases enc.complete trivialSatisfiableThreeCNF n hsize with ⟨input, henc⟩
  exact ⟨input, trivialSatisfiableThreeCNF, henc,
    trivialSatisfiableThreeCNF_satisfiable⟩

/-- The saturated canonical SAT-semantic N-frame rank.

Unlike `stateActionRank : Nat -> Nat`, this is not supplied by the observer.
It is fixed by SAT semantics under the encoding. -/
noncomputable def canonicalSATSemanticActionRank
    (enc : ThreeCNFEncoding) (n : Nat) (input : Fin n -> Bool) : Nat := by
  classical
  exact if exists φ : ThreeCNF, enc.Encodes input φ /\ φ.IsSatisfiable then
    Nat.choose (n / 3) (Nat.log 2 n)
  else
    0

/-- The canonical rank is bounded by the binomial boundary scale. -/
theorem canonicalSATSemanticActionRank_le_boundary
    (enc : ThreeCNFEncoding) (n : Nat) (input : Fin n -> Bool) :
    canonicalSATSemanticActionRank enc n input <=
      Nat.choose (n / 3) (Nat.log 2 n) := by
  classical
  unfold canonicalSATSemanticActionRank
  split
  · rfl
  · exact Nat.zero_le _

/-- On an encoded satisfiable formula, the canonical rank is exactly the
binomial boundary scale. -/
theorem canonicalSATSemanticActionRank_eq_boundary_of_satisfiable
    {enc : ThreeCNFEncoding} {n : Nat} {input : Fin n -> Bool}
    {φ : ThreeCNF} (henc : enc.Encodes input φ) (hsat : φ.IsSatisfiable) :
    canonicalSATSemanticActionRank enc n input =
      Nat.choose (n / 3) (Nat.log 2 n) := by
  classical
  unfold canonicalSATSemanticActionRank
  rw [if_pos ⟨φ, henc, hsat⟩]

/-! ## Canonical observers -/

/-- A SAT observer whose live rank is forced by canonical SAT semantics.

There is no observer-provided rank field here.  The only operational data is a
DTM that decides SAT under the encoding. -/
structure CanonicalDynamicNFrameObserver
    (enc : ThreeCNFEncoding) where
  M : TuringMachine.DTM
  decides : DTMDecidesSATWithEncoding enc M

/-- The canonical observer as a trajectory observer.

The live boundary rank is the fixed semantic rank.  The width is therefore the
binomial boundary scale at each length, not a free accounting choice. -/
noncomputable def CanonicalDynamicNFrameObserver.toTrajectory
    {enc : ThreeCNFEncoding}
    (O : CanonicalDynamicNFrameObserver enc) :
    TrajectoryObserverMachine where
  width := fun n => Nat.choose (n / 3) (Nat.log 2 n)
  acceptsInput := fun n input =>
    exists hn : n >= 1, TuringMachine.accepts O.M n hn input
  stateCode := fun n input t =>
    if hn : n >= 1 then
      (TuringMachine.run O.M n t
        (TuringMachine.initialConfig O.M n hn input)).state.val
    else
      0
  liveBoundaryRank := fun n input _ =>
    canonicalSATSemanticActionRank enc n input
  liveBoundaryRank_le_width := by
    intro n input t
    exact canonicalSATSemanticActionRank_le_boundary enc n input

/-- The canonical trajectory width is exactly the binomial boundary scale. -/
theorem CanonicalDynamicNFrameObserver.toTrajectory_width
    {enc : ThreeCNFEncoding}
    (O : CanonicalDynamicNFrameObserver enc) (n : Nat) :
    O.toTrajectory.width n = Nat.choose (n / 3) (Nat.log 2 n) := by
  rfl

/-! ## Canonical live-minor extraction -/

/-- Fixed-length extraction target for canonical dynamic N-frame observers. -/
def CanonicalDynamicNFrameExtractionAt
    (enc : ThreeCNFEncoding) (n : Nat) : Prop :=
  forall O : CanonicalDynamicNFrameObserver enc,
    Nonempty (TrajectoryGodMoveBoundaryMinor enc O.toTrajectory n)

/-- Exponent-parametric canonical extraction target. -/
def UniversalCanonicalDynamicNFrameExtraction
    (enc : ThreeCNFEncoding) : Prop :=
  forall c : Nat, exists n : Nat,
    n >= 2 ^ 20 /\
    4 * (c + 1) <= Nat.log 2 n /\
    CanonicalDynamicNFrameExtractionAt enc n

/-- If there is any encoded satisfiable formula at length `n`, every canonical
observer has a live boundary minor at that length.

This is the positive test result: the extraction no longer needs a no-decider
hypothesis, because the binomial rank is forced by the semantic invariant. -/
theorem canonicalExtractionAt_of_encodedSatisfiableAt
    {enc : ThreeCNFEncoding} {n : Nat}
    (hinst : EncodedSatisfiableAt enc n) :
    CanonicalDynamicNFrameExtractionAt enc n := by
  intro O
  rcases hinst with ⟨input, φ, henc, hsat⟩
  refine ⟨{
    input := input
    formula := φ
    encoded := henc
    formula_satisfiable := hsat
    time := 0
    state := O.toTrajectory.stateCode n input 0
    state_matches := rfl
    liveRank := Nat.choose (n / 3) (Nat.log 2 n)
    phase_holographic_payload := True
    phase_payload_realized := trivial
    godmove_amplituhedron_payload := True
    godmove_payload_realized := trivial
    rank_lower := le_rfl
    rank_le_boundary := ?_
  }⟩
  change Nat.choose (n / 3) (Nat.log 2 n) <=
    canonicalSATSemanticActionRank enc n input
  rw [canonicalSATSemanticActionRank_eq_boundary_of_satisfiable henc hsat]

/-- Encoding completeness supplies canonical extraction at every positive
length. -/
theorem canonicalExtractionAt_of_one_le
    (enc : ThreeCNFEncoding) {n : Nat} (hn : 1 <= n) :
    CanonicalDynamicNFrameExtractionAt enc n :=
  canonicalExtractionAt_of_encodedSatisfiableAt
    (encodedSatisfiableAt_of_one_le enc hn)

/-- The canonical extraction theorem is unconditionally provable from the
encoding completeness field.

This shows that the canonical pivot avoids the previous vacuous equivalence to
`no SAT-deciding DTM`: it proves extraction even before discussing whether any
SAT decider exists. -/
theorem universalCanonicalDynamicNFrameExtraction
    (enc : ThreeCNFEncoding) :
    UniversalCanonicalDynamicNFrameExtraction enc := by
  intro c
  let k : Nat := Nat.max 20 (4 * (c + 1))
  let n : Nat := 2 ^ k
  refine ⟨n, ?_, ?_, ?_⟩
  · dsimp [n, k]
    exact Nat.pow_le_pow_right
      (by norm_num : 1 <= 2)
      (Nat.le_max_left 20 (4 * (c + 1)))
  · dsimp [n, k]
    have hpow :
        2 ^ (4 * (c + 1)) <= 2 ^ Nat.max 20 (4 * (c + 1)) :=
      Nat.pow_le_pow_right
        (by norm_num : 1 <= 2)
        (Nat.le_max_right 20 (4 * (c + 1)))
    exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow
  · apply canonicalExtractionAt_of_one_le
    dsimp [n, k]
    exact Nat.succ_le_of_lt (Nat.pow_pos (by norm_num : 0 < 2))

/-- Even under an explicit SAT-decider hypothesis, canonical extraction follows
from semantics.  This records that the new target does not collapse to the
previous no-decider equivalence by definition. -/
theorem universalCanonicalDynamicNFrameExtraction_of_decider
    {enc : ThreeCNFEncoding}
    (_hdec : exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) :
    UniversalCanonicalDynamicNFrameExtraction enc :=
  universalCanonicalDynamicNFrameExtraction enc

/-! ## The price: the saturated semantic rank is not a P-side calibration -/

/-- Any existing canonical SAT observer has non-polynomial canonical width:
for every polynomial exponent `c`, some length has boundary scale above `n^c`.

This is not a P-vs-NP proof.  It says the saturated semantic invariant already
contains the superpolynomial SAT boundary by definition, so it cannot serve as
the desired poly-on-P dynamic CEW measure without a new calibration theorem. -/
theorem not_polyWidth_of_canonicalDynamicNFrameObserver
    {enc : ThreeCNFEncoding}
    (O : CanonicalDynamicNFrameObserver enc) (c : Nat) :
    Not (TrajectoryObserverHasPolyWidthExponent O.toTrajectory c) := by
  intro hpoly
  let k : Nat := Nat.max 20 (4 * (c + 1))
  let n : Nat := 2 ^ k
  have hn20 : n >= 2 ^ 20 := by
    dsimp [n, k]
    exact Nat.pow_le_pow_right
      (by norm_num : 1 <= 2)
      (Nat.le_max_left 20 (4 * (c + 1)))
  have hlog : 4 * (c + 1) <= Nat.log 2 n := by
    dsimp [n, k]
    have hpow :
        2 ^ (4 * (c + 1)) <= 2 ^ Nat.max 20 (4 * (c + 1)) :=
      Nat.pow_le_pow_right
        (by norm_num : 1 <= 2)
        (Nat.le_max_right 20 (4 * (c + 1)))
    exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow
  have hgap :
      n ^ c < Nat.choose (n / 3) (Nat.log 2 n) :=
    arithmetic_gap_for_exponent c n hn20 hlog
  have hupper :
      Nat.choose (n / 3) (Nat.log 2 n) <= n ^ c := by
    simpa [CanonicalDynamicNFrameObserver.toTrajectory, n] using hpoly n
  exact (not_le_of_gt hgap) hupper

/-! ## Kernel-only axiom trace -/

#print axioms encodedSatisfiableAt_of_one_le
#print axioms canonicalExtractionAt_of_encodedSatisfiableAt
#print axioms universalCanonicalDynamicNFrameExtraction
#print axioms universalCanonicalDynamicNFrameExtraction_of_decider
#print axioms not_polyWidth_of_canonicalDynamicNFrameObserver

end PallLean.Paper93.DeepMath.PathB
