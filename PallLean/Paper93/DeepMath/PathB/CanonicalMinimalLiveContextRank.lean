import PallLean.Paper93.DeepMath.PathB.ObserverTrajectoryDCEW

/-!
# Canonical minimal live-context rank

This file tests the paper-faithful positive pivot suggested by the dynamic CEW
correction:

* no static SPDP rank as the main invariant;
* no observer-supplied `Nat -> Nat` rank bookkeeping;
* no saturated rule that assigns binomial rank to SAT by definition.

The invariant below is canonical and local.  At a live input it counts the
semantic SAT continuations in the radius-one N-frame neighborhood: the current
input and all one-bit local moves.  This is the narrowest direct formalization
of "minimal live local context" available from the repository's current
observer semantics.

The test result is negative but sharp.  The invariant is canonical and has the
right P-side behavior (linear local context), but precisely because it is only
radius-one local it cannot carry the binomial-size God-Move boundary minor.
Consequently the corresponding universal extraction theorem is again
equivalent to the absence of a polynomial-time SAT-deciding DTM.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-! ## Radius-one semantic contexts -/

/-- A radius-one N-frame local move: either stay at the current input or flip
one input bit. -/
abbrev RadiusOneMove (n : Nat) := Option (Fin n)

/-- Apply a radius-one local move to an input. -/
def applyRadiusOneMove {n : Nat}
    (input : Fin n -> Bool) : RadiusOneMove n -> Fin n -> Bool
  | none => input
  | some i => fun j => if j = i then Bool.not (input j) else input j

/-- A concrete input encodes a satisfiable SAT instance. -/
def InputEncodesSatisfiable
    (enc : ThreeCNFEncoding) {n : Nat} (input : Fin n -> Bool) : Prop :=
  exists φ : ThreeCNF, enc.Encodes input φ /\ φ.IsSatisfiable

/-- Canonical minimal live-context rank.

This is not observer supplied.  It is the number of radius-one local moves whose
semantic continuation is a satisfiable encoded formula. -/
noncomputable def canonicalMinimalLiveContextRank
    (enc : ThreeCNFEncoding) (n : Nat) (input : Fin n -> Bool) : Nat := by
  classical
  exact ((Finset.univ : Finset (RadiusOneMove n)).filter
    (fun move => InputEncodesSatisfiable enc
      (applyRadiusOneMove input move))).card

/-- The local move type has linear cardinality. -/
theorem radiusOneMove_card (n : Nat) :
    Fintype.card (RadiusOneMove n) = n + 1 := by
  simp [RadiusOneMove]

/-- The canonical minimal live-context rank is bounded by the number of local
radius-one moves. -/
theorem canonicalMinimalLiveContextRank_le_radiusOneMove_card
    (enc : ThreeCNFEncoding) (n : Nat) (input : Fin n -> Bool) :
    canonicalMinimalLiveContextRank enc n input <=
      Fintype.card (RadiusOneMove n) := by
  classical
  unfold canonicalMinimalLiveContextRank
  exact Finset.card_filter_le
    (s := (Finset.univ : Finset (RadiusOneMove n)))
    (p := fun move => InputEncodesSatisfiable enc
      (applyRadiusOneMove input move))

/-- The local move bound is at most quadratic once `n >= 2`.  This lets the
existing binomial arithmetic gap rule out binomial live minors. -/
theorem radiusOneMove_card_le_square {n : Nat} (hn : 2 <= n) :
    Fintype.card (RadiusOneMove n) <= n ^ 2 := by
  have hone : 1 <= n := le_trans (by norm_num : 1 <= 2) hn
  have hleft : n + 1 <= n + n := Nat.add_le_add_left hone n
  have hright : n + n <= n * n := by
    calc
      n + n = 2 * n := by rw [two_mul]
      _ <= n * n := Nat.mul_le_mul_right n hn
  calc
    Fintype.card (RadiusOneMove n) = n + 1 := radiusOneMove_card n
    _ <= n + n := hleft
    _ <= n * n := hright
    _ = n ^ 2 := by rw [pow_two]

/-! ## Canonical minimal observers -/

/-- A canonical minimal live-context observer.

The observer has no rank field.  The live rank is forced by the canonical
radius-one semantic context above. -/
structure CanonicalMinimalNFrameObserver
    (enc : ThreeCNFEncoding) where
  M : TuringMachine.DTM
  decides : DTMDecidesSATWithEncoding enc M

/-- Forget a canonical minimal observer to a trajectory observer.

The width is the radius-one local-context cardinality, hence linear in the
input length. -/
noncomputable def CanonicalMinimalNFrameObserver.toTrajectory
    {enc : ThreeCNFEncoding}
    (O : CanonicalMinimalNFrameObserver enc) :
    TrajectoryObserverMachine where
  width := fun n => Fintype.card (RadiusOneMove n)
  acceptsInput := fun n input =>
    exists hn : n >= 1, TuringMachine.accepts O.M n hn input
  stateCode := fun n input t =>
    if hn : n >= 1 then
      (TuringMachine.run O.M n t
        (TuringMachine.initialConfig O.M n hn input)).state.val
    else
      0
  liveBoundaryRank := fun n input _ =>
    canonicalMinimalLiveContextRank enc n input
  liveBoundaryRank_le_width := by
    intro n input t
    exact canonicalMinimalLiveContextRank_le_radiusOneMove_card enc n input

/-- The canonical minimal observer width is the radius-one local move count. -/
theorem CanonicalMinimalNFrameObserver.toTrajectory_width
    {enc : ThreeCNFEncoding}
    (O : CanonicalMinimalNFrameObserver enc) (n : Nat) :
    O.toTrajectory.width n = Fintype.card (RadiusOneMove n) := by
  rfl

/-! ## Extraction target and collapse test -/

/-- Fixed-length live-minor extraction for canonical minimal observers. -/
def CanonicalMinimalLiveContextExtractionAt
    (enc : ThreeCNFEncoding) (n : Nat) : Prop :=
  forall O : CanonicalMinimalNFrameObserver enc,
    Nonempty (TrajectoryGodMoveBoundaryMinor enc O.toTrajectory n)

/-- Universal exponent-parametric extraction target for the canonical minimal
live-context invariant. -/
def UniversalCanonicalMinimalLiveContextExtraction
    (enc : ThreeCNFEncoding) : Prop :=
  forall c : Nat, exists n : Nat,
    n >= 2 ^ 20 /\
    4 * (c + 1) <= Nat.log 2 n /\
    CanonicalMinimalLiveContextExtractionAt enc n

/-- At paper scale, the binomial boundary is larger than any radius-one local
context. -/
theorem radiusOneMove_card_lt_boundary_of_scale
    {n : Nat} (hn20 : n >= 2 ^ 20)
    (hlog : 4 * (2 + 1) <= Nat.log 2 n) :
    Fintype.card (RadiusOneMove n) <
      Nat.choose (n / 3) (Nat.log 2 n) := by
  have hn2 : 2 <= n :=
    le_trans (by norm_num : 2 <= 2 ^ 20) hn20
  have hcard_sq :
      Fintype.card (RadiusOneMove n) <= n ^ 2 :=
    radiusOneMove_card_le_square hn2
  have hgap :
      n ^ 2 < Nat.choose (n / 3) (Nat.log 2 n) :=
    arithmetic_gap_for_exponent 2 n hn20 hlog
  exact lt_of_le_of_lt hcard_sq hgap

/-- A binomial-scale trajectory minor cannot fit inside a radius-one canonical
minimal observer at lengths where the boundary exceeds the local move count. -/
theorem no_trajectoryMinor_of_canonicalMinimal_boundary_gap
    {enc : ThreeCNFEncoding}
    (O : CanonicalMinimalNFrameObserver enc) {n : Nat}
    (hgap :
      Fintype.card (RadiusOneMove n) <
        Nat.choose (n / 3) (Nat.log 2 n)) :
    Not (Nonempty (TrajectoryGodMoveBoundaryMinor enc O.toTrajectory n)) := by
  intro hminor
  rcases hminor with ⟨minor⟩
  have hwidth :
      Nat.choose (n / 3) (Nat.log 2 n) <= O.toTrajectory.width n :=
    observer_width_lower_of_trajectory_minor minor
  have hboundary :
      Nat.choose (n / 3) (Nat.log 2 n) <=
        Fintype.card (RadiusOneMove n) := by
    simpa [CanonicalMinimalNFrameObserver.toTrajectory] using hwidth
  exact (not_le_of_gt hgap) hboundary

/-- Fixed-length canonical minimal extraction is false for any existing
canonical minimal observer once the binomial boundary exceeds the local context
cardinality. -/
theorem not_canonicalMinimalLiveContextExtractionAt_of_boundary_gap
    {enc : ThreeCNFEncoding}
    (O : CanonicalMinimalNFrameObserver enc) {n : Nat}
    (hgap :
      Fintype.card (RadiusOneMove n) <
        Nat.choose (n / 3) (Nat.log 2 n)) :
    Not (CanonicalMinimalLiveContextExtractionAt enc n) := by
  intro hextract
  exact no_trajectoryMinor_of_canonicalMinimal_boundary_gap
    O hgap (hextract O)

/-- If a SAT-deciding DTM exists, the canonical minimal extraction theorem is
impossible.  The obstruction is no longer arbitrary zero bookkeeping; it is the
linear size of radius-one live semantic context itself. -/
theorem not_universalCanonicalMinimalLiveContextExtraction_of_decider
    {enc : ThreeCNFEncoding}
    (hdec : exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) :
    Not (UniversalCanonicalMinimalLiveContextExtraction enc) := by
  intro hextract
  rcases hdec with ⟨M, hMdec⟩
  let O : CanonicalMinimalNFrameObserver enc := ⟨M, hMdec⟩
  rcases hextract 2 with ⟨n, hn20, hlog, hextract_at⟩
  exact
    (not_canonicalMinimalLiveContextExtractionAt_of_boundary_gap
      O (radiusOneMove_card_lt_boundary_of_scale hn20 hlog))
      hextract_at

/-- Conversely, if no DTM decides SAT under the encoding, the canonical minimal
extraction target is vacuous. -/
theorem universalCanonicalMinimalLiveContextExtraction_of_no_decider
    (enc : ThreeCNFEncoding)
    (hno : Not (exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M)) :
    UniversalCanonicalMinimalLiveContextExtraction enc := by
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
  · intro O
    exact False.elim (hno ⟨O.M, O.decides⟩)

/-- Exact status of the radius-one canonical minimal live-context pivot.

It is canonical and P-side small, but that smallness prevents it from carrying
the paper's binomial God-Move minor.  Therefore its universal extraction
theorem is again exactly the no-SAT-decider theorem in this DTM model. -/
theorem universalCanonicalMinimalLiveContextExtraction_iff_no_decider
    (enc : ThreeCNFEncoding) :
    UniversalCanonicalMinimalLiveContextExtraction enc ↔
      Not (exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) := by
  constructor
  · intro hextract hdec
    exact
      (not_universalCanonicalMinimalLiveContextExtraction_of_decider
        (enc := enc) hdec)
        hextract
  · exact universalCanonicalMinimalLiveContextExtraction_of_no_decider enc

/-! ## Kernel-only axiom trace -/

#print axioms canonicalMinimalLiveContextRank_le_radiusOneMove_card
#print axioms radiusOneMove_card_lt_boundary_of_scale
#print axioms not_universalCanonicalMinimalLiveContextExtraction_of_decider
#print axioms universalCanonicalMinimalLiveContextExtraction_of_no_decider
#print axioms universalCanonicalMinimalLiveContextExtraction_iff_no_decider

end PallLean.Paper93.DeepMath.PathB
