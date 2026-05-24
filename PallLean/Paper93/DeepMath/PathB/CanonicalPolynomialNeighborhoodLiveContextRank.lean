import PallLean.Paper93.DeepMath.PathB.ObserverTrajectoryDCEW

/-!
# Canonical polynomial-neighborhood live-context rank

This file tests the next paper-faithful dynamic CEW pivot.

The radius-one minimal context was canonical and P-side small, but too small to
carry the binomial God-Move minor.  The natural next move is to allow a larger
canonical local semantic neighborhood while keeping it polynomially bounded.

We formalize the full fixed-polynomial version: for an exponent `d`, a canonical
neighborhood supplies exactly `n^d` semantic moves at length `n`.  The live rank
is computed from SAT semantics over those moves; it is not supplied by the
observer and it is not the saturated "SAT implies binomial" rank.

The result is the generic collapse theorem: any fixed-polynomial canonical
neighborhood has live rank at most `n^d`, so the paper's binomial extraction
target is again equivalent to the absence of a polynomial-time SAT-deciding DTM.
Thus "larger but still polynomial" neighborhoods do not escape the boundary
minor obstruction.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-! ## Polynomially bounded canonical semantic neighborhoods -/

/-- A concrete input encodes a satisfiable SAT instance. -/
def PolyNeighborhoodInputEncodesSatisfiable
    (enc : ThreeCNFEncoding) {n : Nat} (input : Fin n -> Bool) : Prop :=
  exists φ : ThreeCNF, enc.Encodes input φ /\ φ.IsSatisfiable

/-- A fixed-polynomial canonical semantic neighborhood.

At length `n`, the neighborhood has exactly `n^d` canonical moves.  The move map
is independent of the observer and can represent whatever paper-faithful
N-frame/PAC/holographic local continuation rule one wants to test, provided it
remains fixed-polynomial in size. -/
structure CanonicalPolynomialNeighborhood (d : Nat) where
  applyMove :
    {n : Nat} -> Fin (n ^ d) -> (Fin n -> Bool) -> Fin n -> Bool

/-- The semantic live-context rank induced by a canonical polynomial
neighborhood.

This is canonical once the neighborhood rule is fixed.  It is computed from SAT
semantics over the neighborhood, not supplied by an observer. -/
noncomputable def canonicalPolynomialNeighborhoodLiveContextRank
    (enc : ThreeCNFEncoding) {d : Nat}
    (N : CanonicalPolynomialNeighborhood d)
    (n : Nat) (input : Fin n -> Bool) : Nat := by
  classical
  exact ((Finset.univ : Finset (Fin (n ^ d))).filter
    (fun move => PolyNeighborhoodInputEncodesSatisfiable enc
      (N.applyMove move input))).card

/-- A fixed-polynomial canonical neighborhood has polynomial live rank. -/
theorem canonicalPolynomialNeighborhoodLiveContextRank_le_poly
    (enc : ThreeCNFEncoding) {d : Nat}
    (N : CanonicalPolynomialNeighborhood d)
    (n : Nat) (input : Fin n -> Bool) :
    canonicalPolynomialNeighborhoodLiveContextRank enc N n input <= n ^ d := by
  classical
  unfold canonicalPolynomialNeighborhoodLiveContextRank
  have hcard :
      ((Finset.univ : Finset (Fin (n ^ d))).filter
        (fun move => PolyNeighborhoodInputEncodesSatisfiable enc
          (N.applyMove move input))).card <=
        (Finset.univ : Finset (Fin (n ^ d))).card :=
    Finset.card_filter_le
      (s := (Finset.univ : Finset (Fin (n ^ d))))
      (p := fun move => PolyNeighborhoodInputEncodesSatisfiable enc
        (N.applyMove move input))
  simpa using hcard

/-! ## Canonical polynomial-neighborhood observers -/

/-- A SAT observer whose live rank is forced by a canonical polynomial semantic
neighborhood. -/
structure CanonicalPolynomialNeighborhoodObserver
    (enc : ThreeCNFEncoding) {d : Nat}
    (N : CanonicalPolynomialNeighborhood d) where
  M : TuringMachine.DTM
  decides : DTMDecidesSATWithEncoding enc M

/-- Forget a canonical polynomial-neighborhood observer to a trajectory
observer.

The live boundary rank is computed semantically from `N`; the width is the
polynomial neighborhood size `n^d`. -/
noncomputable def CanonicalPolynomialNeighborhoodObserver.toTrajectory
    {enc : ThreeCNFEncoding} {d : Nat}
    {N : CanonicalPolynomialNeighborhood d}
    (O : CanonicalPolynomialNeighborhoodObserver enc N) :
    TrajectoryObserverMachine where
  width := fun n => n ^ d
  acceptsInput := fun n input =>
    exists hn : n >= 1, TuringMachine.accepts O.M n hn input
  stateCode := fun n input t =>
    if hn : n >= 1 then
      (TuringMachine.run O.M n t
        (TuringMachine.initialConfig O.M n hn input)).state.val
    else
      0
  liveBoundaryRank := fun n input _ =>
    canonicalPolynomialNeighborhoodLiveContextRank enc N n input
  liveBoundaryRank_le_width := by
    intro n input t
    exact canonicalPolynomialNeighborhoodLiveContextRank_le_poly enc N n input

/-- The canonical polynomial-neighborhood observer has width exactly `n^d`. -/
theorem CanonicalPolynomialNeighborhoodObserver.toTrajectory_width
    {enc : ThreeCNFEncoding} {d : Nat}
    {N : CanonicalPolynomialNeighborhood d}
    (O : CanonicalPolynomialNeighborhoodObserver enc N) (n : Nat) :
    O.toTrajectory.width n = n ^ d := by
  rfl

/-! ## Extraction target and generic collapse -/

/-- Fixed-length live-minor extraction for a fixed canonical polynomial
neighborhood. -/
def CanonicalPolynomialNeighborhoodExtractionAt
    (enc : ThreeCNFEncoding) {d : Nat}
    (N : CanonicalPolynomialNeighborhood d) (n : Nat) : Prop :=
  forall O : CanonicalPolynomialNeighborhoodObserver enc N,
    Nonempty (TrajectoryGodMoveBoundaryMinor enc O.toTrajectory n)

/-- Universal exponent-parametric extraction for a fixed canonical polynomial
neighborhood. -/
def UniversalCanonicalPolynomialNeighborhoodExtraction
    (enc : ThreeCNFEncoding) {d : Nat}
    (N : CanonicalPolynomialNeighborhood d) : Prop :=
  forall c : Nat, exists n : Nat,
    n >= 2 ^ 20 /\
    4 * (c + 1) <= Nat.log 2 n /\
    CanonicalPolynomialNeighborhoodExtractionAt enc N n

/-- A binomial-scale trajectory minor cannot fit inside a fixed-polynomial
canonical neighborhood at a length where the binomial boundary exceeds `n^d`. -/
theorem no_trajectoryMinor_of_canonicalPolynomialNeighborhood_gap
    {enc : ThreeCNFEncoding} {d : Nat}
    {N : CanonicalPolynomialNeighborhood d}
    (O : CanonicalPolynomialNeighborhoodObserver enc N) {n : Nat}
    (hgap : n ^ d < Nat.choose (n / 3) (Nat.log 2 n)) :
    Not (Nonempty (TrajectoryGodMoveBoundaryMinor enc O.toTrajectory n)) := by
  intro hminor
  rcases hminor with ⟨minor⟩
  have hwidth :
      Nat.choose (n / 3) (Nat.log 2 n) <= O.toTrajectory.width n :=
    observer_width_lower_of_trajectory_minor minor
  have hupper :
      Nat.choose (n / 3) (Nat.log 2 n) <= n ^ d := by
    simpa [CanonicalPolynomialNeighborhoodObserver.toTrajectory] using hwidth
  exact (not_le_of_gt hgap) hupper

/-- Fixed-length extraction is false for any existing canonical polynomial
observer once the binomial boundary exceeds the polynomial neighborhood size. -/
theorem not_canonicalPolynomialNeighborhoodExtractionAt_of_gap
    {enc : ThreeCNFEncoding} {d : Nat}
    {N : CanonicalPolynomialNeighborhood d}
    (O : CanonicalPolynomialNeighborhoodObserver enc N) {n : Nat}
    (hgap : n ^ d < Nat.choose (n / 3) (Nat.log 2 n)) :
    Not (CanonicalPolynomialNeighborhoodExtractionAt enc N n) := by
  intro hextract
  exact no_trajectoryMinor_of_canonicalPolynomialNeighborhood_gap
    O hgap (hextract O)

/-- If a SAT-deciding DTM exists, no fixed-polynomial canonical neighborhood can
satisfy the universal binomial live-minor extraction target. -/
theorem not_universalCanonicalPolynomialNeighborhoodExtraction_of_decider
    {enc : ThreeCNFEncoding} {d : Nat}
    (N : CanonicalPolynomialNeighborhood d)
    (hdec : exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) :
    Not (UniversalCanonicalPolynomialNeighborhoodExtraction enc N) := by
  intro hextract
  rcases hdec with ⟨M, hMdec⟩
  let O : CanonicalPolynomialNeighborhoodObserver enc N := ⟨M, hMdec⟩
  rcases hextract d with ⟨n, hn20, hlog, hextract_at⟩
  have hgap :
      n ^ d < Nat.choose (n / 3) (Nat.log 2 n) :=
    arithmetic_gap_for_exponent d n hn20 hlog
  exact
    (not_canonicalPolynomialNeighborhoodExtractionAt_of_gap O hgap)
      hextract_at

/-- Conversely, if no DTM decides SAT under the encoding, the extraction target
is vacuous for every canonical polynomial neighborhood. -/
theorem universalCanonicalPolynomialNeighborhoodExtraction_of_no_decider
    (enc : ThreeCNFEncoding) {d : Nat}
    (N : CanonicalPolynomialNeighborhood d)
    (hno : Not (exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M)) :
    UniversalCanonicalPolynomialNeighborhoodExtraction enc N := by
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

/-- Exact status of every fixed-polynomial canonical-neighborhood pivot.

The invariant is canonical and polynomially bounded, but that same polynomial
bound prevents it from carrying the paper's binomial God-Move minor unless no
polynomial-time SAT-deciding DTM exists. -/
theorem universalCanonicalPolynomialNeighborhoodExtraction_iff_no_decider
    (enc : ThreeCNFEncoding) {d : Nat}
    (N : CanonicalPolynomialNeighborhood d) :
    UniversalCanonicalPolynomialNeighborhoodExtraction enc N ↔
      Not (exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) := by
  constructor
  · intro hextract hdec
    exact
      (not_universalCanonicalPolynomialNeighborhoodExtraction_of_decider
        (enc := enc) N hdec)
        hextract
  · exact universalCanonicalPolynomialNeighborhoodExtraction_of_no_decider enc N

/-! ## Kernel-only axiom trace -/

#print axioms canonicalPolynomialNeighborhoodLiveContextRank_le_poly
#print axioms not_universalCanonicalPolynomialNeighborhoodExtraction_of_decider
#print axioms universalCanonicalPolynomialNeighborhoodExtraction_of_no_decider
#print axioms universalCanonicalPolynomialNeighborhoodExtraction_iff_no_decider

end PallLean.Paper93.DeepMath.PathB
