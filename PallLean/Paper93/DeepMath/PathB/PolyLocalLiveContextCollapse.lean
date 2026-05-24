import PallLean.Paper93.DeepMath.PathB.ObserverTrajectoryDCEW

/-!
# Poly-local live-context collapse

This file records the general counting theorem behind the canonical dynamic
CEW experiments.

The previous files tested concrete choices:

* radius-one local context;
* fixed-polynomial canonical neighborhoods;
* saturated SAT-semantic rank.

The real obstruction is independent of those presentations.  If a live-context
rank is bounded by any polynomial-size context, then it cannot carry the
paper's binomial God-Move boundary minor at the arithmetic-gap scale.  Therefore
the corresponding universal live-minor extraction theorem is equivalent to the
absence of a polynomial-time SAT-deciding DTM.

This is the paper-faithful "poly-local" collapse theorem: the P-side-feasible
half of the dynamic invariant family is too small by counting.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-! ## Abstract poly-local live-context ranks -/

/-- A live-context rank bounded by a polynomial-size context.

The fields intentionally abstract away the concrete canonical rule.  This covers
radius-one neighborhoods, constant-radius neighborhoods, fixed-polynomial
semantic neighborhoods, and any other observer-independent rule whose live
context size is bounded by `n^k`. -/
structure PolyLocalLiveContextRank
    (enc : ThreeCNFEncoding) (k : Nat) where
  contextSize : Nat -> Nat
  liveRank : (n : Nat) -> (Fin n -> Bool) -> Nat
  liveRank_le_contextSize :
    forall (n : Nat) (input : Fin n -> Bool),
      liveRank n input <= contextSize n
  contextSize_le_poly :
    forall n : Nat, contextSize n <= n ^ k

/-- A SAT observer whose live rank is forced by a poly-local rank rule. -/
structure PolyLocalLiveContextObserver
    (enc : ThreeCNFEncoding) {k : Nat}
    (R : PolyLocalLiveContextRank enc k) where
  M : TuringMachine.DTM
  decides : DTMDecidesSATWithEncoding enc M

/-- Forget a poly-local observer to a trajectory observer. -/
noncomputable def PolyLocalLiveContextObserver.toTrajectory
    {enc : ThreeCNFEncoding} {k : Nat}
    {R : PolyLocalLiveContextRank enc k}
    (O : PolyLocalLiveContextObserver enc R) :
    TrajectoryObserverMachine where
  width := R.contextSize
  acceptsInput := fun n input =>
    exists hn : n >= 1, TuringMachine.accepts O.M n hn input
  stateCode := fun n input t =>
    if hn : n >= 1 then
      (TuringMachine.run O.M n t
        (TuringMachine.initialConfig O.M n hn input)).state.val
    else
      0
  liveBoundaryRank := fun n input _ => R.liveRank n input
  liveBoundaryRank_le_width := by
    intro n input t
    exact R.liveRank_le_contextSize n input

/-- The trajectory width is exactly the poly-local context-size bound. -/
theorem PolyLocalLiveContextObserver.toTrajectory_width
    {enc : ThreeCNFEncoding} {k : Nat}
    {R : PolyLocalLiveContextRank enc k}
    (O : PolyLocalLiveContextObserver enc R) (n : Nat) :
    O.toTrajectory.width n = R.contextSize n := by
  rfl

/-! ## Universal extraction target -/

/-- Fixed-length live-minor extraction for a poly-local rank rule. -/
def PolyLocalLiveContextExtractionAt
    (enc : ThreeCNFEncoding) {k : Nat}
    (R : PolyLocalLiveContextRank enc k) (n : Nat) : Prop :=
  forall O : PolyLocalLiveContextObserver enc R,
    Nonempty (TrajectoryGodMoveBoundaryMinor enc O.toTrajectory n)

/-- Exponent-parametric live-minor extraction for a poly-local rank rule. -/
def UniversalPolyLocalLiveContextExtraction
    (enc : ThreeCNFEncoding) {k : Nat}
    (R : PolyLocalLiveContextRank enc k) : Prop :=
  forall c : Nat, exists n : Nat,
    n >= 2 ^ 20 /\
    4 * (c + 1) <= Nat.log 2 n /\
    PolyLocalLiveContextExtractionAt enc R n

/-! ## Counting collapse -/

/-- If the binomial boundary exceeds the poly-local context size, no trajectory
minor can fit inside the induced observer. -/
theorem no_trajectoryMinor_of_polyLocal_context_gap
    {enc : ThreeCNFEncoding} {k : Nat}
    {R : PolyLocalLiveContextRank enc k}
    (O : PolyLocalLiveContextObserver enc R) {n : Nat}
    (hgap :
      R.contextSize n < Nat.choose (n / 3) (Nat.log 2 n)) :
    Not (Nonempty (TrajectoryGodMoveBoundaryMinor enc O.toTrajectory n)) := by
  intro hminor
  rcases hminor with ⟨minor⟩
  have hwidth :
      Nat.choose (n / 3) (Nat.log 2 n) <= O.toTrajectory.width n :=
    observer_width_lower_of_trajectory_minor minor
  have hboundary :
      Nat.choose (n / 3) (Nat.log 2 n) <= R.contextSize n := by
    simpa [PolyLocalLiveContextObserver.toTrajectory] using hwidth
  exact (not_le_of_gt hgap) hboundary

/-- At the arithmetic-gap scale, every poly-local context is smaller than the
binomial boundary. -/
theorem polyLocal_context_lt_boundary_of_scale
    {enc : ThreeCNFEncoding} {k n : Nat}
    (R : PolyLocalLiveContextRank enc k)
    (hn20 : n >= 2 ^ 20)
    (hlog : 4 * (k + 1) <= Nat.log 2 n) :
    R.contextSize n < Nat.choose (n / 3) (Nat.log 2 n) := by
  have hpoly : R.contextSize n <= n ^ k :=
    R.contextSize_le_poly n
  have hgap :
      n ^ k < Nat.choose (n / 3) (Nat.log 2 n) :=
    arithmetic_gap_for_exponent k n hn20 hlog
  exact lt_of_le_of_lt hpoly hgap

/-- Fixed-length poly-local extraction is impossible for any existing observer
at a scale where the binomial boundary exceeds the context size. -/
theorem not_polyLocalLiveContextExtractionAt_of_context_gap
    {enc : ThreeCNFEncoding} {k : Nat}
    {R : PolyLocalLiveContextRank enc k}
    (O : PolyLocalLiveContextObserver enc R) {n : Nat}
    (hgap :
      R.contextSize n < Nat.choose (n / 3) (Nat.log 2 n)) :
    Not (PolyLocalLiveContextExtractionAt enc R n) := by
  intro hextract
  exact no_trajectoryMinor_of_polyLocal_context_gap
    O hgap (hextract O)

/-- If a SAT-deciding DTM exists, no poly-local rank rule can satisfy the
universal binomial live-minor extraction target.

This is the general counting obstruction: P-side-feasible polynomial live
context is too small to host the paper's superpolynomial boundary minor. -/
theorem not_universalPolyLocalLiveContextExtraction_of_decider
    {enc : ThreeCNFEncoding} {k : Nat}
    (R : PolyLocalLiveContextRank enc k)
    (hdec : exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) :
    Not (UniversalPolyLocalLiveContextExtraction enc R) := by
  intro hextract
  rcases hdec with ⟨M, hMdec⟩
  let O : PolyLocalLiveContextObserver enc R := ⟨M, hMdec⟩
  rcases hextract k with ⟨n, hn20, hlog, hextract_at⟩
  have hgap :
      R.contextSize n < Nat.choose (n / 3) (Nat.log 2 n) :=
    polyLocal_context_lt_boundary_of_scale R hn20 hlog
  exact
    (not_polyLocalLiveContextExtractionAt_of_context_gap O hgap)
      hextract_at

/-- Conversely, if no DTM decides SAT under the encoding, the poly-local
extraction target is vacuous. -/
theorem universalPolyLocalLiveContextExtraction_of_no_decider
    (enc : ThreeCNFEncoding) {k : Nat}
    (R : PolyLocalLiveContextRank enc k)
    (hno : Not (exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M)) :
    UniversalPolyLocalLiveContextExtraction enc R := by
  intro c
  let j : Nat := Nat.max 20 (4 * (c + 1))
  let n : Nat := 2 ^ j
  refine ⟨n, ?_, ?_, ?_⟩
  · dsimp [n, j]
    exact Nat.pow_le_pow_right
      (by norm_num : 1 <= 2)
      (Nat.le_max_left 20 (4 * (c + 1)))
  · dsimp [n, j]
    have hpow :
        2 ^ (4 * (c + 1)) <= 2 ^ Nat.max 20 (4 * (c + 1)) :=
      Nat.pow_le_pow_right
        (by norm_num : 1 <= 2)
        (Nat.le_max_right 20 (4 * (c + 1)))
    exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow
  · intro O
    exact False.elim (hno ⟨O.M, O.decides⟩)

/-- Exact general collapse theorem for every polynomial-size live-context rank.

This subsumes the radius-one and fixed-polynomial-neighborhood tests.  The only
way to escape the theorem is to leave the poly-local hypothesis, which means
the live context is already superpolynomial and the P-side CEW calibration is
lost. -/
theorem universalPolyLocalLiveContextExtraction_iff_no_decider
    (enc : ThreeCNFEncoding) {k : Nat}
    (R : PolyLocalLiveContextRank enc k) :
    UniversalPolyLocalLiveContextExtraction enc R ↔
      Not (exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) := by
  constructor
  · intro hextract hdec
    exact
      (not_universalPolyLocalLiveContextExtraction_of_decider
        (enc := enc) R hdec)
        hextract
  · exact universalPolyLocalLiveContextExtraction_of_no_decider enc R

/-! ## Kernel-only axiom trace -/

#print axioms no_trajectoryMinor_of_polyLocal_context_gap
#print axioms polyLocal_context_lt_boundary_of_scale
#print axioms not_universalPolyLocalLiveContextExtraction_of_decider
#print axioms universalPolyLocalLiveContextExtraction_of_no_decider
#print axioms universalPolyLocalLiveContextExtraction_iff_no_decider

end PallLean.Paper93.DeepMath.PathB
