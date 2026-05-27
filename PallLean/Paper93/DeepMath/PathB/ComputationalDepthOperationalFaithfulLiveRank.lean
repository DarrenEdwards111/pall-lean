import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSemanticClosureFrontier

/-!
# Operational faithful live rank

This file implements the non-circular refinement suggested by the zero-rank
obstruction: do not let a SAT decider choose arbitrary live-rank bookkeeping.
Instead, compute live rank from the actual DTM run.

The concrete operational rank here is intentionally minimal and semantic:
at a live configuration it counts the radius-one local configuration
neighborhood

```text
{ current configuration, one-step successor configuration }.
```

This excludes the structure-free `fun _ => 0` presentation without assuming any
high-rank minor.  The resulting audit is sharp: merely tying live rank to the
machine semantics is not enough to prove the God-Move lower bound.  This
faithful rank is always at most `2`, so a binomial live-boundary minor is still
impossible at paper scale.  Therefore any successful version needs a richer
operational semantic rank theorem, not just a ban on arbitrary bookkeeping.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- The cardinality of the actual radius-one local configuration neighborhood
at a DTM configuration: the current configuration and its deterministic
successor.  It is `1` when the successor has the same code and `2` otherwise.

This avoids any quotienting or rank payload: it is a direct function of the
machine's actual transition semantics. -/
noncomputable def operationalLocalConfigNeighborhoodRank
    (M : TuringMachine.DTM) (n : Nat)
    (cfg : TuringMachine.Configuration M (TuringMachine.tapeSize M n)) : Nat :=
  if strictConfigCode M cfg =
      strictConfigCode M (TuringMachine.step M n cfg) then
    1
  else
    2

/-- The radius-one operational neighborhood is nonempty. -/
theorem operationalLocalConfigNeighborhoodRank_pos
    (M : TuringMachine.DTM) (n : Nat)
    (cfg : TuringMachine.Configuration M (TuringMachine.tapeSize M n)) :
    0 < operationalLocalConfigNeighborhoodRank M n cfg := by
  by_cases h :
      strictConfigCode M cfg =
        strictConfigCode M (TuringMachine.step M n cfg)
  · simp [operationalLocalConfigNeighborhoodRank, h]
  · simp [operationalLocalConfigNeighborhoodRank, h]

/-- The radius-one operational neighborhood has at most two configurations. -/
theorem operationalLocalConfigNeighborhoodRank_le_two
    (M : TuringMachine.DTM) (n : Nat)
    (cfg : TuringMachine.Configuration M (TuringMachine.tapeSize M n)) :
    operationalLocalConfigNeighborhoodRank M n cfg <= 2 := by
  by_cases h :
      strictConfigCode M cfg =
        strictConfigCode M (TuringMachine.step M n cfg)
  · simp [operationalLocalConfigNeighborhoodRank, h]
  · simp [operationalLocalConfigNeighborhoodRank, h]

/-- Operational live rank at a time/input is the size of the actual one-step
configuration neighborhood, and zero outside the running window. -/
noncomputable def OperationalStrictLiveRankAt
    (M : TuringMachine.DTM)
    (n : Nat) (input : Fin n -> Bool) (t : Nat) : Nat :=
  if hn : n >= 1 then
    if t < TuringMachine.timeSteps M n + 1 then
      let cfg := TuringMachine.run M n t
        (TuringMachine.initialConfig M n hn input)
      operationalLocalConfigNeighborhoodRank M n cfg
    else
      0
  else
    0

/-- Inside the actual running window, operational live rank is positive.
This is the non-circular exclusion of the zero-rank presentation. -/
theorem OperationalStrictLiveRankAt_pos
    (M : TuringMachine.DTM)
    {n : Nat} (hn : n >= 1)
    (input : Fin n -> Bool)
    {t : Nat} (ht : t < TuringMachine.timeSteps M n + 1) :
    0 < OperationalStrictLiveRankAt M n input t := by
  simp [OperationalStrictLiveRankAt, hn, ht,
    operationalLocalConfigNeighborhoodRank_pos]

/-- Operational live rank is always bounded by `2`. -/
theorem OperationalStrictLiveRankAt_le_two
    (M : TuringMachine.DTM)
    (n : Nat) (input : Fin n -> Bool) (t : Nat) :
    OperationalStrictLiveRankAt M n input t <= 2 := by
  unfold OperationalStrictLiveRankAt
  by_cases hn : n >= 1
  · by_cases ht : t < TuringMachine.timeSteps M n + 1
    · simp [hn, ht, operationalLocalConfigNeighborhoodRank_le_two]
    · simp [hn, ht]
  · simp [hn]

/-- Trajectory machine whose live-boundary rank is computed from the actual
DTM configuration-neighborhood semantics, not supplied as arbitrary
bookkeeping. -/
noncomputable def operationalFaithfulTrajectoryObserver
    (M : TuringMachine.DTM) : TrajectoryObserverMachine where
  width := fun _ => 2
  acceptsInput := fun n input =>
    if hn : n >= 1 then TuringMachine.accepts M n hn input else False
  stateCode := fun n input t =>
    if hn : n >= 1 then
      let cfg := TuringMachine.run M n t
        (TuringMachine.initialConfig M n hn input)
      strictConfigCode M cfg
    else
      0
  liveBoundaryRank := OperationalStrictLiveRankAt M
  liveBoundaryRank_le_width := OperationalStrictLiveRankAt_le_two M

/-- Operational faithful observer: an encoded SAT-deciding DTM read through the
actual radius-one live-rank semantics above. -/
structure OperationalFaithfulLiveRankObserver
    (enc : ThreeCNFEncoding) where
  M : TuringMachine.DTM
  decides : DTMDecidesSATWithEncoding enc M

/-- The operational trajectory associated to an operational faithful observer. -/
noncomputable def OperationalFaithfulLiveRankObserver.toTrajectory
    {enc : ThreeCNFEncoding}
    (O : OperationalFaithfulLiveRankObserver enc) :
    TrajectoryObserverMachine :=
  operationalFaithfulTrajectoryObserver O.M

/-- Any encoded SAT decider has a canonical operational faithful presentation. -/
noncomputable def operationalFaithfulObserver_of_DTMDecidesSATWithEncoding
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM}
    (hM : DTMDecidesSATWithEncoding enc M) :
    OperationalFaithfulLiveRankObserver enc where
  M := M
  decides := hM

/-- Operational faithful live rank is uniformly bounded by `2`. -/
theorem operationalFaithful_liveBoundaryRank_le_two
    {enc : ThreeCNFEncoding}
    (O : OperationalFaithfulLiveRankObserver enc)
    (n : Nat) (input : Fin n -> Bool) (time : Nat) :
    O.toTrajectory.liveBoundaryRank n input time <= 2 := by
  exact OperationalStrictLiveRankAt_le_two O.M n input time

/-- Operational faithful live rank is positive on valid running-window states. -/
theorem operationalFaithful_liveBoundaryRank_pos
    {enc : ThreeCNFEncoding}
    (O : OperationalFaithfulLiveRankObserver enc)
    {n : Nat} (hn : n >= 1)
    (input : Fin n -> Bool)
    {time : Nat} (ht : time < TuringMachine.timeSteps O.M n + 1) :
    0 < O.toTrajectory.liveBoundaryRank n input time := by
  exact OperationalStrictLiveRankAt_pos O.M hn input ht

/-- Fixed-length operational semantic closure: every operational faithful SAT
observer carries a God-Move boundary minor at this length. -/
def OperationalSemanticClosureExtractionAt
    (enc : ThreeCNFEncoding) (n : Nat) : Prop :=
  forall O : OperationalFaithfulLiveRankObserver enc,
    Nonempty (TrajectoryGodMoveBoundaryMinor enc O.toTrajectory n)

/-- Paper-scale operational semantic closure.  This is the candidate obtained
after replacing arbitrary presentation rank by actual operational live rank. -/
def OperationalFaithfulSemanticClosure
    (enc : ThreeCNFEncoding) : Prop :=
  forall c : Nat, exists n : Nat,
    n >= 2 ^ 20 /\
    4 * (c + 1) <= Nat.log 2 n /\
    OperationalSemanticClosureExtractionAt enc n

/-- At paper scale, the operational radius-one rank cannot support a binomial
minor: the live boundary is at most `2`, while the binomial floor is already
larger than `2`. -/
theorem no_operationalTrajectoryMinor_at_paperScale
    {enc : ThreeCNFEncoding}
    (O : OperationalFaithfulLiveRankObserver enc)
    {n : Nat}
    (hn20 : n >= 2 ^ 20)
    (hlog : 4 * (1 + 1) <= Nat.log 2 n) :
    Not (Nonempty (TrajectoryGodMoveBoundaryMinor enc O.toTrajectory n)) := by
  intro hminor
  rcases hminor with ⟨minor⟩
  have hboundary_le_two :
      O.toTrajectory.liveBoundaryRank n minor.input minor.time <= 2 :=
    operationalFaithful_liveBoundaryRank_le_two O n minor.input minor.time
  have hlive_le_two : minor.liveRank <= 2 :=
    le_trans minor.rank_le_boundary hboundary_le_two
  have hgap :
      n ^ 1 < Nat.choose (n / 3) (Nat.log 2 n) :=
    arithmetic_gap_for_exponent 1 n hn20 hlog
  have hn_ge_two : 2 <= n := by
    have hpow : 2 <= 2 ^ 20 := by norm_num
    exact le_trans hpow hn20
  have htwo_lt_choose :
      2 < Nat.choose (n / 3) (Nat.log 2 n) := by
    have hn_lt_choose :
        n < Nat.choose (n / 3) (Nat.log 2 n) := by
      simpa using hgap
    exact lt_of_le_of_lt hn_ge_two hn_lt_choose
  have hchoose_le_two :
      Nat.choose (n / 3) (Nat.log 2 n) <= 2 :=
    le_trans minor.rank_lower hlive_le_two
  exact (Nat.not_lt_of_ge hchoose_le_two) htwo_lt_choose

/-- If an encoded SAT decider exists, operational semantic closure fails at any
paper-scale length with the `c = 1` gap. -/
theorem not_operationalSemanticClosureExtractionAt_of_DTMDecidesSATWithEncoding
    {enc : ThreeCNFEncoding}
    (hdec : exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M)
    {n : Nat}
    (hn20 : n >= 2 ^ 20)
    (hlog : 4 * (1 + 1) <= Nat.log 2 n) :
    Not (OperationalSemanticClosureExtractionAt enc n) := by
  intro hAt
  rcases hdec with ⟨M, hM⟩
  let O : OperationalFaithfulLiveRankObserver enc :=
    operationalFaithfulObserver_of_DTMDecidesSATWithEncoding hM
  exact (no_operationalTrajectoryMinor_at_paperScale O hn20 hlog) (hAt O)

/-- Operational semantic closure still implies the no-decider endpoint.  The
proof is explicit: a hypothetical decider has an operational faithful
presentation, but that presentation has live rank at most `2`. -/
theorem no_DTMDecidesSATWithEncoding_of_operationalFaithfulSemanticClosure
    (enc : ThreeCNFEncoding)
    (H : OperationalFaithfulSemanticClosure enc) :
    Not (exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M) := by
  intro hdec
  rcases H 1 with ⟨n, hn20, hlog, hAt⟩
  exact (not_operationalSemanticClosureExtractionAt_of_DTMDecidesSATWithEncoding
    hdec hn20 hlog) hAt

/-- Conversely, if no encoded SAT decider exists, operational semantic closure
is vacuous because there are no operational faithful SAT observers. -/
theorem operationalFaithfulSemanticClosure_of_no_DTMDecidesSATWithEncoding
    (enc : ThreeCNFEncoding)
    (hno : Not (exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M)) :
    OperationalFaithfulSemanticClosure enc := by
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

/-- Exact audit result for the operational faithful refinement.

The zero-rank presentation is gone, but a radius-one operational neighborhood
rank is still too small.  Therefore this refinement is not a proof route by
itself; it precisely identifies the next required theorem as a richer semantic
rank lower bound tied to the actual run, not merely nonzero operational
faithfulness. -/
theorem operationalFaithfulSemanticClosure_iff_no_DTMDecidesSATWithEncoding
    (enc : ThreeCNFEncoding) :
    OperationalFaithfulSemanticClosure enc ↔
      Not (exists M : TuringMachine.DTM,
        DTMDecidesSATWithEncoding enc M) := by
  constructor
  · exact no_DTMDecidesSATWithEncoding_of_operationalFaithfulSemanticClosure enc
  · exact operationalFaithfulSemanticClosure_of_no_DTMDecidesSATWithEncoding enc

/-! ## Kernel-only axiom trace -/

#print axioms operationalLocalConfigNeighborhoodRank_pos
#print axioms operationalLocalConfigNeighborhoodRank_le_two
#print axioms OperationalStrictLiveRankAt_pos
#print axioms OperationalStrictLiveRankAt_le_two
#print axioms operationalFaithful_liveBoundaryRank_le_two
#print axioms operationalFaithful_liveBoundaryRank_pos
#print axioms no_operationalTrajectoryMinor_at_paperScale
#print axioms not_operationalSemanticClosureExtractionAt_of_DTMDecidesSATWithEncoding
#print axioms no_DTMDecidesSATWithEncoding_of_operationalFaithfulSemanticClosure
#print axioms operationalFaithfulSemanticClosure_of_no_DTMDecidesSATWithEncoding
#print axioms operationalFaithfulSemanticClosure_iff_no_DTMDecidesSATWithEncoding

end PallLean.Paper93.DeepMath.PathB
