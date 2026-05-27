import PallLean.Paper93.DeepMath.PathB.ComputationalDepthOperationalFaithfulLiveRank

/-!
# Operational trace-prefix semantic rank

`ComputationalDepthOperationalFaithfulLiveRank` ties live rank to the actual
one-step DTM transition semantics.  That removes arbitrary zero-rank
bookkeeping, but the resulting radius-one rank is bounded by `2`.

This file tests the next stronger non-smuggling refinement: let the live rank
see the whole actual run prefix up to time `t`.  This is still fully induced by
the DTM run, not supplied as an external rank field.

The result is sharp and negative: even this richer run-induced rank is bounded
by the polynomial time window `n ^ M.timeBound + 1`.  At the paper scale, the
binomial floor eventually dominates that polynomial.  Therefore trace-prefix
semantic closure is again equivalent to the no-decider endpoint.

The useful conclusion is not a proof of P vs NP.  It identifies the next
unavoidable strengthening: a successful live-rank theorem must extract
superpolynomial semantic structure from the run, not merely count local
configurations or the polynomial-length trace prefix.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Trace-prefix live rank.  Inside the actual polynomial-time run window this
is the size of the prefix `{0, ..., t}` of the DTM trajectory.  Outside the
declared window it is zero.

This is deliberately fixed by the actual run clock.  The observer no longer
chooses an arbitrary `liveBoundaryRank`. -/
noncomputable def OperationalTracePrefixRankAt
    (M : TuringMachine.DTM)
    (n : Nat) (_input : Fin n -> Bool) (t : Nat) : Nat :=
  if _hn : n >= 1 then
    if _ht : t < TuringMachine.timeSteps M n + 1 then
      t + 1
    else
      0
  else
    0

/-- Trace-prefix rank is positive inside the actual run window. -/
theorem OperationalTracePrefixRankAt_pos
    (M : TuringMachine.DTM)
    {n : Nat} (hn : n >= 1)
    (input : Fin n -> Bool)
    {t : Nat} (ht : t < TuringMachine.timeSteps M n + 1) :
    0 < OperationalTracePrefixRankAt M n input t := by
  simp [OperationalTracePrefixRankAt, hn, ht]

/-- Trace-prefix rank is bounded by the DTM's polynomial time window. -/
theorem OperationalTracePrefixRankAt_le_timeWindow
    (M : TuringMachine.DTM)
    (n : Nat) (input : Fin n -> Bool) (t : Nat) :
    OperationalTracePrefixRankAt M n input t <=
      TuringMachine.timeSteps M n + 1 := by
  unfold OperationalTracePrefixRankAt
  by_cases hn : n >= 1
  · by_cases ht : t < TuringMachine.timeSteps M n + 1
    · simp [hn, ht]
      omega
    · simp [hn, ht]
  · simp [hn]

/-- For lengths at least two, the polynomial time window plus one is bounded
by the next power. -/
theorem timeWindow_succ_le_next_power
    (M : TuringMachine.DTM)
    {n : Nat} (hn2 : 2 <= n) :
    TuringMachine.timeSteps M n + 1 <= n ^ (M.timeBound + 1) := by
  unfold TuringMachine.timeSteps
  have hpow_pos : 0 < n ^ M.timeBound :=
    Nat.pow_pos (lt_of_lt_of_le (by norm_num : 0 < 2) hn2)
  have hone_le_pow : 1 <= n ^ M.timeBound :=
    Nat.succ_le_of_lt hpow_pos
  have hsum :
      n ^ M.timeBound + 1 <= n ^ M.timeBound + n ^ M.timeBound :=
    Nat.add_le_add_left hone_le_pow (n ^ M.timeBound)
  have hmul :
      n ^ M.timeBound + n ^ M.timeBound <=
        n * n ^ M.timeBound := by
    calc
      n ^ M.timeBound + n ^ M.timeBound
          = 2 * n ^ M.timeBound := by ring
      _ <= n * n ^ M.timeBound :=
          Nat.mul_le_mul_right (n ^ M.timeBound) hn2
  have hpow :
      n * n ^ M.timeBound = n ^ (M.timeBound + 1) := by
    simp [Nat.pow_succ, Nat.mul_comm]
  exact le_trans hsum (hpow ▸ hmul)

/-- Trace-prefix rank is polynomially bounded by the DTM time exponent plus
one. -/
theorem OperationalTracePrefixRankAt_le_next_power
    (M : TuringMachine.DTM)
    {n : Nat} (hn2 : 2 <= n)
    (input : Fin n -> Bool) (t : Nat) :
    OperationalTracePrefixRankAt M n input t <= n ^ (M.timeBound + 1) :=
  le_trans
    (OperationalTracePrefixRankAt_le_timeWindow M n input t)
    (timeWindow_succ_le_next_power M hn2)

/-- Trajectory observer whose live-boundary rank is the actual DTM trace-prefix
rank. -/
noncomputable def operationalTracePrefixTrajectoryObserver
    (M : TuringMachine.DTM) : TrajectoryObserverMachine where
  width := fun n =>
    if _hn : n >= 1 then TuringMachine.timeSteps M n + 1 else 0
  acceptsInput := fun n input =>
    if hn : n >= 1 then TuringMachine.accepts M n hn input else False
  stateCode := fun n input t =>
    if hn : n >= 1 then
      let cfg := TuringMachine.run M n t
        (TuringMachine.initialConfig M n hn input)
      strictConfigCode M cfg
    else
      0
  liveBoundaryRank := OperationalTracePrefixRankAt M
  liveBoundaryRank_le_width := by
    intro n input t
    unfold OperationalTracePrefixRankAt
    by_cases hn : n >= 1
    · by_cases ht : t < TuringMachine.timeSteps M n + 1
      · simp [hn, ht]
        omega
      · simp [hn, ht]
    · simp [hn]

/-- Operational trace-prefix observer: an encoded SAT-deciding DTM read through
the actual polynomial-length trace-prefix rank. -/
structure OperationalTracePrefixObserver
    (enc : ThreeCNFEncoding) where
  M : TuringMachine.DTM
  decides : DTMDecidesSATWithEncoding enc M

/-- Associated trace-prefix trajectory. -/
noncomputable def OperationalTracePrefixObserver.toTrajectory
    {enc : ThreeCNFEncoding}
    (O : OperationalTracePrefixObserver enc) :
    TrajectoryObserverMachine :=
  operationalTracePrefixTrajectoryObserver O.M

/-- Any encoded SAT decider has a canonical trace-prefix presentation. -/
noncomputable def operationalTracePrefixObserver_of_DTMDecidesSATWithEncoding
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM}
    (hM : DTMDecidesSATWithEncoding enc M) :
    OperationalTracePrefixObserver enc where
  M := M
  decides := hM

/-- Trace-prefix live rank is bounded by the next power of the DTM time
exponent at lengths at least two. -/
theorem operationalTracePrefix_liveBoundaryRank_le_next_power
    {enc : ThreeCNFEncoding}
    (O : OperationalTracePrefixObserver enc)
    {n : Nat} (hn2 : 2 <= n)
    (input : Fin n -> Bool) (time : Nat) :
    O.toTrajectory.liveBoundaryRank n input time <= n ^ (O.M.timeBound + 1) :=
  OperationalTracePrefixRankAt_le_next_power O.M hn2 input time

/-- Fixed-length trace-prefix semantic closure. -/
def OperationalTracePrefixSemanticClosureExtractionAt
    (enc : ThreeCNFEncoding) (n : Nat) : Prop :=
  forall O : OperationalTracePrefixObserver enc,
    Nonempty (TrajectoryGodMoveBoundaryMinor enc O.toTrajectory n)

/-- Paper-scale trace-prefix semantic closure. -/
def OperationalTracePrefixSemanticClosure
    (enc : ThreeCNFEncoding) : Prop :=
  forall c : Nat, exists n : Nat,
    n >= 2 ^ 20 /\
    4 * (c + 1) <= Nat.log 2 n /\
    OperationalTracePrefixSemanticClosureExtractionAt enc n

/-- A trace-prefix observer cannot carry the paper-scale binomial minor once
the gap is taken against its own polynomial time exponent. -/
theorem no_operationalTracePrefixMinor_at_paperScale
    {enc : ThreeCNFEncoding}
    (O : OperationalTracePrefixObserver enc)
    {n : Nat}
    (hn20 : n >= 2 ^ 20)
    (hlog : 4 * ((O.M.timeBound + 1) + 1) <= Nat.log 2 n) :
    Not (Nonempty (TrajectoryGodMoveBoundaryMinor enc O.toTrajectory n)) := by
  intro hminor
  rcases hminor with ⟨minor⟩
  have hn2 : 2 <= n :=
    le_trans (by norm_num : 2 <= 2 ^ 20) hn20
  have hlive_le_poly :
      minor.liveRank <= n ^ (O.M.timeBound + 1) :=
    le_trans minor.rank_le_boundary
      (operationalTracePrefix_liveBoundaryRank_le_next_power
        O hn2 minor.input minor.time)
  have hgap :
      n ^ (O.M.timeBound + 1) <
        Nat.choose (n / 3) (Nat.log 2 n) :=
    arithmetic_gap_for_exponent (O.M.timeBound + 1) n hn20 hlog
  have hchoose_le_poly :
      Nat.choose (n / 3) (Nat.log 2 n) <=
        n ^ (O.M.timeBound + 1) :=
    le_trans minor.rank_lower hlive_le_poly
  exact (Nat.not_lt_of_ge hchoose_le_poly) hgap

/-- If an encoded SAT decider exists, trace-prefix semantic closure fails at
the paper scale tuned to that machine's polynomial time exponent. -/
theorem not_operationalTracePrefixSemanticClosureExtractionAt_of_DTMDecidesSATWithEncoding
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM}
    (hM : DTMDecidesSATWithEncoding enc M)
    {n : Nat}
    (hn20 : n >= 2 ^ 20)
    (hlog : 4 * ((M.timeBound + 1) + 1) <= Nat.log 2 n) :
    Not (OperationalTracePrefixSemanticClosureExtractionAt enc n) := by
  intro hAt
  let O : OperationalTracePrefixObserver enc :=
    operationalTracePrefixObserver_of_DTMDecidesSATWithEncoding hM
  exact (no_operationalTracePrefixMinor_at_paperScale O hn20 hlog) (hAt O)

/-- Trace-prefix semantic closure implies the no-decider endpoint.  This is not
a rank-bookkeeping artifact: the presentation is run-induced, but its rank is
still polynomial because the run is polynomial-time. -/
theorem no_DTMDecidesSATWithEncoding_of_operationalTracePrefixSemanticClosure
    (enc : ThreeCNFEncoding)
    (H : OperationalTracePrefixSemanticClosure enc) :
    Not (exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M) := by
  intro hdec
  rcases hdec with ⟨M, hM⟩
  rcases H (M.timeBound + 1) with ⟨n, hn20, hlog, hAt⟩
  exact
    (not_operationalTracePrefixSemanticClosureExtractionAt_of_DTMDecidesSATWithEncoding
      hM hn20 hlog) hAt

/-- Conversely, with no encoded SAT decider, trace-prefix semantic closure is
vacuous because there are no trace-prefix SAT observers. -/
theorem operationalTracePrefixSemanticClosure_of_no_DTMDecidesSATWithEncoding
    (enc : ThreeCNFEncoding)
    (hno : Not (exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M)) :
    OperationalTracePrefixSemanticClosure enc := by
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

/-- Exact audit for the trace-prefix semantic-rank refinement.

Even allowing the live rank to see the entire polynomial-length DTM run prefix,
the closure theorem is still equivalent to the no-decider endpoint. -/
theorem operationalTracePrefixSemanticClosure_iff_no_DTMDecidesSATWithEncoding
    (enc : ThreeCNFEncoding) :
    OperationalTracePrefixSemanticClosure enc ↔
      Not (exists M : TuringMachine.DTM,
        DTMDecidesSATWithEncoding enc M) := by
  constructor
  · exact no_DTMDecidesSATWithEncoding_of_operationalTracePrefixSemanticClosure enc
  · exact operationalTracePrefixSemanticClosure_of_no_DTMDecidesSATWithEncoding enc

/-! ## Kernel-only axiom trace -/

#print axioms OperationalTracePrefixRankAt_pos
#print axioms OperationalTracePrefixRankAt_le_timeWindow
#print axioms timeWindow_succ_le_next_power
#print axioms OperationalTracePrefixRankAt_le_next_power
#print axioms operationalTracePrefix_liveBoundaryRank_le_next_power
#print axioms no_operationalTracePrefixMinor_at_paperScale
#print axioms not_operationalTracePrefixSemanticClosureExtractionAt_of_DTMDecidesSATWithEncoding
#print axioms no_DTMDecidesSATWithEncoding_of_operationalTracePrefixSemanticClosure
#print axioms operationalTracePrefixSemanticClosure_of_no_DTMDecidesSATWithEncoding
#print axioms operationalTracePrefixSemanticClosure_iff_no_DTMDecidesSATWithEncoding

end PallLean.Paper93.DeepMath.PathB
