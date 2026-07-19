import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTranscriptInfoCap

/-!
# Stress-testing the cumulative-novelty measure (falsify-first, before defining it)

The transcript cap (`transcriptInfo_le`) killed *static* information: it is `≤ n`.  The proposed
escape is a **cumulative** measure — how often the computation creates and discards distinctions
among possibilities — hoped to be time-bounded, simulation-stable, and *not* capped by `n`.  Before
defining it in full we test it against the two traps it must avoid:

* **Trap A (runtime hidden inside it ⇒ content-free).**  If novelty is counted *along a single
  computation*, it is bounded by the number of time steps, so it is `≤` time and gives no leverage
  beyond "time is superpolynomial", i.e. beyond the separation itself.
* **Trap B (not size-dominated).**  To beat Trap A it must aggregate *across inputs* — but then it is
  bounded by the input entropy (`≤ 2^n`) and by the transcript capacity (`≤ (2|State|+1)^T`,
  exponential in `T`), so a raw cross-input count is not `≤` time and fails size-domination.

## The dichotomy, made precise

* `cumulativeNovelty` / `cumulativeNovelty_le_time` — **Trap A horn.**  Per-computation novelty (the
  number of *distinct configurations* visited in `[0,T]`, an upper bound on any per-trajectory count
  of "new distinctions") is `≤ T+1`.  So it is size-dominated, hence content-free: its hardness for
  SAT holds iff time is superpolynomial, i.e. iff SAT ∉ P — no new leverage.
* **Trap B horn** (already proved, cited here): the cross-input distinction count is exactly
  `transcriptSupport`, with `transcriptSupport_le : ≤ 2^n` and
  `transcriptInfo_le_length : ≤ (2|State|+1)^T`.  Bounded by input entropy and exponential in time —
  a raw cross-input count is not size-dominated; capping it at time reintroduces Trap A.

## Verdict

Neither natural reading survives: per-computation cumulative novelty *is* time (content-free);
cross-input cumulative novelty is bounded by static input entropy and is exponential in time (not
size-dominated).  A measure that is simultaneously (i) `≤` poly(time), (ii) not a re-labelling of
time, and (iii) not capped by `n`, must thread between these — and the two natural definitions do
not.  The real object (if it exists) has to count distinctions that are *re-created* across time
without being either a per-step count or a static cross-input count.  This file does **not** claim
such an object exists; it records that the two obvious candidates are dead.

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

variable {M : Machine}

/-- Per-computation cumulative novelty: the number of *distinct configurations* visited in `[0,T]`.
This upper-bounds any per-trajectory count of "new distinctions created" along the computation. -/
noncomputable def cumulativeNovelty (M : Machine) (c : Cfg M) (T : ℕ) : ℕ :=
  letI := Classical.decEq (Cfg M)
  ((Finset.range (T + 1)).image (fun t => run M t c)).card

/-- **Trap A horn.**  Per-computation cumulative novelty is `≤ T+1`: there are only `T+1` time steps,
so at most `T+1` distinct configurations.  Hence it is size-dominated — and therefore content-free:
it is superpolynomial exactly when time is, giving no leverage beyond the separation itself. -/
theorem cumulativeNovelty_le_time (c : Cfg M) (T : ℕ) :
    cumulativeNovelty M c T ≤ T + 1 := by
  classical
  unfold cumulativeNovelty
  exact le_trans Finset.card_image_le (le_of_eq (Finset.card_range _))

/-- **Trap B horn**, as a named restatement: the cross-input distinction count is `transcriptSupport`,
bounded by the input entropy `2^n`. -/
theorem crossInputNovelty_le_input_entropy (b T n : ℕ) :
    transcriptSupport M b T n ≤ 2 ^ n :=
  transcriptSupport_le b T n

/-- **Trap B horn**, capacity side: the cross-input distinction count is exponential in time,
`≤ (2|State|+1)^T`, not `≤` poly(time). -/
theorem crossInputNovelty_le_capacity (b T n : ℕ) :
    transcriptSupport M b T n ≤ (2 * Fintype.card M.State + 1) ^ T :=
  transcriptInfo_le_length b T n

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
