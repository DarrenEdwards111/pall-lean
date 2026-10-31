import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTranscriptInfoCap

/-!
# Building blocks for a cumulative-novelty measure, and two risks they expose

The transcript cap (`transcriptInfo_le`) showed that *static* information of the input is `≤ n`.  The
proposed way forward is a **cumulative** measure — how often the computation creates and discards
distinctions among possibilities.  Before defining such a measure in full, this file records a few
*proved facts* about two candidate building-block quantities, and the risks they flag.  It does not
attempt a definition, and it does not claim any measure succeeds or fails.

## Proved facts

* `cumulativeNovelty` / `cumulativeNovelty_le_time` — the number of *distinct configurations* visited
  in `[0,T]` is `≤ T+1`.  A quantity read off a single trajectory this way is bounded by time.
* `crossInputNovelty_le_input_entropy` — the number of distinct transcripts at a cut, as the length-`n`
  input varies (`transcriptSupport`), is `≤ 2^n`.
* `crossInputNovelty_le_capacity` — the same count is `≤ (2|State|+1)^T`.

## Two risks these facts expose (risks, not verdicts)

* **Risk from Risk-A quantities.**  A per-trajectory count like distinct configurations is bounded by
  time.  *Being bounded by time is not a defect* — it is exactly the soundness (size-domination) half
  a valid invariant needs.  The open question it leaves is whether a time-bounded novelty quantity
  can *also* be forced high on SAT.  For `cumulativeNovelty` specifically we prove only the upper
  bound `≤ T+1`; we do not show it is high on SAT, nor that it cannot be.
* **Risk from cross-input counts.**  The distinct-transcript count is bounded by `2^n`, a ceiling
  that could obstruct superpolynomial-in-`n` growth.  Note the `(2|State|+1)^T` bound is only an
  *upper* bound; it does **not** establish that this count exceeds time or fails size-domination —
  that would require a lower bound, which is not proved here.

These are cautions to respect when designing a cumulative measure.  They do **not** constitute a
dichotomy, do **not** show the measure equals time or the separation, and do **not** rule out a
hybrid time-bounded cumulative measure.  A time-bounded measure that is also provably high on SAT
remains the open target.

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

variable {M : Machine}

/-- The number of *distinct configurations* visited in `[0,T]`. -/
noncomputable def cumulativeNovelty (M : Machine) (c : Cfg M) (T : ℕ) : ℕ :=
  letI := Classical.decEq (Cfg M)
  ((Finset.range (T + 1)).image (fun t => run M t c)).card

/-- The number of distinct configurations visited in `[0,T]` is `≤ T+1`: there are only `T+1` time
steps.  So this per-trajectory quantity is bounded by time — the soundness (size-domination) side of
what an invariant needs.  Whether such a time-bounded quantity can be forced high on SAT is not
addressed here. -/
theorem cumulativeNovelty_le_time (c : Cfg M) (T : ℕ) :
    cumulativeNovelty M c T ≤ T + 1 := by
  classical
  unfold cumulativeNovelty
  exact le_trans Finset.card_image_le (le_of_eq (Finset.card_range _))

/-- The distinct-transcript count at a cut, as the length-`n` input varies, is `≤ 2^n`. -/
theorem crossInputNovelty_le_input_entropy (b T n : ℕ) :
    transcriptSupport M b T n ≤ 2 ^ n :=
  transcriptSupport_le b T n

/-- The same distinct-transcript count is `≤ (2|State|+1)^T`.  This is an upper bound only; it does
not by itself establish that the count exceeds time. -/
theorem crossInputNovelty_le_capacity (b T n : ℕ) :
    transcriptSupport M b T n ≤ (2 * Fintype.card M.State + 1) ^ T :=
  transcriptInfo_le_length b T n

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
