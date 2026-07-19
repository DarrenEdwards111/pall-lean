import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingInfoBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingEnergy

/-!
# The crossing-transcript information candidate — and its cap (a no-go)

A candidate stronger than raw crossing energy: weight crossings by the *novelty* of the information
they carry, via the **crossing transcript** — the ordered sequence of `(control state, direction)`
symbols at the crossings of a boundary.  This file defines it, connects it to the existing crossing
framework, and — as a stress test — proves its **information ceiling**, which kills raw transcript
entropy as an observer invariant.

## The candidate and its bridge to what we built

* `crossingTranscript` — the `(state, went-right?)` symbol at each crossing of `b`, in time order.
* `crossingTranscript_length` — its length is exactly `crossingCount b` (no reset artefact: it maps
  over the actual crossing times).
* `crossingEnergy_eq_transcript_length_sq` — the bridge: `crossingEnergy = Σ_b (transcript length)²`.
  Energy measures the *volume/concentration* of boundary traffic; transcript information will measure
  the *novelty* inside it.

## The information cap (the no-go)

Fix the machine, boundary `b`, clock `T`.  As the length-`n` input varies, the transcript is a
*function of the input*, so it takes at most `2^n` distinct values:

* `transcriptSupport_le` — `supportSize ≤ 2^n`.
* `transcriptInfo_le` — `transcriptInfo := log₂ supportSize ≤ n`.
* `transcriptInfo_le_length` — also `supportSize ≤ (2|State|+1)^T`, so `transcriptInfo ≤ T·log₂(2|State|+1)`.
* `transcriptInfoAggregate_le` — summed over `S` cuts, `≤ S·n` (`≤ n²` when `S ≤ n`).

**No-go conclusion.**  Ordinary support/Shannon/Rényi information of the fixed input is `≤ n` per
cut, hence polynomially bounded for *every* language — independently of whether SAT ∈ P.  So it can
never be `InvHard` for SAT: a static-information measure cannot separate.  This is the analogue of
"enormous generative unfolding is not enormous new information": a compact rule reuses the same `≤ n`
bits for arbitrarily long computation.

## What this leaves open (not built here)

The cap kills *static* information.  A live candidate would have to measure *cumulative* novelty —
how often the computation creates and discards distinctions among possibilities — without hiding
runtime inside it or becoming representation-dependent.  Defining that is the real difficulty; it is
not attempted here.

Nothing here proves `P ≠ NP`, SAT hardness, or an information-flow lower bound.  It proves the raw
candidate is capped.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

variable {M : Machine}

/-- The crossing transcript: at each crossing of `b` (in time order), the control state and whether
the head ends up on the right of `b` (the crossing direction). -/
noncomputable def crossingTranscript (M : Machine) (c : Cfg M) (b T : ℕ) : List (M.State × Bool) :=
  ((crossingTimes M c b T).sort (· ≤ ·)).map (fun t => ((run M t c).st, decide (b < (run M (t + 1) c).hd)))

/-- The transcript length is the crossing count. -/
theorem crossingTranscript_length (c : Cfg M) (b T : ℕ) :
    (crossingTranscript M c b T).length = crossingCount M c b T := by
  unfold crossingTranscript crossingCount
  rw [List.length_map, Finset.length_sort]

/-- **Bridge to crossing energy.**  `crossingEnergy = Σ_b (transcript length)²` — energy is the
squared transcript length summed over boundaries. -/
theorem crossingEnergy_eq_transcript_length_sq (c : Cfg M) (S T : ℕ) :
    crossingEnergy M c S T = ∑ b ∈ Finset.range S, (crossingTranscript M c b T).length ^ 2 := by
  unfold crossingEnergy
  exact Finset.sum_congr rfl (fun b _ => by rw [crossingTranscript_length])

/-- The number of distinct transcripts at `b` as the length-`n` input varies. -/
noncomputable def transcriptSupport (M : Machine) (b T n : ℕ) : ℕ :=
  (Finset.univ.image (fun x : Fin n → Bool => crossingTranscript M (init M (List.ofFn x)) b T)).card

/-- **Input-entropy cap.**  The transcript is a function of the input, so it takes at most `2^n`
distinct values. -/
theorem transcriptSupport_le (b T n : ℕ) : transcriptSupport M b T n ≤ 2 ^ n := by
  unfold transcriptSupport
  calc (Finset.univ.image _).card ≤ (Finset.univ : Finset (Fin n → Bool)).card := Finset.card_image_le
    _ = 2 ^ n := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- The support information: `log₂` of the number of distinct transcripts. -/
noncomputable def transcriptInfo (M : Machine) (b T n : ℕ) : ℕ :=
  Nat.log 2 (transcriptSupport M b T n)

/-- **The cap (no-go).**  Support information is at most `n` bits — the input entropy — for every
machine and language. -/
theorem transcriptInfo_le (b T n : ℕ) : transcriptInfo M b T n ≤ n := by
  unfold transcriptInfo
  calc Nat.log 2 (transcriptSupport M b T n) ≤ Nat.log 2 (2 ^ n) :=
        Nat.log_mono_right (transcriptSupport_le b T n)
    _ = n := by rw [Nat.log_pow (show (1:ℕ) < 2 by norm_num)]

/-- Transcript symbols also cap the support by transcript length: `supportSize ≤ (2|State|+1)^T`. -/
theorem transcriptInfo_le_length (b T n : ℕ) :
    transcriptSupport M b T n ≤ (2 * Fintype.card M.State + 1) ^ T := by
  unfold transcriptSupport
  have hcard : Fintype.card (M.State × Bool) = 2 * Fintype.card M.State := by
    rw [Fintype.card_prod, Fintype.card_bool]; ring
  have := card_le_of_injOn_bounded_lists (α := M.State × Bool)
    (I := Finset.univ.image (fun x : Fin n → Bool => crossingTranscript M (init M (List.ofFn x)) b T))
    id T (Set.injOn_id _) (by
      intro l hl
      rw [Finset.mem_image] at hl
      obtain ⟨x, _, rfl⟩ := hl
      simp only [id_eq]
      rw [crossingTranscript_length]
      exact crossingCount_le_time _ b T)
  rwa [hcard] at this

/-- **Aggregate cap.**  Summed over `S` cuts, transcript information is `≤ S·n` (so `≤ n²` when
`S ≤ n`). -/
theorem transcriptInfoAggregate_le (T n S : ℕ) :
    ∑ b ∈ Finset.range S, transcriptInfo M b T n ≤ S * n := by
  calc ∑ b ∈ Finset.range S, transcriptInfo M b T n
      ≤ ∑ _b ∈ Finset.range S, n := Finset.sum_le_sum (fun b _ => transcriptInfo_le b T n)
    _ = S * n := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
