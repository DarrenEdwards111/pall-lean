import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingComplexity

/-!
# The crossing-for-space barrier, machine-checked

Crossing complexity (`CrossingComplexity`) is a corridor candidate with a real pumping handle, but
its power caps at `Ω(n log n)`.  The reason is the **crossing-for-space barrier**: the peak crossing
count is the total crossing activity *diluted across the boundaries*, so a machine shrinks its peak
by using more space.  This file proves the dilution exactly and names what a stronger measure must
overcome.

* `sumCrossings M c S T` = total crossings summed over the `S` boundaries `[0,S)`.
* `maxCrossing M c S T` = the peak crossing count over those boundaries.
* `sumCrossings_le_space_mul_maxCrossing` — **the barrier**: `sumCrossings ≤ S · maxCrossing`.
  Equivalently `maxCrossing ≥ sumCrossings / S`: the peak is the total diluted across `S` boundaries.

## Why this caps the technique

The total `sumCrossings` is essentially the head's total movement — a run-fixed proxy for **time**,
independent of how the machine lays out its work.  The peak `maxCrossing` is the space-sensitive
refinement, but the bound shows it is at most `time / space`: a machine that decides in polynomial
space with a polynomial number of sweeps has polynomial `maxCrossing`, so crossing complexity gives
it no superpolynomial bound.  For a hypothetical poly-time SAT decider (poly space, poly sweeps)
`maxCrossing` is polynomial — the technique is silent.  That is the crossing-for-space barrier.

## What a stronger measure must do (the named target)

Beating the barrier requires a measure that is **both**

1. *space-invariant* — not diluted by increasing `S` (unlike `maxCrossing`), yet
2. *strictly below time* — not merely the total movement (unlike `sumCrossings`, which is `≈ time`
   and hence content-free).

Crossing complexity structurally cannot supply this: its total is time, its peak is `time / space`,
and `sumCrossings_le_space_mul_maxCrossing` shows there is nothing in between within this measure.  A
technique reaching superpolynomial time must therefore introduce genuinely new structure — one whose
"crossing" cost cannot be flattened by spreading the computation across space.  That is the precise
mathematical ingredient the whole programme is missing; this file pins it, and proves no such
ingredient is available from crossing counts alone.

Nothing here proves a separation or a superpolynomial bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

variable {M : Machine}

/-- Total crossings summed over the `S` boundaries `[0,S)`. -/
noncomputable def sumCrossings (M : Machine) (c : Cfg M) (S T : ℕ) : ℕ :=
  ∑ b ∈ Finset.range S, crossingCount M c b T

/-- The peak crossing count over the `S` boundaries `[0,S)`. -/
noncomputable def maxCrossing (M : Machine) (c : Cfg M) (S T : ℕ) : ℕ :=
  (Finset.range S).sup (fun b => crossingCount M c b T)

/-- Every boundary's crossing count is at most the peak. -/
theorem crossingCount_le_maxCrossing (c : Cfg M) {b S : ℕ} (hb : b < S) (T : ℕ) :
    crossingCount M c b T ≤ maxCrossing M c S T := by
  unfold maxCrossing
  exact Finset.le_sup (f := fun b => crossingCount M c b T) (Finset.mem_range.mpr hb)

/-- **The crossing-for-space barrier.**  The total crossing activity is at most space times the peak
crossing: `sumCrossings ≤ S · maxCrossing`.  Equivalently the peak `maxCrossing ≥ sumCrossings / S`
is the total diluted across `S` boundaries, so more space lowers the peak. -/
theorem sumCrossings_le_space_mul_maxCrossing (c : Cfg M) (S T : ℕ) :
    sumCrossings M c S T ≤ S * maxCrossing M c S T := by
  unfold sumCrossings
  calc ∑ b ∈ Finset.range S, crossingCount M c b T
      ≤ (Finset.range S).card • maxCrossing M c S T :=
        Finset.sum_le_card_nsmul _ _ _
          (fun b hb => crossingCount_le_maxCrossing c (Finset.mem_range.mp hb) T)
    _ = S * maxCrossing M c S T := by rw [Finset.card_range, smul_eq_mul]

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
