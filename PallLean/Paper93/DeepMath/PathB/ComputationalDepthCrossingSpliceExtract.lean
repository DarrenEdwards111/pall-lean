import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingSpliceIterate
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingRecursive

/-!
# Splice crossing-time extraction

Reads a concrete `SpliceStep` off a computation's actual crossing times, using the `firstExitTime` /
`firstEntryTime` primitives (and their specs) from the right-side determinism.  These are the steps
that instantiate `splice_iterate`'s `γ` from a real mixed computation.

* `extract_splice_step_right` — at a rightward crossing (head `b+1`), extract the right-phase
  `SpliceStep`: `z`/`x_R` exit at `z`'s first exit time `d`, `x_L` at its first exit time `e`; given
  the leftward-crossing states agree, a `SpliceStep` (right branch) results.
* `extract_splice_step_left` — at a leftward crossing (head `b`), extract the left-phase `SpliceStep`
  dually, via first *entry* times.

## What still remains (NOT here)

The recursive assembly of these into `γ` (chaining alternately, with the base case of the initial left
excursion from head `0` to the first rightward crossing), the crossing-sequence hypothesis
`C(x_L) = C(x_R)` supplying each step's state agreement, the concrete palindrome family, and the
`Ω(n)`-cut summation are the remaining work; this file does **not** claim the `Ω(n²)` bound (restricted:
`crossingCount ≤ time` caps the technique at polynomial, one-tape P `=` P, not `SAT ∉ P`).

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- **Extract a right-phase `SpliceStep`.**  At a rightward crossing, `z`/`x_R` advance to `z`'s first
exit and `x_L` to its own first exit; given the leftward-crossing states agree, this is a `SpliceStep`. -/
theorem extract_splice_step_right (M : Machine) (b : ℕ) (z xL xR : Cfg M)
    (hz_entry : z.hd = b + 1)
    (hz_exit : ∃ t, (run M t z).hd ≤ b)
    (hxL_exit : ∃ t, (run M t xL).hd ≤ b)
    (hstate : (run M (firstExitTime M b xL) xL).st = (run M (firstExitTime M b z) xR).st) :
    SpliceStep M b z xL xR (run M (firstExitTime M b z) z) (run M (firstExitTime M b xL) xL)
      (run M (firstExitTime M b z) xR) := by
  refine Or.inl ⟨firstExitTime M b z, firstExitTime M b xL, hz_entry, ?_, ?_, ?_, ?_, hstate, rfl, rfl, rfl⟩
  · exact (firstExitTime_spec M b z hz_exit).1
  · exact (firstExitTime_spec M b z hz_exit).2
  · exact (firstExitTime_spec M b xL hxL_exit).1
  · exact (firstExitTime_spec M b xL hxL_exit).2

/-- **Extract a left-phase `SpliceStep`.**  At a leftward crossing, `z`/`x_L` advance to `z`'s first
re-entry and `x_R` to its own first re-entry; given the rightward-crossing states agree, this is a
`SpliceStep`. -/
theorem extract_splice_step_left (M : Machine) (b : ℕ) (z xL xR : Cfg M)
    (hz_entry : z.hd = b)
    (hz_reentry : ∃ t, b < (run M t z).hd)
    (hxR_reentry : ∃ t, b < (run M t xR).hd)
    (hstate : (run M (firstEntryTime M b z) xL).st = (run M (firstEntryTime M b xR) xR).st) :
    SpliceStep M b z xL xR (run M (firstEntryTime M b z) z) (run M (firstEntryTime M b z) xL)
      (run M (firstEntryTime M b xR) xR) := by
  refine Or.inr ⟨firstEntryTime M b z, firstEntryTime M b xR, hz_entry, ?_, ?_, ?_, ?_, hstate, rfl, rfl, rfl⟩
  · exact (firstEntryTime_spec M b z hz_reentry).1
  · exact (firstEntryTime_spec M b z hz_reentry).2
  · exact (firstEntryTime_spec M b xR hxR_reentry).1
  · exact (firstEntryTime_spec M b xR hxR_reentry).2

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
