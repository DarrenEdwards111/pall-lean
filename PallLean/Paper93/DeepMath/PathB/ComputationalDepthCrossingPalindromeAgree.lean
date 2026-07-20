import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingPalindrome
import Mathlib.Data.List.GetD

/-!
# Tape agreement of the mixed input with the two references

At the cut `b = |u|-1` (after the prefix `u`), the mixed input `mixInput u u' m` agrees with
`palInput u m` on the left (cells `< |u|`) and with `palInput u' m` on the right (cells `≥ |u|`, when
`|u| = |u'|`).  These are the `getD`-level facts that furnish the splice's initial `SpliceSynced`
condition (`init`'s tape is the input list).

* `mix_agree_left` — for `p < |u|`, `mixInput` and `palInput u` read equally.
* `mix_agree_right` — for `|u| ≤ p` and `|u| = |u'|`, `mixInput` and `palInput u'` read equally.

## What still remains (NOT here)

The acceptance contradiction (assembling the splice + membership + agreement into `crossingSeq`
injective on the `2^i` family) and the `Ω(n)`-cut summation.  This file does **not** claim the `Ω(n²)`
bound (restricted: `crossingCount ≤ time` caps the technique at polynomial, one-tape P `=` P, not
`SAT ∉ P`).

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

/-- **Left agreement.**  Left of the cut (`p < |u|`), the mixed input and `palInput u` read equally
(both are `u` there). -/
theorem mix_agree_left (u u' : List Bool) (m : ℕ) (p : ℕ) (hp : p < u.length) :
    (mixInput u u' m).getD p false = (palInput u m).getD p false := by
  unfold mixInput palInput
  rw [List.append_assoc, List.append_assoc, List.getD_append _ _ _ _ hp,
    List.getD_append _ _ _ _ hp]

/-- **Right agreement.**  Right of the cut (`|u| ≤ p`, `|u| = |u'|`), the mixed input and `palInput u'`
read equally (both are `0ᵐ · u'ᴿ` there). -/
theorem mix_agree_right (u u' : List Bool) (m : ℕ) (hlen : u.length = u'.length) (p : ℕ)
    (hp : u.length ≤ p) :
    (mixInput u u' m).getD p false = (palInput u' m).getD p false := by
  unfold mixInput palInput
  rw [List.append_assoc, List.append_assoc, List.getD_append_right u _ false p hp,
    List.getD_append_right u' _ false p (hlen ▸ hp), hlen]

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
