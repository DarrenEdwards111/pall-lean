import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingComplexity

/-!
# The palindrome fooling family

Defines the family the splice fools: for a prefix `u`, the palindrome `u · 0ᵐ · uᴿ`, and the mixed
input `u · 0ᵐ · u'ᴿ` (a non-palindrome when `u ≠ u'`).  The splice showed the mixed input follows
`palInput u` on the left and `palInput u'` on the right; so if their crossing sequences agreed, the
mixed input would be accepted despite not being a palindrome — the fooling contradiction, giving `2^i`
distinct crossing sequences at cut `|u|`.

* `IsPalindrome` — `x = xᴿ`.
* `palInput u m` — `u · 0ᵐ · uᴿ`, a palindrome (`palInput_isPalindrome`).
* `mixInput u u' m` — `u · 0ᵐ · u'ᴿ`; not a palindrome when `|u| = |u'|` and `u ≠ u'`
  (`mixInput_not_palindrome`).

## What still remains (NOT here)

The tape-agreement facts (mixInput agrees with `palInput u` left of the cut, with `palInput u'` right
of it), the acceptance contradiction (splice ⇒ mixInput accepted ⇒ contradiction with a decider ⇒
distinct crossing sequences ⇒ `crossingSeq` injective on the family), and the `Ω(n)`-cut summation.
This file does **not** claim the `Ω(n²)` bound (restricted: `crossingCount ≤ time` caps the technique
at polynomial, one-tape P `=` P, not `SAT ∉ P`).

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

/-- A list is a palindrome if it equals its reverse. -/
def IsPalindrome (x : List Bool) : Prop := x = x.reverse

/-- The palindrome family member for prefix `u` with `m` central blanks: `u · 0ᵐ · uᴿ`. -/
def palInput (u : List Bool) (m : ℕ) : List Bool := u ++ List.replicate m false ++ u.reverse

/-- The mixed input: `u`'s left part with `u'`'s reversed right part. -/
def mixInput (u u' : List Bool) (m : ℕ) : List Bool := u ++ List.replicate m false ++ u'.reverse

/-- Each `palInput u m` is a palindrome. -/
theorem palInput_isPalindrome (u : List Bool) (m : ℕ) : IsPalindrome (palInput u m) := by
  simp only [IsPalindrome, palInput, List.reverse_append, List.reverse_reverse,
    List.reverse_replicate, List.append_assoc]

/-- The mixed input `u · 0ᵐ · u'ᴿ` with `|u| = |u'|` and `u ≠ u'` is not a palindrome. -/
theorem mixInput_not_palindrome (u u' : List Bool) (m : ℕ)
    (hlen : u.length = u'.length) (hne : u ≠ u') : ¬ IsPalindrome (mixInput u u' m) := by
  intro hpal
  apply hne
  unfold IsPalindrome mixInput at hpal
  simp only [List.reverse_append, List.reverse_reverse, List.reverse_replicate,
    List.append_assoc] at hpal
  exact List.append_inj_left hpal hlen

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
