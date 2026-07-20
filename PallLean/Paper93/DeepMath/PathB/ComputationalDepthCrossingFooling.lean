import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingPalindromeAgree

/-!
# The fooling logic: distinct family members have distinct crossing sequences

Assembles the palindrome membership facts with the two remaining connections into the fooling
injectivity.  The fooling *logic* is proved here; the one substantive connection it rests on — that
equal crossing sequences force the mixed input to be accepted (the splice's acceptance consequence) —
is taken as an explicit hypothesis, `hsplice`, because bridging it needs two things this file does not
carry out: relating the crossing-sequence equality to the per-step `SpliceData` state agreements, and
relating the config-level splice (`splice_recursive`) to acceptance at the halt.

* `palindrome_fooling` — for `u ≠ u'` (`|u| = |u'|`): given decider correctness on the mixed input
  (`acc → IsPalindrome`) and the splice consequence (`hsplice : cs(x_u) = cs(x_{u'}) → acc(mixed)`),
  the crossing sequences differ: `cs (palInput u m) ≠ cs (palInput u' m)`.

Instantiated with `acc = "M accepts"` and `cs = crossingSeq M (init M ·) b T`, this is exactly
`crossingSeq` injective on the family — the input to `crossing_pigeonhole` for the `Ω(n²)` summation.

## What still remains (NOT here)

`hsplice` itself (the splice ⇒ acceptance connection: `crossingSeq` equality ⇒ `SpliceData` ⇒
`splice_recursive` ⇒ mixed accepts at the halt), and the `Ω(n)`-cut summation via `crossing_pigeonhole`.
This file does **not** claim the `Ω(n²)` bound (restricted: `crossingCount ≤ time` caps the technique at
polynomial, one-tape P `=` P, not `SAT ∉ P`).

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

/-- **The fooling.**  Two distinct, equal-length prefixes give palindrome family members with distinct
crossing sequences: if they agreed, the splice (`hsplice`) would force the mixed input accepted, but a
correct decider rejects the non-palindrome mixed input (`mixInput_not_palindrome`). -/
theorem palindrome_fooling {α : Type} (acc : List Bool → Prop) (cs : List Bool → α)
    (u u' : List Bool) (m : ℕ) (hlen : u.length = u'.length) (hne : u ≠ u')
    (hdec_mix : acc (mixInput u u' m) → IsPalindrome (mixInput u u' m))
    (hsplice : cs (palInput u m) = cs (palInput u' m) → acc (mixInput u u' m)) :
    cs (palInput u m) ≠ cs (palInput u' m) := by
  intro hcs
  exact mixInput_not_palindrome u u' m hlen hne (hdec_mix (hsplice hcs))

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
