import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingInfoBound

/-!
# The counting half of the palindrome bound — and an honest correction on the fooling

The `Ω(n²)` bound has two remaining pieces: **fooling** (many distinct crossing sequences at a cut)
and **counting** (few crossings ⇒ few sequences).  This file lands the counting cleanly and states
the fooling precisely — including a correction to an earlier over-optimistic claim.

## Counting (proved)

* `crossing_pigeonhole` — the contrapositive of `crossing_info_capacity`: if a family of computations
  has pairwise-distinct crossing sequences at `b` and more than `(|State|+1)^K` members, then some
  member crosses `b` **more than `K`** times.  So `2^i` distinct crossing sequences at cut `i` force
  some computation to cross `i / log₂(|State|+1)` times there.

## Fooling (the honest remaining piece — corrected)

The fooling is *not* just the contrapositive of the determinism theorem, as previously suggested.
`determinism_recursive` proves **right-side** determinism: equal crossing sequence + equal *right*
tape ⇒ equal right behaviour.  The palindrome fooling needs to show the `2^i` prefix-inputs
`x_u = u·0…·uᴿ` have pairwise-distinct crossing sequences at cut `i`.  Suppose two agree; the
contradiction comes from the **mixed input** `u·0…·u'ᴿ` (a non-palindrome that must be rejected):
one shows its computation *splices* `x_u`'s left excursions with `x_{u'}`'s right excursions and
therefore accepts.  Establishing that splice — that the mixed input's actual computation matches
`x_u` on the left and `x_{u'}` on the right and carries the shared crossing sequence — is a
*mixed-input joint induction* comparing one computation against two references.  It is strictly more
than the one-sided determinism proved so far (it needs the left-side determinism too, and the
acceptance-location bookkeeping).  That splice, the concrete palindrome family, and the summation
over `Ω(n)` cuts are the remaining work; this file does **not** claim the `Ω(n²)` bound.

Ceiling unchanged: even finished, an unconditional *restricted* result (`crossingCount ≤ time` caps
the technique at polynomial; one-tape P `=` P), not `SAT ∉ P`.

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

variable {M : Machine}

/-- **Counting pigeonhole.**  A family with pairwise-distinct crossing sequences at `b` and more than
`(|State|+1)^K` members contains a computation that crosses `b` more than `K` times.  (Contrapositive
of `crossing_info_capacity`: at most `(|State|+1)^K` distinct crossing sequences use `≤ K` crossings.)
-/
theorem crossing_pigeonhole (b T K : ℕ) (I : Finset (Cfg M))
    (hinj : Set.InjOn (fun c => crossingSeq M c b T) ↑I)
    (hcard : (Fintype.card M.State + 1) ^ K < I.card) :
    ∃ c ∈ I, K < crossingCount M c b T := by
  by_contra hcon
  push_neg at hcon
  have hcap := crossing_info_capacity b T K I hinj hcon
  omega

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
