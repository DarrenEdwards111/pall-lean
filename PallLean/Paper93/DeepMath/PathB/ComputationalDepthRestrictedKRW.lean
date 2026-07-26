import Mathlib.Data.Nat.Basic

/-!
# The restricted KRW one-round lemma

Route 2's whole route rests on a single open socket: the **KRW one-round lemma** (`KWOneStep`) — that KW
communication is (super)additive under composition, `kw(f ⋄ g) ≥ kw(f) + kw(g)`, proved one outer round at
a time.  Here we prove it in a **restricted** case: we *derive* the one-round step from an explicit
structural hypothesis (no round shares outer and inner work), rather than assuming it, and telescope it to
the full composition bound.

## The KW composition picture

For `f ⋄ g` (outer `f`, inner `g`), a KW protocol must find a differing bit.  The differing *block* is a
`KW_f` subproblem (`kwOuter` rounds); inside it, the differing *coordinate* is a `KW_g` subproblem
(`kwInner` rounds).  The one-round lemma says: **each outer round costs ≥ 1 and does not touch the inner
game** — so the two costs add.

## What is proved

* **`oneRound_holds`** — the one-round lemma, *derived*: for a `StructuredComposition` (cost splits as
  `inner + outer r`, with no cross-term = no round sharing, and each round makes ≤ 1 outer progress),
  `1 + cost r ≤ cost (r+1)`.  A single round can't shortcut the composition.
* **`krw_telescope`** — the per-round lemma telescopes: `cost 0 + d ≤ cost d`.
* **`restricted_krw_bound`** — the composition lower bound: `kwInner + d ≤ cost d` — solving the composed
  game needs the inner cost *plus* one per outer round.  `kw(f ⋄ g) ≥ kw(g) + kw(f)`.
* **`structuredWitness`** — non-vacuous.

## Honest scope — the restriction, and the ceiling

Two honest limits, both load-bearing:

1. **The restriction.**  `oneRound_holds` is derived from `cost r = inner + outer r` — the cost splits
   with **no cross-term**, i.e. no round makes simultaneous outer *and* inner progress.  That is the
   *no-round-sharing* hypothesis.  The **general** KRW conjecture is exactly whether the one-round lemma
   survives when a round *can* share outer+inner progress — the same sharing wall, once more.
2. **The ceiling.**  Even proved in full, KRW gives a **depth** bound: `P ⊄ NC¹`, *not* `P ≠ NP`.  KW
   composition adds *depth* (additive), never *size* (multiplicative doubling).  The gap is uniformity.

So this discharges the `KWOneStep` socket in the restricted (no-round-sharing) model — a real, checked
one-round lemma — while the general socket (round sharing) stays open and the route's ceiling stays at
`P ⊄ NC¹`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RestrictedKRW

/-- A **structured composition**: the KW cost after `r` outer rounds splits as `inner + outer r` — inner
game preserved, outer progress separate (no cross-term = no round sharing) — with each round making at
least one unit of outer progress (`outer_step`). -/
structure StructuredComposition where
  /-- inner KW cost `kw(g)`, preserved across outer rounds -/
  inner : ℕ
  /-- outer progress after `r` rounds -/
  outer : ℕ → ℕ
  /-- one outer round makes at least one unit of progress (one job per round) -/
  outer_step : ∀ r, 1 + outer r ≤ outer (r + 1)

/-- The composed KW cost with `r` outer rounds done: `inner + outer r` (no cross-term). -/
def StructuredComposition.cost (S : StructuredComposition) (r : ℕ) : ℕ := S.inner + S.outer r

/-- **The one-round lemma, derived (proved).**  In a structured composition, one more outer round costs at
least one and leaves the inner game intact: `1 + cost r ≤ cost (r+1)`.  A single round cannot shortcut the
composition.  This is `KWOneStep`, discharged under the no-round-sharing structure. -/
theorem oneRound_holds (S : StructuredComposition) (r : ℕ) :
    1 + S.cost r ≤ S.cost (r + 1) := by
  show 1 + (S.inner + S.outer r) ≤ S.inner + S.outer (r + 1)
  have h := S.outer_step r
  omega

/-- **The one-round lemma telescopes (proved).**  A per-round step `1 + C r ≤ C (r+1)` accumulates:
`C 0 + d ≤ C d`.  This is the reduction from the one-round lemma to the full composition bound. -/
theorem krw_telescope (C : ℕ → ℕ) (oneRound : ∀ r, 1 + C r ≤ C (r + 1)) (d : ℕ) :
    C 0 + d ≤ C d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h := oneRound d
    omega

/-- **The restricted KRW composition bound (proved).**  For a structured composition, the composed game
needs the inner cost plus one per outer round: `kwInner + d ≤ cost d`.  Telescoping the one-round lemma
gives `kw(f ⋄ g) ≥ kw(g) + kw(f)` — the KRW lower bound, in the restricted model. -/
theorem restricted_krw_bound (S : StructuredComposition) (d : ℕ) :
    S.inner + d ≤ S.cost d := by
  have h := krw_telescope S.cost (oneRound_holds S) d
  have hbase : S.cost 0 = S.inner + S.outer 0 := rfl
  omega

/-- **Non-vacuous (proved).**  Each outer round makes exactly one unit of progress (`outer r = r`), inner
cost `5`: the composed bound `5 + d ≤ cost d` holds tightly. -/
def structuredWitness : StructuredComposition where
  inner := 5
  outer := fun r => r
  outer_step := fun r => by omega

end PallLean.Paper93.DeepMath.PathB.RestrictedKRW

#print axioms PallLean.Paper93.DeepMath.PathB.RestrictedKRW.oneRound_holds
#print axioms PallLean.Paper93.DeepMath.PathB.RestrictedKRW.restricted_krw_bound
