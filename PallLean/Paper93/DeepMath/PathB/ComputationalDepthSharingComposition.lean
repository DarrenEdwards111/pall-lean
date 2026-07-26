import Mathlib.Data.Nat.Basic

/-!
# Removing the no-sharing restriction on the composition lemma = facing cost_super

The restricted KRW one-round lemma (`RestrictedKRW`) was *derived* from a no-cross-term structure — no
round shares outer and inner work.  Removing that restriction means allowing a round to make **simultaneous
outer + inner progress** — protocol-level *sharing* / mass production.  That is the general KRW conjecture,
and it is **open**.  This file does not prove it (nothing can, in-model).  It proves the honest thing: the
restriction is **load-bearing** — removing it reduces *exactly* to bounding the sharing, i.e. to
`cost_super`.

## The general composition, with a sharing term

A `GeneralComposition` keeps the outer progress `outer r` and inner cost `inner`, but adds a **sharing
term** `cross r` — the accumulated savings from rounds that did double duty (outer *and* inner at once).
The invariant `cost r + cross r = inner + outer r` says the true cost is `inner + outer − cross`: sharing
*discounts* the additive bound.  `cross ≡ 0` recovers the restricted (no-sharing) case.

## What is proved

* **`oneRound_iff_bounded`** — per round, the one-round lemma `1 + cost r ≤ cost (r+1)` holds **iff** the
  sharing increment stays within the outer slack: `1 + cross (r+1) + outer r ≤ cross r + outer (r+1)`.
* **`general_lemma_iff_bounded_sharing`** — globally: the general one-round lemma holds **iff** sharing is
  bounded.  Removing the restriction = proving `BoundedSharing`.
* **`unbounded_sharing_breaks`** — the restriction is load-bearing: a concrete composition where each round
  shares one unit (`cross r = r`, tight `outer`) makes the cost **flat** (`cost ≡ 5`), and the one-round
  lemma is **false** — `¬ (1 + cost 0 ≤ cost 1)`.  Unbounded sharing collapses the KRW bound.

## Honest scope — removing the restriction IS the wall

`general_lemma_iff_bounded_sharing` shows the general one-round lemma is *equivalent* to `BoundedSharing`
— no round can absorb outer progress into the inner game.  That is exactly *no mass production* in the
protocol, i.e. `cost_super` in the KW/communication setting.  And `unbounded_sharing_breaks` proves the
restriction cannot be dropped for free: when sharing is unbounded, the one-round lemma is not merely
unproven, it is **false**.  So "remove the no-sharing restriction" does not simplify to a lemma we can
prove — it *is* the wall, in a sixth costume.  We have not removed it; we have proved that removing it is
`cost_super`.  (And even removing it yields only `P ⊄ NC¹`, not `P ≠ NP` — the depth ceiling stands.)
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SharingComposition

/-- A **general composition** with a protocol-level **sharing** term.  `cross r` accumulates the savings
from rounds that advance outer *and* inner at once; the invariant `cost r + cross r = inner + outer r`
makes `cost = inner + outer − cross`.  `cross ≡ 0` is the restricted no-sharing case. -/
structure GeneralComposition where
  /-- inner KW cost -/
  inner : ℕ
  /-- outer progress after `r` rounds -/
  outer : ℕ → ℕ
  /-- accumulated sharing savings (mass production in the protocol) -/
  cross : ℕ → ℕ
  /-- the composed cost -/
  cost : ℕ → ℕ
  /-- cost = inner + outer − cross (additive form) -/
  invariant : ∀ r, cost r + cross r = inner + outer r

/-- The general one-round lemma: each round grows the cost by at least one. -/
def OneRoundLemma (S : GeneralComposition) : Prop := ∀ r, 1 + S.cost r ≤ S.cost (r + 1)

/-- Bounded sharing: per round, the sharing increment stays within the outer slack — no round absorbs
outer progress into the inner game.  This is *no mass production* in the protocol. -/
def BoundedSharing (S : GeneralComposition) : Prop :=
  ∀ r, 1 + S.cross (r + 1) + S.outer r ≤ S.cross r + S.outer (r + 1)

/-- **The one-round step ⟺ bounded sharing (proved).**  Per round, `1 + cost r ≤ cost (r+1)` holds iff the
sharing increment stays within the outer slack.  With no cross-term this is automatic; with sharing it is
a real condition. -/
theorem oneRound_iff_bounded (S : GeneralComposition) (r : ℕ) :
    (1 + S.cost r ≤ S.cost (r + 1)) ↔
      (1 + S.cross (r + 1) + S.outer r ≤ S.cross r + S.outer (r + 1)) := by
  have h1 := S.invariant r
  have h2 := S.invariant (r + 1)
  omega

/-- **Removing the restriction ⟺ bounding the sharing (proved).**  The general one-round lemma holds iff
sharing is bounded.  So dropping the no-sharing hypothesis reduces *exactly* to proving `BoundedSharing` —
no mass production in the protocol = `cost_super` in the KW setting. -/
theorem general_lemma_iff_bounded_sharing (S : GeneralComposition) :
    OneRoundLemma S ↔ BoundedSharing S := by
  constructor
  · intro h r
    exact (oneRound_iff_bounded S r).mp (h r)
  · intro h r
    exact (oneRound_iff_bounded S r).mpr (h r)

/-- A composition where every round shares one unit (`cross r = r`, tight `outer r = r`): the sharing
exactly cancels the outer progress, so the cost is **flat**. -/
def unboundedSharingWitness : GeneralComposition where
  inner := 5
  outer := fun r => r
  cross := fun r => r
  cost := fun _ => 5
  invariant := fun r => by simp

/-- **The restriction is load-bearing (proved).**  Under unbounded sharing the cost is flat (`cost ≡ 5`),
and the one-round lemma is **false**: `¬ (1 + cost 0 ≤ cost 1)` (i.e. `¬ (6 ≤ 5)`).  Unbounded sharing
collapses the KRW composition bound — the no-sharing hypothesis cannot be dropped for free. -/
theorem unbounded_sharing_breaks :
    ¬ (1 + unboundedSharingWitness.cost 0 ≤ unboundedSharingWitness.cost 1) := by
  show ¬ (1 + 5 ≤ 5)
  omega

end PallLean.Paper93.DeepMath.PathB.SharingComposition

#print axioms PallLean.Paper93.DeepMath.PathB.SharingComposition.general_lemma_iff_bounded_sharing
#print axioms PallLean.Paper93.DeepMath.PathB.SharingComposition.unbounded_sharing_breaks
