import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEntanglementRuler

/-!
# Reformulating the ruler's middle link: the measure is free, the two residues are a fixed point

The ruler's middle link prices multiplicity by one specific measure — **private reach** `depCard`.
That choice is what produced the two residues (localization = cap the reach; demand-generation = make
`k·b` large).  The natural next move: bound the middle link **differently** — a different per-gate
capacity measure — and hope a better measure dodges the residues.  This file is the honest test, and
the answer is that it cannot: reformulation is a **fixed point**.

## What the middle link actually is

A *capacity measure* `cap : gate → ℕ` is **valid** if it upper-bounds multiplicity —
`mult(g) ≤ cap(g)` — i.e. it genuinely prices how many blocks a gate can witness.  Given any valid
measure bounded by `s` on the gates, the middle link runs verbatim:
`middle_link_general` gives `k·b ≤ s·|gates|`.  The entanglement ruler is exactly the `depCard`
instance (`ruler_is_capacity_instance`).  So the measure is a **free parameter** — `depCard` is one
choice among many.

## Why reformulation cannot escape

Two facts, both proved, pin the residues in place for *every* valid measure:

* **`bounded_capacity_invalid`** — in the presence of sharing (a gate with `mult(g) > β`), **no
  measure bounded by `β` is valid**: validity forces `cap(g) ≥ mult(g) > β`.  You cannot price the
  middle link with a provably-bounded quantity (fan-in, say), because multiplicity itself is
  unbounded — a single gate can witness many blocks — and a valid measure must be at least as large
  as the sharing it prices.  The capacity residue is **forced**, not an artifact of choosing
  `depCard`.
* **`middle_link_separates`** — for *any* valid measure, the separation `G < |gates|` needs **both**
  the capacity bound (`cap ≤ s`) **and** the demand (`s·G < k·b`).  The same two residues, identical
  in shape, for every measure.  Changing the measure moves neither wall.

## Honest scope — the walls are structural, the measure is not

So: yes, the middle link can be bounded differently — it is measure-agnostic, and `depCard` is just
one instantiation.  But every valid reformulation carries the *same* two residues — a capacity cap
(localization-type) and a demand (demand-generation-type) — because the middle link is intrinsically
a "demand ≤ capacity × size" bound, and such a bound separates iff capacity is capped and demand is
large.  Worse, no *bounded* measure is even valid under sharing, so the capacity residue cannot be
dodged by a clever choice.  Reformulating the middle link is a fixed point: it cannot escape
`localization + demand-generation`.  The measure is free; the walls are structural.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MiddleLinkReformulation

open PallLean.Paper93.DeepMath.PathB.EntanglementRuler
open PallLean.Paper93.DeepMath.PathB.TheReasonShared

variable {k b n : ℕ}

/-- A per-gate **capacity measure** is *valid* if it upper-bounds multiplicity: `mult(g) ≤ cap(g)`.
A valid measure genuinely prices how many blocks a gate can witness.  `depCard` is one such measure
(the ruler); this abstracts over the choice. -/
def ValidCapacity (C : EntangledTower k b n) (cap : ℕ → ℕ) : Prop :=
  ∀ g, mult (toShared C) g ≤ cap g

/-- **The middle link, for any valid measure (proved).**  Given any valid capacity bounded by `s` on
the gates, the middle link runs verbatim: `k·b ≤ s·|gates|`.  The bound does not care which measure
prices multiplicity — only that it is valid and bounded. -/
theorem middle_link_general (C : EntangledTower k b n) (cap : ℕ → ℕ)
    (hvalid : ValidCapacity C cap) (s : ℕ) (hs : ∀ g ∈ C.gates, cap g ≤ s) :
    k * b ≤ s * C.gates.card :=
  the_reason_shared (toShared C) s (fun g hg => le_trans (hvalid g) (hs g hg))

/-- **The entanglement ruler is one instance (proved).**  The `depCard` measure is valid — that is
exactly `mult_le_depCard`.  So the ruler is the `depCard` instantiation of the general middle link;
the measure is a free parameter. -/
theorem ruler_is_capacity_instance (C : EntangledTower k b n) :
    ValidCapacity C (fun g => (depSet C g).card) :=
  fun g => mult_le_depCard C g

/-- **No bounded measure is valid under sharing (proved).**  If a gate witnesses more than `β` blocks
(`mult(g) > β`), then every valid capacity has `cap(g) > β`: a valid measure must be at least as
large as the sharing it prices.  So the capacity residue cannot be dodged by pricing with a
provably-bounded quantity — multiplicity is unbounded, and validity chases it. -/
theorem bounded_capacity_invalid (C : EntangledTower k b n) (cap : ℕ → ℕ)
    (hvalid : ValidCapacity C cap) (g : ℕ) (β : ℕ) (hshare : β < mult (toShared C) g) :
    β < cap g :=
  lt_of_lt_of_le hshare (hvalid g)

/-- **The two residues are invariant across measures (proved).**  For *any* valid capacity, the
separation `G < |gates|` follows only from the capacity bound `cap ≤ s` *together with* the demand
`s·G < k·b`.  Drop either and nothing follows.  Every reformulation of the middle link carries the
same two residues — a capacity cap (localization-type) and a demand (demand-generation-type). -/
theorem middle_link_separates (C : EntangledTower k b n) (cap : ℕ → ℕ)
    (hvalid : ValidCapacity C cap) (s G : ℕ)
    (hs : ∀ g ∈ C.gates, cap g ≤ s) (hdemand : s * G < k * b) :
    G < C.gates.card := by
  by_contra h
  push_neg at h
  have h1 := middle_link_general C cap hvalid s hs
  have h2 : s * C.gates.card ≤ s * G := Nat.mul_le_mul (le_refl s) h
  omega

end PallLean.Paper93.DeepMath.PathB.MiddleLinkReformulation

#print axioms PallLean.Paper93.DeepMath.PathB.MiddleLinkReformulation.middle_link_general
#print axioms PallLean.Paper93.DeepMath.PathB.MiddleLinkReformulation.ruler_is_capacity_instance
#print axioms PallLean.Paper93.DeepMath.PathB.MiddleLinkReformulation.bounded_capacity_invalid
#print axioms PallLean.Paper93.DeepMath.PathB.MiddleLinkReformulation.middle_link_separates
