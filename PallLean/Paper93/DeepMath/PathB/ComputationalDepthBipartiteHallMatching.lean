import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMatchingRootBound
import Mathlib.Combinatorics.Hall.Basic

/-!
# Matchability from Hall's condition (the matchability half of the expander instance, proved)

The graph-PHP root bound needs **matchability of small pigeon-sets**, and on a bipartite *expander* this comes
from the Hall condition (expansion ⇒ `|N(S')| ≥ |S'|`).  This file proves the general tool via **Mathlib's
Hall marriage theorem** (`Finset.all_card_le_biUnion_card_iff_exists_injective`): the Hall condition on `S`
gives an injective placement of `S` into holes *respecting the bipartite neighbourhoods* — i.e. a matching of
`S` in the graph.

This is the matchability the expander root bound consumes (the complete-bipartite case
`matchable_of_small` is the trivial instance where `N(S') = all holes`); it generalises matchability to any
graph satisfying Hall, expanders included.

## Proved (clean axioms, no `sorry`)

* `exists_placement_of_hall` — if every `S' ⊆ S` has `|S'| ≤ |⋃_{p∈S'} nbr p|` (Hall), then there is an
  injective `f : {p ∈ S} → holes` with `f p ∈ nbr p` for each `p` — a matching of `S` in the bipartite graph.
  Proved by applying Mathlib's Hall theorem on the subtype `{p // p ∈ S}`.

## The irreducible bottom (named, not faked)

A *full unconditional* graph-PHP lower bound needs a concrete bipartite graph with **`n < m` and
unique-neighbour expansion** — every medium pigeon-set has `≥ c|S|` unique-neighbour holes — which gives
*both* the Hall condition (here, via `|∂S| ≥ |S|`) *and* the flip's private holes
(`ComputationalDepthGraphPHPExpansion.lean`).  Such a graph is a **lossless / unique-neighbour expander**
(Capalbo–Reingold–Vadhan–Wigderson; or a Ramanujan bipartite graph).  Its explicit construction and expansion
proof are a deep theorem in their own right — **named here, not formalised**.  With it, `exists_placement_of_hall`
discharges the root bound and the three proved flip cores discharge the width link, closing the lower bound.
So the graph-PHP arc is reduced to exactly one named input: *a unique-neighbour bipartite expander*.
-/

namespace PallLean.Paper93.DeepMath.PathB.PHPProofSpace

open PallLean.Paper93.DeepMath.PathB
open scoped BigOperators

/-- **Matchability from Hall's condition (proved via Mathlib Hall).**  If every subset `S' ⊆ S` has
`|S'| ≤ |⋃_{p ∈ S'} nbr p|`, then there is an injective placement `f` of the pigeons of `S` into holes with
`f p ∈ nbr p` — a matching of `S` in the bipartite graph `nbr`. -/
theorem exists_placement_of_hall {m n : ℕ} (nbr : Fin m → Finset (Fin n)) (S : Finset (Fin m))
    (hall : ∀ S' ⊆ S, S'.card ≤ (S'.biUnion nbr).card) :
    ∃ f : {x // x ∈ S} → Fin n, Function.Injective f ∧ ∀ x, f x ∈ nbr x.val := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun x : {x // x ∈ S} => nbr x.val)).mp
  intro s
  have hsub : s.image (Subtype.val) ⊆ S := by
    intro p hp
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hp
    exact hx ▸ x.2
  have hcard : s.card = (s.image (Subtype.val)).card :=
    (Finset.card_image_of_injective s Subtype.val_injective).symm
  have hbiun : s.biUnion (fun x : {x // x ∈ S} => nbr x.val)
      = (s.image (Subtype.val)).biUnion nbr := by
    rw [Finset.image_biUnion]
  rw [hcard, hbiun]
  exact hall (s.image (Subtype.val)) hsub

end PallLean.Paper93.DeepMath.PathB.PHPProofSpace

#print axioms PallLean.Paper93.DeepMath.PathB.PHPProofSpace.exists_placement_of_hall
