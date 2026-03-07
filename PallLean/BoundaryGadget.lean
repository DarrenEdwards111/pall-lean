import Mathlib
import PallLean.NPvsLpoly

/-!
# Boundary Channel Gadgets for 3-Coloring

## Architecture

Layer 1 (`coloring_residual_explosion_independent`) proves residual explosion
under degree-1 independence. That hypothesis is too strong for d-regular expanders.

This file defines:
1. **Boundary channels**: a weakened independence condition (palette-controlled
   Alice side, Bob-side isolated from other Bob vertices)
2. **Residual explosion from channels**: the core theorem under weakened hypotheses
3. **Channel extraction interface**: what a graph family must provide

## Key Weakening

Instead of degree-1 everywhere, we require:
- **Alice side**: every Alice-side neighbor of the channel vertex has base color 2.
  Since bitColor ∈ {0,1}, changing the channel vertex to 0 or 1 never conflicts.
  This is achievable via a palette triangle gadget.
- **Bob side**: the channel's Bob vertex has no Bob-side neighbors (all its edges
  cross the cut). This is weaker than degree-1 (allows multiple Alice-side neighbors)
  but still restricts the Bob vertex.

## Gadget Design (Not Formalized Here)

The **palette gadget** for 3-coloring:
- Add a palette triangle P = {p₀, p₁, p₂} (colors 0, 1, 2 in any proper 3-coloring)
- For each crossing edge (u, v) in a matching M:
  - Add new vertex w connected to p₂ and v only
  - w is forced to {0,1} (since w ≠ p₂ = 2)
  - w has degree 2: one Alice-internal edge, one crossing edge
  - w's Alice-side neighbor (p₂) has color 2 ✓

This does NOT modify the original graph's edges — it ADDS new vertices and edges.
The reduction: G is 3-colorable ↔ G + gadgets is 3-colorable (since the gadget
vertices are determined by the original coloring).

The NP-hardness of the gadgetized problem follows from the original problem
being NP-hard and the gadget being a polynomial-time reduction.
-/

open Finset

namespace BoundaryGadget

open NPvsLpoly

/-! ## 1. Boundary Channel Structure -/

/-- A boundary channel: a private crossing edge with controlled neighborhoods.
    Weaker than degree-1: allows Alice-side neighbors if they have base color 2,
    and allows Bob-side vertex to have multiple Alice-side neighbors. -/
structure BoundaryChannel (G : ColorGraph) (k : ℕ) (base : Coloring G.numVertices) where
  alice_vert : Fin G.numVertices    -- Channel vertex on Alice's side
  bob_vert : Fin G.numVertices      -- Channel vertex on Bob's side
  edge : Fin G.numEdges             -- The crossing edge
  h_alice_lt : alice_vert.val < k
  h_bob_ge : bob_vert.val ≥ k
  h_src : G.edgeSrc edge = alice_vert
  h_tgt : G.edgeTgt edge = bob_vert
  -- Alice-side neighbors of alice_vert all have base color 2
  h_alice_controlled : ∀ e : Fin G.numEdges,
    G.edgeSrc e = alice_vert → (G.edgeTgt e).val < k → base (G.edgeTgt e) = 2
  h_alice_controlled' : ∀ e : Fin G.numEdges,
    G.edgeTgt e = alice_vert → (G.edgeSrc e).val < k → base (G.edgeSrc e) = 2
  -- Bob vertex has no Bob-side neighbors (all edges cross the cut)
  h_bob_boundary : ∀ e : Fin G.numEdges,
    G.edgeSrc e = bob_vert → (G.edgeTgt e).val < k
  h_bob_boundary' : ∀ e : Fin G.numEdges,
    G.edgeTgt e = bob_vert → (G.edgeSrc e).val < k

/-- A family of c independent boundary channels. -/
structure IndependentChannels (G : ColorGraph) (k : ℕ) (base : Coloring G.numVertices) (c : ℕ) where
  toFun : Fin c → BoundaryChannel G k base
  h_alice_inj : Function.Injective (fun i => (toFun i).alice_vert)
  h_bob_inj : Function.Injective (fun i => (toFun i).bob_vert)
  h_edge_inj : Function.Injective (fun i => (toFun i).edge)
  h_bob_private : ∀ i (e : Fin G.numEdges),
    G.edgeSrc e = (toFun i).bob_vert ∨ G.edgeTgt e = (toFun i).bob_vert →
    e = (toFun i).edge
  h_base_bob : ∀ i, base ((toFun i).bob_vert) = 2
  h_disj : ∀ i j, (toFun i).alice_vert ≠ (toFun j).bob_vert

/-! ## 2. Residual Explosion from Independent Channels -/

/-- The core theorem: independent boundary channels yield exponentially many
    distinct residuals. This is WEAKER than `coloring_residual_explosion_independent`
    in its hypotheses (palette-controlled instead of degree-1 on Alice side). -/
theorem channel_residual_explosion
    (G : ColorGraph) (k : ℕ) (hk : k ≤ G.numVertices) (c : ℕ)
    (base : Coloring G.numVertices)
    (h_base_proper : isProper G base = true)
    (channels : IndependentChannels G k base c) :
    ∃ (assign : Fin (2 ^ c) → (Fin k → Fin 3)),
      ∀ i j : Fin (2 ^ c), i ≠ j →
        ∃ (bob_col : Fin (G.numVertices - k) → Fin 3),
          threeColFun G (fun v =>
            if h : v.val < k then (assign i) ⟨v.val, h⟩
            else bob_col ⟨v.val - k, by omega⟩) ≠
          threeColFun G (fun v =>
            if h : v.val < k then (assign j) ⟨v.val, h⟩
            else bob_col ⟨v.val - k, by omega⟩) := by
  -- Construction follows the same pattern as coloring_residual_explosion_independent:
  -- Alice assignment n: bitColor(n, i) at channel alice vertices, base elsewhere
  -- Bob distinguisher: base everywhere except v_p = bitColor(n₁, p)
  --
  -- The proof adapts directly:
  -- 1. col₁ is false: edge p monochromatic (bitColor n₁ p on both sides)
  -- 2. col₂ is true:
  --    a. Private edge p: bitColor n₂ p ≠ bitColor n₁ p ✓
  --    b. Private edge i≠p: bitColor n₂ i ∈ {0,1} ≠ 2 = base(bob_vert i) ✓
  --    c. Left edges touching alice_vert i: neighbor has base color 2,
  --       bitColor ∈ {0,1}, so 0 ≠ 2 and 1 ≠ 2 ✓ [h_alice_controlled]
  --    d. Left edges not touching any alice_vert: base coloring → proper ✓
  --    e. Right edges: no Bob channel vertex has Bob-side neighbors
  --       [h_bob_boundary], and we only changed v_p, so right edges
  --       not touching v_p see base → proper ✓
  --    f. Crossing edges not in our family: if touching alice_vert i,
  --       the other endpoint is on Bob's side with base color.
  --       bitColor(n₂, i) ∈ {0,1} ≠ base(other) is NOT guaranteed.
  --       This needs: base color of non-channel Bob neighbors of alice_vert i
  --       is neither 0 nor 1, i.e., is 2. But h_alice_controlled only
  --       covers Alice-side neighbors, not Bob-side ones.
  --
  -- GAP: crossing edges from alice_vert(i) to non-channel Bob vertices
  -- could have base color 0 or 1 on the Bob side. Changing alice_vert(i)
  -- from base to bitColor might make these edges monochromatic.
  --
  -- RESOLUTION: strengthen h_alice_controlled to also cover Bob-side
  -- neighbors, OR require alice_vert(i) to have no non-channel crossing
  -- edges, OR require base(alice_vert i) ∈ {0,1} so the original
  -- coloring already uses {0,1} and the change preserves properness.
  sorry

/-! ## 3. Strengthened Channel: Full Isolation

To close the gap above, we add: the channel's Alice vertex has no
non-channel crossing edges. Combined with h_alice_controlled (Alice-side
neighbors have color 2), this means the ONLY way alice_vert(i) interacts
with Bob's side is through its channel edge. -/

/-- Fully isolated boundary channel: Alice vertex's only crossing edge
    is the channel edge, and all Alice-side neighbors have base color 2. -/
structure IsolatedChannel (G : ColorGraph) (k : ℕ) (base : Coloring G.numVertices)
    extends BoundaryChannel G k base where
  -- Alice vertex's only crossing edge is the channel edge
  h_alice_only_crossing : ∀ e : Fin G.numEdges,
    (G.edgeSrc e = alice_vert ∧ (G.edgeTgt e).val ≥ k) ∨
    (G.edgeTgt e = alice_vert ∧ (G.edgeSrc e).val ≥ k) →
    e = edge

/-- Independent family of fully isolated channels. -/
structure IndependentIsolatedChannels (G : ColorGraph) (k : ℕ)
    (base : Coloring G.numVertices) (c : ℕ) where
  channels : Fin c → IsolatedChannel G k base
  h_alice_inj : Function.Injective (fun i => (channels i).alice_vert)
  h_bob_inj : Function.Injective (fun i => (channels i).bob_vert)
  h_edge_inj : Function.Injective (fun i => (channels i).edge)
  h_bob_private : ∀ i (e : Fin G.numEdges),
    G.edgeSrc e = (channels i).bob_vert ∨ G.edgeTgt e = (channels i).bob_vert →
    e = (channels i).edge
  h_base_bob : ∀ i, base ((channels i).bob_vert) = 2
  h_disj : ∀ i j, (channels i).alice_vert ≠ (channels j).bob_vert
  -- Channel Alice vertices are pairwise non-adjacent
  h_alice_nonadj : ∀ i j, i ≠ j → ∀ e : Fin G.numEdges,
    ¬(G.edgeSrc e = (channels i).alice_vert ∧ G.edgeTgt e = (channels j).alice_vert)

/-- Residual explosion from fully isolated channels. This is provable
    with the same technique as coloring_residual_explosion_independent. -/
theorem isolated_channel_residual_explosion
    (G : ColorGraph) (k : ℕ) (hk : k ≤ G.numVertices) (c : ℕ)
    (base : Coloring G.numVertices)
    (h_base_proper : isProper G base = true)
    (channels : IndependentIsolatedChannels G k base c) :
    ∃ (assign : Fin (2 ^ c) → (Fin k → Fin 3)),
      ∀ i j : Fin (2 ^ c), i ≠ j →
        ∃ (bob_col : Fin (G.numVertices - k) → Fin 3),
          threeColFun G (fun v =>
            if h : v.val < k then (assign i) ⟨v.val, h⟩
            else bob_col ⟨v.val - k, by omega⟩) ≠
          threeColFun G (fun v =>
            if h : v.val < k then (assign j) ⟨v.val, h⟩
            else bob_col ⟨v.val - k, by omega⟩) := by
  -- The proof follows the same structure as coloring_residual_explosion_independent
  -- in NPvsLpoly.lean, adapted for the weaker IsolatedChannel hypotheses.
  -- The key differences:
  -- 1. Alice-side edges: h_alice_controlled ensures bitColor ∈ {0,1} ≠ 2 = base(neighbor)
  -- 2. Crossing edges: h_alice_only_crossing ensures no non-channel crossing edges
  -- 3. Adjacent Alice channels: h_alice_nonadj prevents monochromatic channel-channel edges
  --
  -- The proof is mechanically identical to coloring_residual_explosion_independent
  -- with these substitutions, but requires re-proving all Fin plumbing for Lean 4.28.
  -- We sorry this for now and focus on the extraction conjecture.
  sorry


/-! ## 4. Locally Frozen Channels — The Realistic Target

The degree-1 and IsolatedChannel conditions are too strong for d-regular expanders.
The correct weakening is **locally frozen channels**: crossing edges whose endpoints
have palette freedom under a base coloring, with disjoint radius-1 neighbourhoods.

### Conceptual Shift

For a crossing edge e_i = (u_i, v_i), we do NOT need degree 1. We need:
1. Relative to a base coloring χ₀, changing u_i's color keeps all its
   non-channel incident edges proper.
2. These local recolorings do not force recolorings on other channels.

This is **one-vertex freedom under frozen neighbourhoods**.

### The Two-Part Decomposition

**Part A: Geometric Separation**
From a good cut in a bounded-degree expander, extract a linear-sized family of
crossing edges whose closed 1-neighbourhoods are pairwise disjoint.

In a d-regular graph: a good cut has ≥ εn crossing edges. A maximal matching
gives ≥ εn/d matched edges. Thinning for radius-1 disjointness loses at most
a factor of (2d)² (each matched vertex has ≤ d neighbours, each with ≤ d neighbours).
So we get ≥ εn/(4d³) edges with disjoint N₁ balls. For d = O(1), this is Ω(n).

**Part B: Local Palette Control**
For each selected edge (u_i, v_i) with disjoint N₁ balls, show there exists
a proper base coloring where:
- u_i has ≥ 2 available colors not used by its non-channel neighbours
- v_i has ≥ 2 available colors not used by its non-channel neighbours
- These constraints are independent across channels (by disjointness)

Since N₁ balls are disjoint, local coloring choices don't interfere. Each ball
is a bounded-size subgraph (≤ d² + d + 1 vertices), so a proper 3-coloring
with the desired palette freedom exists by a local extension argument.

### Formal Statement -/

/-- A locally frozen channel: a crossing edge where both endpoints have
    2-color freedom under the base coloring, with the freedom colors
    disjoint from the base colors of non-channel neighbours. -/
structure FrozenChannel (G : ColorGraph) (k : ℕ) (base : Coloring G.numVertices) where
  alice_vert : Fin G.numVertices
  bob_vert : Fin G.numVertices
  edge : Fin G.numEdges
  h_alice_lt : alice_vert.val < k
  h_bob_ge : bob_vert.val ≥ k
  h_src : G.edgeSrc edge = alice_vert
  h_tgt : G.edgeTgt edge = bob_vert
  -- Alice endpoint: for any color c ∈ {0,1}, recoloring alice_vert to c
  -- keeps all non-channel edges incident to alice_vert proper.
  -- This means: no non-channel neighbour of alice_vert has color 0 or 1.
  -- Equivalently: all neighbours of alice_vert (other than bob_vert via edge)
  -- have base color 2.
  h_alice_free : ∀ e' : Fin G.numEdges, e' ≠ edge →
    (G.edgeSrc e' = alice_vert → base (G.edgeTgt e') = 2) ∧
    (G.edgeTgt e' = alice_vert → base (G.edgeSrc e') = 2)
  -- Bob endpoint: same condition. All neighbours other than alice_vert have color 2.
  h_bob_free : ∀ e' : Fin G.numEdges, e' ≠ edge →
    (G.edgeSrc e' = bob_vert → base (G.edgeTgt e') = 2) ∧
    (G.edgeTgt e' = bob_vert → base (G.edgeSrc e') = 2)

/-- Independent family of locally frozen channels with pairwise disjoint
    radius-1 neighbourhoods. -/
structure IndependentFrozenChannels (G : ColorGraph) (k : ℕ)
    (base : Coloring G.numVertices) (c : ℕ) where
  channels : Fin c → FrozenChannel G k base
  h_alice_inj : Function.Injective (fun i => (channels i).alice_vert)
  h_bob_inj : Function.Injective (fun i => (channels i).bob_vert)
  h_edge_inj : Function.Injective (fun i => (channels i).edge)
  h_base_bob : ∀ i, base ((channels i).bob_vert) = 2
  h_disj : ∀ i j, (channels i).alice_vert ≠ (channels j).bob_vert
  -- Radius-1 disjointness: no edge connects a vertex in channel i's
  -- neighbourhood to a vertex in channel j's neighbourhood (i ≠ j).
  -- This is stronger than vertex disjointness — it ensures complete
  -- independence of local recoloring.
  h_r1_disjoint : ∀ i j, i ≠ j → ∀ e : Fin G.numEdges,
    ¬((G.edgeSrc e = (channels i).alice_vert ∨ G.edgeSrc e = (channels i).bob_vert) ∧
      (G.edgeTgt e = (channels j).alice_vert ∨ G.edgeTgt e = (channels j).bob_vert))

/-- The realistic Layer 2 extraction conjecture:
    bounded-degree expanders have Ω(n) locally frozen channels. -/
def FrozenExtractionHypothesis : Prop :=
  ∀ C : ℕ, ∃ n₀ : ℕ, ∀ (G : ColorGraph),
    G.numVertices ≥ n₀ →
    ∃ (c : ℕ) (k : ℕ) (hk : k ≤ G.numVertices)
      (base : Coloring G.numVertices),
      2 ^ c > G.numVertices ^ C ∧
      isProper G base = true ∧
      ∃ channels : IndependentFrozenChannels G k base c, True

/-! ## 5. Frozen Channels → Residual Explosion

The core theorem: frozen channels with disjoint R₁ balls yield
exponentially many distinct residuals.

The proof is cleaner than the IsolatedChannel version because:
- h_alice_free and h_bob_free directly give properness at recolored vertices
- h_r1_disjoint prevents interaction between channels
- No need for h_alice_only_crossing or h_bob_boundary as separate conditions
-/

theorem frozen_channel_residual_explosion
    (G : ColorGraph) (k : ℕ) (hk : k ≤ G.numVertices) (c : ℕ)
    (base : Coloring G.numVertices)
    (h_base_proper : isProper G base = true)
    (channels : IndependentFrozenChannels G k base c) :
    ∃ (assign : Fin (2 ^ c) → (Fin k → Fin 3)),
      ∀ i j : Fin (2 ^ c), i ≠ j →
        ∃ (bob_col : Fin (G.numVertices - k) → Fin 3),
          threeColFun G (fun v =>
            if h : v.val < k then (assign i) ⟨v.val, h⟩
            else bob_col ⟨v.val - k, by omega⟩) ≠
          threeColFun G (fun v =>
            if h : v.val < k then (assign j) ⟨v.val, h⟩
            else bob_col ⟨v.val - k, by omega⟩) := by
  -- The proof structure:
  -- mkAlice n: bitColor(n, i) at channel alice_vert(i), base elsewhere
  -- mkBob p n₁: bitColor(n₁, p) at channel bob_vert(p), base elsewhere
  --
  -- col₁ is false: channel edge p has both endpoints = bitColor(n₁, p) → monochromatic
  --
  -- col₂ is true: for each edge e,
  --   Case 1: e is channel edge i
  --     - src = bitColor(n₂, i), tgt = bitColor(n₁, p) or base(bob) = 2
  --     - if i = p: bitColor(n₂, p) ≠ bitColor(n₁, p) by hp ✓
  --     - if i ≠ p: bitColor(n₂, i) ∈ {0,1} ≠ 2 ✓
  --   Case 2: e is incident to channel alice_vert(i) but not a channel edge
  --     - By h_alice_free: other endpoint has base color 2
  --     - bitColor(n₂, i) ∈ {0,1} ≠ 2 ✓
  --   Case 3: e is incident to channel bob_vert(i) but not a channel edge
  --     - By h_bob_free: other endpoint has base color 2
  --     - If i = p: bitColor(n₁, p) ∈ {0,1} ≠ 2 ✓
  --     - If i ≠ p: base(bob_vert(i)) = 2, other endpoint has base color 2
  --       Wait — base(bob_vert(i)) = 2 and other endpoint has color 2 → monochromatic!
  --       This would be a problem. But h_bob_free says non-channel neighbours have
  --       color 2, and the base coloring is PROPER, so base(bob_vert(i)) ≠ 2 for
  --       any vertex adjacent to one with color 2... unless bob_vert(i) also has color 2.
  --       In fact h_base_bob says base(bob_vert(i)) = 2. So bob_vert(i) has color 2
  --       and all its non-channel neighbours have color 2 — that contradicts base proper!
  --       Unless bob_vert(i) has NO non-channel neighbours, i.e., its only edge is the
  --       channel edge. That's exactly the degree-1 condition on Bob's side.
  --
  -- INSIGHT: h_bob_free + h_base_bob + h_base_proper forces bob_vert to have degree 1.
  -- The "frozen channel" condition on Bob's side COLLAPSES to degree-1 when
  -- base(bob_vert) = 2 and base is proper. The freedom comes from Alice's side only.
  --
  -- This means the realistic target is:
  -- - Alice side: frozen (neighbours have color 2, free to use {0,1})
  -- - Bob side: degree-1 (only the channel edge)
  -- Which is exactly what IsolatedChannel provides.
  sorry

/-! ## 6. Honest Status

### Architecture:
- `FrozenChannel`, `IndependentFrozenChannels`: realistic target structures
- `FrozenExtractionHypothesis`: precise Layer 2 conjecture
- `frozen_channel_residual_explosion`: sorry (collapses to IsolatedChannel case)

### Key Insight Discovered During Formalization:
The "locally frozen" condition on Bob's side is vacuous when combined with
h_base_bob (base color 2) and h_base_proper (proper coloring). A vertex
with color 2 whose non-channel neighbours all have color 2 violates properness
unless it has no non-channel neighbours (degree 1). So the **real weakening
is Alice-side only**: Alice endpoints can have controlled neighbours, but
Bob endpoints must still be degree-1 or have no same-side neighbours.

This simplifies the conjecture: we need to extract a matching where
- Bob endpoints have degree 1 (or all edges cross the cut)
- Alice endpoints have disjoint, palette-controlled neighbourhoods

The degree-1 constraint on Bob is equivalent to: each Bob endpoint's
only edge is the channel edge. In a d-regular graph, this requires
either subdivision (rejected: makes graph bipartite) or working with
a graph family that naturally has such vertices (e.g., after gadget reduction).
-/

end BoundaryGadget
