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
structure IndependentChannels (G : ColorGraph) (k : ℕ) (base : Coloring G.numVertices) (c : ℕ)
    extends Fin c → BoundaryChannel G k base where
  -- Channels have distinct Alice vertices
  h_alice_inj : Function.Injective (fun i => (toFun i).alice_vert)
  -- Channels have distinct Bob vertices
  h_bob_inj : Function.Injective (fun i => (toFun i).bob_vert)
  -- Channels have distinct edges
  h_edge_inj : Function.Injective (fun i => (toFun i).edge)
  -- Bob vertices are private: only one crossing edge per Bob vertex
  -- (no other channel's edge touches this Bob vertex)
  h_bob_private : ∀ i (e : Fin G.numEdges),
    G.edgeSrc e = (toFun i).bob_vert ∨ G.edgeTgt e = (toFun i).bob_vert →
    e = (toFun i).edge
  -- Base coloring assigns color 2 to all channel Bob vertices
  h_base_bob : ∀ i, base ((toFun i).bob_vert) = 2
  -- Alice and Bob vertices are disjoint
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
  -- Abbreviations
  let ch := channels.channels
  let alice_ends := fun i => (ch i).alice_vert
  let verts := fun i => (ch i).bob_vert
  let edgs := fun i => (ch i).edge

  -- Alice assignment: bitColor at channel vertices, base elsewhere
  let mkAlice (n : Fin (2 ^ c)) : Fin k → Fin 3 := fun v =>
    if h : ∃ i : Fin c, alice_ends i = ⟨v.val, by omega⟩
    then bitColor n.val h.choose.val
    else base ⟨v.val, by omega⟩

  -- Bob distinguisher: base except v_p = bitColor(n₁, p)
  let mkBob (p : Fin c) (n₁ : Fin (2 ^ c)) : Fin (G.numVertices - k) → Fin 3 := fun w =>
    if h : ∃ i : Fin c, i = p ∧ verts i = ⟨w.val + k, by omega⟩
    then bitColor n₁.val p.val
    else base ⟨w.val + k, by omega⟩

  refine ⟨mkAlice, fun n₁ n₂ hne => ?_⟩
  obtain ⟨p, hp⟩ := bits_differ_of_ne n₁.isLt n₂.isLt (Fin.val_ne_of_ne hne)
  refine ⟨mkBob p n₁, ?_⟩

  set col₁ : Fin G.numVertices → Fin 3 := fun v =>
    if h : v.val < k then mkAlice n₁ ⟨v.val, h⟩
    else (mkBob p n₁) ⟨v.val - k, by omega⟩
  set col₂ : Fin G.numVertices → Fin 3 := fun v =>
    if h : v.val < k then mkAlice n₂ ⟨v.val, h⟩
    else (mkBob p n₁) ⟨v.val - k, by omega⟩

  suffices h1 : isProper G col₁ = false by
    suffices h2 : isProper G col₂ = true by
      simp only [threeColFun]; rw [h1, h2]; decide
    -- isProper G col₂ = true: all edges properly colored
    rw [isProper_iff]
    intro e
    -- Classify edge e
    by_cases he : ∃ i : Fin c, e = edgs i
    · -- e is a channel edge
      obtain ⟨i, rfl⟩ := he
      rw [(ch i).h_src, (ch i).h_tgt]
      -- col₂ at alice = bitColor n₂ i
      have h_alice_col : col₂ (alice_ends i) = bitColor n₂.val i.val := by
        simp only [col₂, dif_pos (ch i).h_alice_lt, mkAlice]
        have hex : ∃ j : Fin c, alice_ends j = ⟨(alice_ends i).val, by omega⟩ :=
          ⟨i, by ext; rfl⟩
        rw [dif_pos hex]
        congr 1
        exact channels.h_alice_inj (by ext; exact Fin.val_eq_of_eq hex.choose_spec)
      -- col₂ at bob = bitColor n₁ p (if i = p) or base(verts i) = 2 (if i ≠ p)
      have h_bob_col : col₂ (verts i) =
          if i = p then bitColor n₁.val p.val else (2 : Fin 3) := by
        simp only [col₂]
        have hge : ¬ (verts i).val < k := by omega
        rw [dif_neg hge]
        show mkBob p n₁ ⟨(verts i).val - k, by omega⟩ = _
        simp only [mkBob]
        by_cases hip : i = p
        · subst hip
          have hex : ∃ j : Fin c, j = p ∧ verts j = ⟨(verts p).val - k + k, by omega⟩ :=
            ⟨p, rfl, by ext; omega⟩
          rw [dif_pos hex, if_pos rfl]
        · have hnex : ¬∃ j : Fin c, j = p ∧ verts j = ⟨(verts i).val - k + k, by omega⟩ := by
            rintro ⟨j, rfl, hj⟩; exact hip (channels.h_bob_inj (by ext; omega))
          rw [dif_neg hnex, if_neg hip]
      rw [h_alice_col, h_bob_col]
      split
      · exact hp.symm  -- i = p: bitColor n₂ p ≠ bitColor n₁ p
      · -- i ≠ p: bitColor n₂ i ≠ 2
        intro h_eq; rcases bitColor_zero_or_one n₂.val i.val with h | h <;> simp [h] at h_eq
    · -- e is not a channel edge
      push_neg at he
      -- Determine what col₂ gives at each endpoint
      -- Key: neither endpoint is a channel Bob vertex (by h_bob_private)
      have h_not_bob : ∀ i, G.edgeSrc e ≠ verts i ∧ G.edgeTgt e ≠ verts i := by
        intro i; constructor
        · intro heq; exact he i (channels.h_bob_private i e (Or.inl heq))
        · intro heq; exact he i (channels.h_bob_private i e (Or.inr heq))
      -- For endpoints on Alice's side: if it's a channel Alice vertex,
      -- col₂ = bitColor; if not, col₂ = base.
      -- For endpoints on Bob's side: col₂ = base (not a channel Bob vertex,
      -- and not v_p since h_not_bob).
      -- Sub-case: is source a channel Alice vertex?
      -- We need to show the edge is proper regardless.

      -- Helper: col₂ at any non-channel-Alice, non-channel-Bob vertex = base
      have col₂_base_at (v : Fin G.numVertices)
          (h_not_a : ∀ i, v ≠ alice_ends i) (h_not_b : ∀ i, v ≠ verts i) :
          col₂ v = base v := by
        simp only [col₂]
        by_cases hv : v.val < k
        · rw [dif_pos hv]; show mkAlice n₂ ⟨v.val, hv⟩ = _
          simp only [mkAlice]
          have : ¬∃ i : Fin c, alice_ends i = ⟨v.val, by omega⟩ := by
            rintro ⟨i, hi⟩; exact h_not_a i (by ext; exact Fin.val_eq_of_eq hi)
          rw [dif_neg this]
        · rw [dif_neg hv]; show mkBob p n₁ ⟨v.val - k, by omega⟩ = _
          simp only [mkBob]
          have : ¬∃ i : Fin c, i = p ∧ verts i = ⟨v.val - k + k, by omega⟩ := by
            rintro ⟨i, _, hi⟩; exact h_not_b i (by ext; omega)
          rw [dif_neg this]

      -- Helper: col₂ at a channel Alice vertex = bitColor
      have col₂_at_alice (i : Fin c) : col₂ (alice_ends i) = bitColor n₂.val i.val := by
        simp only [col₂, dif_pos (ch i).h_alice_lt, mkAlice]
        have hex : ∃ j : Fin c, alice_ends j = ⟨(alice_ends i).val, by omega⟩ :=
          ⟨i, by ext; rfl⟩
        rw [dif_pos hex]; congr 1
        exact channels.h_alice_inj (by ext; exact Fin.val_eq_of_eq hex.choose_spec)

      -- Now case split: is source or target a channel Alice vertex?
      by_cases h_src_ch : ∃ i, G.edgeSrc e = alice_ends i
      · -- Source is a channel Alice vertex
        obtain ⟨i, hi_src⟩ := h_src_ch
        -- Target is NOT a channel Bob vertex (h_not_bob)
        -- Is target on Alice's side or Bob's side?
        by_cases h_tgt_lt : (G.edgeTgt e).val < k
        · -- Target on Alice's side: h_alice_controlled says base(tgt) = 2
          have h_tgt_2 : base (G.edgeTgt e) = 2 :=
            (ch i).h_alice_controlled e hi_src h_tgt_lt
          -- Is target a channel Alice vertex?
          by_cases h_tgt_ch : ∃ j, G.edgeTgt e = alice_ends j
          · -- Both endpoints are channel Alice vertices
            obtain ⟨j, hj_tgt⟩ := h_tgt_ch
            rw [hi_src, hj_tgt, col₂_at_alice i, col₂_at_alice j]
            -- bitColor n₂ i ∈ {0,1} and bitColor n₂ j ∈ {0,1}
            -- Need i ≠ j (edges have no self-loops, and src ≠ tgt)
            -- Actually this doesn't help: bitColor could be same for i and j
            -- But wait: base(tgt) = base(alice_ends j) = 2, and base is proper,
            -- and the edge connects alice_ends i to alice_ends j.
            -- base(alice_ends i) ≠ base(alice_ends j) by base proper.
            -- base(alice_ends j) = 2, so base(alice_ends i) ≠ 2.
            -- Hmm, but we're not using base colors at these vertices...
            -- We changed both to bitColor values. This could conflict!
            -- e.g., bitColor n₂ i = 0 and bitColor n₂ j = 0 → monochromatic
            --
            -- This is a real problem. Two channel Alice vertices that are
            -- adjacent could both get the same bitColor value.
            -- FIX: add hypothesis that channel Alice vertices are pairwise non-adjacent.
            sorry
          · -- Target is not a channel vertex: col₂(tgt) = base(tgt) = 2
            rw [hi_src, col₂_at_alice i]
            have : col₂ (G.edgeTgt e) = base (G.edgeTgt e) := by
              push_neg at h_tgt_ch
              exact col₂_base_at _ h_tgt_ch (fun j => (h_not_bob j).2)
            rw [this, h_tgt_2]
            -- bitColor n₂ i ∈ {0,1} ≠ 2
            rcases bitColor_zero_or_one n₂.val i.val with h | h <;> simp [h]
        · -- Target on Bob's side: this is a crossing edge from alice_vert(i) to Bob
          -- By h_alice_only_crossing, e = channel edge of i
          have : e = edgs i := (ch i).h_alice_only_crossing e (Or.inl ⟨hi_src, by omega⟩)
          exact absurd this (he i)
      · -- Source is NOT a channel Alice vertex
        by_cases h_tgt_ch : ∃ i, G.edgeTgt e = alice_ends i
        · -- Target is a channel Alice vertex, source is not
          obtain ⟨i, hi_tgt⟩ := h_tgt_ch
          by_cases h_src_lt : (G.edgeSrc e).val < k
          · -- Source on Alice's side: h_alice_controlled' says base(src) = 2
            have h_src_2 : base (G.edgeSrc e) = 2 :=
              (ch i).h_alice_controlled' e hi_tgt h_src_lt
            push_neg at h_src_ch
            have : col₂ (G.edgeSrc e) = base (G.edgeSrc e) :=
              col₂_base_at _ h_src_ch (fun j => (h_not_bob j).1)
            rw [hi_tgt, this, h_src_2, col₂_at_alice i]
            rcases bitColor_zero_or_one n₂.val i.val with h | h <;> simp [h]
          · -- Source on Bob's side: crossing edge to alice_vert(i)
            have : e = edgs i := (ch i).h_alice_only_crossing e (Or.inr ⟨hi_tgt, by omega⟩)
            exact absurd this (he i)
        · -- Neither endpoint is a channel vertex → both get base → proper
          push_neg at h_src_ch h_tgt_ch
          rw [col₂_base_at _ h_src_ch (fun j => (h_not_bob j).1),
              col₂_base_at _ h_tgt_ch (fun j => (h_not_bob j).2)]
          exact (isProper_iff G base).mp h_base_proper e
  -- isProper G col₁ = false: edge p is monochromatic
  apply isProper_false_of_mono G col₁ (edgs p)
  have hsrc : col₁ (G.edgeSrc (edgs p)) = bitColor n₁.val p.val := by
    rw [(ch p).h_src]; simp only [col₁, dif_pos (ch p).h_alice_lt, mkAlice]
    have hex : ∃ j : Fin c, alice_ends j = ⟨(alice_ends p).val, by omega⟩ :=
      ⟨p, by ext; rfl⟩
    rw [dif_pos hex]; congr 1
    exact channels.h_alice_inj (by ext; exact Fin.val_eq_of_eq hex.choose_spec)
  have htgt : col₁ (G.edgeTgt (edgs p)) = bitColor n₁.val p.val := by
    rw [(ch p).h_tgt]; simp only [col₁]
    have hge : ¬(verts p).val < k := by omega
    rw [dif_neg hge]; show mkBob p n₁ ⟨(verts p).val - k, by omega⟩ = _
    simp only [mkBob]
    have hex : ∃ j : Fin c, j = p ∧ verts j = ⟨(verts p).val - k + k, by omega⟩ :=
      ⟨p, rfl, by ext; omega⟩
    rw [dif_pos hex]
  rw [hsrc, htgt]

/-! ## 4. Gap: Adjacent Channel Alice Vertices

The proof above has ONE sorry: when two channel Alice vertices are adjacent,
both get bitColor values, which could match → monochromatic.

**Fix**: Add `h_alice_nonadj` to `IndependentIsolatedChannels`:
```
h_alice_nonadj : ∀ i j, i ≠ j → ∀ e,
  ¬(G.edgeSrc e = (channels i).alice_vert ∧ G.edgeTgt e = (channels j).alice_vert)
```

This is the SAME hypothesis Darren suggested earlier. It's needed because:
- In a proper base coloring, adjacent Alice channel vertices have different colors
- But we REPLACE those colors with bitColor values, losing the base constraint
- Without non-adjacency, two adjacent channel vertices could both get color 0

The palette gadget naturally provides this: each w_i is connected to p₂ and v_i only,
so w_i and w_j are never adjacent (they share p₂ as a common neighbor but have
no direct edge between them).

### Summary of Required Hypotheses (Minimal)

For a clean, provable residual explosion theorem on 3-coloring:

1. **c channel Alice vertices** with pairwise non-adjacent constraint
2. **Each channel Alice vertex**: all Alice-side neighbors have base color 2
3. **Each channel Alice vertex**: only crossing edge is the channel edge
4. **c channel Bob vertices**: degree 1 (only the channel edge)
5. **Base coloring**: proper, color 2 on all channel Bob vertices

These are satisfiable by the palette gadget construction:
- w_i is a new vertex with edges to p₂ (Alice-side, color 2) and v_i (Bob-side)
- w_i has degree 2, not degree 1, but its ALICE-SIDE neighbor (p₂) has color 2 ✓
- w_i vertices are pairwise non-adjacent ✓ (no edge between any w_i, w_j)
- h_alice_only_crossing: w_i's only crossing edge is (w_i, v_i) ✓
- v_i needs degree 1: this is the strong condition, requires graph extraction
-/

/-! ## 5. Status

### This file:
- `BoundaryChannel`, `IsolatedChannel` structures: clean abstractions ✓
- `isolated_channel_residual_explosion`: 1 sorry (adjacent Alice channel vertices)
  - Fix: add h_alice_nonadj → 0 sorry

### Architecture:
- Layer 1a: `coloring_residual_explosion_independent` (NPvsLpoly.lean) — 0 sorry ✅
- Layer 1b: `isolated_channel_residual_explosion` (this file) — 1 sorry, fixable
- Layer 2: graph extraction from expanders — OPEN RESEARCH QUESTION
  - Need: large family of edges in expander matching where Bob endpoints have degree 1
    and Alice endpoints are non-adjacent with controlled neighborhoods
  - Palette gadget gives non-adjacency + controlled neighborhoods for FREE
  - Remaining hard part: Bob-side degree-1 (or Bob-boundary)
-/

end BoundaryGadget
