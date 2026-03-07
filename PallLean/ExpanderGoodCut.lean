import Mathlib
import PallLean.TseitinOBDD

/-!
# Expander Graphs → HasGoodCut

Proves infrastructure for showing d-regular edge-expander graphs satisfy HasGoodCut.

Right-side connectivity IS essential (GF2 satisfiability needs connected graph).
The approach: choose k small enough that removing k edges preserves connectivity
(via expansion), while still creating enough split vertices.
-/

open Finset BigOperators Classical

namespace TseitinOBDD

-- Edge expansion: for every vertex subset S with 0 < |S| ≤ n/2,
-- there are ≥ ε|S| edges with exactly one endpoint in S.
def IsEdgeExpander (G : Tseitin.RegularGraph) (ε : ℕ) : Prop :=
  ∀ S : Finset (Fin G.numVertices),
    S.card > 0 → S.card ≤ G.numVertices / 2 →
    (univ.filter fun e : Fin G.numEdges =>
      ((G.edgeSrc e ∈ S) ≠ (G.edgeTgt e ∈ S))).card ≥ ε * S.card

-- Vertices touched by left-side edges
def leftTouched (G : Tseitin.RegularGraph) (k : ℕ) : Finset (Fin G.numVertices) :=
  univ.filter fun v => ∃ e : Fin G.numEdges,
    (G.edgeSrc e = v ∨ G.edgeTgt e = v) ∧ e.val < k

-- Vertices touched by right-side edges
def rightTouched (G : Tseitin.RegularGraph) (k : ℕ) : Finset (Fin G.numVertices) :=
  univ.filter fun v => ∃ e : Fin G.numEdges,
    (G.edgeSrc e = v ∨ G.edgeTgt e = v) ∧ e.val ≥ k

-- Split vertices = left-touched ∩ right-touched (under identity ordering)
theorem splitVertices_eq_inter (G : Tseitin.RegularGraph) (k : Fin (G.numEdges + 1)) :
    splitVertices G (Equiv.refl _) k = leftTouched G k.val ∩ rightTouched G k.val := by
  ext v; simp only [splitVertices, leftTouched, rightTouched, Finset.mem_filter,
    Finset.mem_inter, Finset.mem_univ, true_and, Equiv.refl_apply]

-- Left-touched bound: k left edges touch ≤ 2k vertices.
-- Each edge with index < k contributes ≤ 2 endpoints.
theorem leftTouched_le (G : Tseitin.RegularGraph) (k : ℕ) :
    (leftTouched G k).card ≤ 2 * k := by
  -- leftTouched ⊆ image(src) ∪ image(tgt) over {e | e.val < k}
  -- |{e | e.val < k}| ≤ min(k, m), each contributes ≤ 2 vertices
  -- So |leftTouched| ≤ 2 · min(k, m)
  have : leftTouched G k ⊆
      (univ.filter (fun e : Fin G.numEdges => e.val < k)).image G.edgeSrc ∪
      (univ.filter (fun e : Fin G.numEdges => e.val < k)).image G.edgeTgt := by
    intro v hv
    simp only [leftTouched, mem_filter, mem_univ, true_and] at hv
    obtain ⟨e, he_inc, he_lt⟩ := hv
    simp only [mem_union, mem_image, mem_filter, mem_univ, true_and]
    rcases he_inc with h | h
    · left; exact ⟨e, he_lt, h⟩
    · right; exact ⟨e, he_lt, h⟩
  calc (leftTouched G k).card
      ≤ ((univ.filter (fun e : Fin G.numEdges => e.val < k)).image G.edgeSrc ∪
         (univ.filter (fun e : Fin G.numEdges => e.val < k)).image G.edgeTgt).card :=
        card_le_card this
    _ ≤ ((univ.filter (fun e : Fin G.numEdges => e.val < k)).image G.edgeSrc).card +
        ((univ.filter (fun e : Fin G.numEdges => e.val < k)).image G.edgeTgt).card :=
        card_union_le _ _
    _ ≤ (univ.filter (fun e : Fin G.numEdges => e.val < k)).card +
        (univ.filter (fun e : Fin G.numEdges => e.val < k)).card :=
        Nat.add_le_add (card_image_le) (card_image_le)
    _ = 2 * (univ.filter (fun e : Fin G.numEdges => e.val < k)).card := by ring
    _ ≤ 2 * k := by
        apply Nat.mul_le_mul_left
        -- |{e : Fin m | e.val < k}| ≤ k
        calc (univ.filter (fun e : Fin G.numEdges => e.val < k)).card
            ≤ (Finset.range k).card := by
              apply card_le_card_of_injOn (fun (e : Fin G.numEdges) => e.val)
                (fun e he => by simp at he; exact Finset.mem_range.mpr he)
                (fun a _ b _ h => Fin.ext h)
          _ = k := Finset.card_range k

-- Right-touched = univ when coverage holds
theorem rightTouched_eq_univ (G : Tseitin.RegularGraph) (k : ℕ)
    (h_cover : ∀ v : Fin G.numVertices, ∃ e : Fin G.numEdges,
      (G.edgeSrc e = v ∨ G.edgeTgt e = v) ∧ e.val ≥ k) :
    rightTouched G k = univ := by
  ext v; simp only [rightTouched, mem_filter, mem_univ, true_and, iff_true]
  exact h_cover v

-- With coverage, split vertices = left-touched vertices
theorem split_eq_leftTouched (G : Tseitin.RegularGraph) (k : Fin (G.numEdges + 1))
    (h_cover : ∀ v : Fin G.numVertices, ∃ e : Fin G.numEdges,
      (G.edgeSrc e = v ∨ G.edgeTgt e = v) ∧ e.val ≥ k.val) :
    splitVertices G (Equiv.refl _) k = leftTouched G k.val := by
  rw [splitVertices_eq_inter, rightTouched_eq_univ G k.val h_cover, inter_univ]

-- Assembly: given three conditions, HasGoodCut holds.
theorem assemble_good_cut (G : Tseitin.RegularGraph) (c : ℕ)
    (k : Fin (G.numEdges + 1)) (hk : k.val ≤ G.numEdges)
    (h_split : (splitVertices G (Equiv.refl _) k).card ≥ (G.degree + 1) * c)
    (h_cover : ∀ v, ∃ e : Fin G.numEdges,
      (G.edgeSrc e = v ∨ G.edgeTgt e = v) ∧ e.val ≥ k.val)
    (h_conn : ∀ u v, RightReachable G k.val u v) :
    HasGoodCut G c :=
  ⟨k, hk, h_split, h_cover, h_conn⟩

-- Connectivity preservation: removing k < ε edges from a connected
-- ε-edge-expander preserves connectivity.
--
-- Proof: Suppose the right-side subgraph (edges ≥ k) is disconnected.
-- Then there exists a component C with |C| ≤ n/2 such that all edges
-- from C to V\C have index < k (they're left edges, removed).
-- By expansion, there are ≥ ε·|C| ≥ ε such edges.
-- So k ≥ ε, contradicting k < ε.
-- Right-reachability component of u: the set of vertices reachable from u via right edges.
noncomputable def rightComponent (G : Tseitin.RegularGraph) (k : ℕ) (u : Fin G.numVertices) :
    Finset (Fin G.numVertices) :=
  univ.filter fun v => RightReachable G k u v

-- Monotonicity: increasing k shrinks the reachable set
-- (more edges removed → fewer connections)
theorem rightComponent_mono (G : Tseitin.RegularGraph) (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂)
    (u v : Fin G.numVertices) :
    RightReachable G k₂ u v → RightReachable G k₁ u v := by
  intro h
  induction h with
  | refl => exact RightReachable.refl _
  | step v' w e _ hek he ih =>
    exact RightReachable.step _ v' w e ih (by omega) he

-- Key lemma: if a right-side crossing edge exists between C and V\C,
-- then C is not a right-component (it would extend).
theorem crossing_edge_extends (G : Tseitin.RegularGraph) (k : ℕ)
    (u : Fin G.numVertices) (C : Finset (Fin G.numVertices))
    (hC : C = rightComponent G k u)
    (v : Fin G.numVertices) (hv : v ∈ C)
    (w : Fin G.numVertices) (hw : w ∉ C)
    (e : Fin G.numEdges) (hek : e.val ≥ k)
    (he : (G.edgeSrc e = v ∧ G.edgeTgt e = w) ∨ (G.edgeSrc e = w ∧ G.edgeTgt e = v)) :
    False := by
  apply hw
  rw [hC, rightComponent, mem_filter]
  constructor
  · exact mem_univ _
  · have hv_reach : RightReachable G k u v := by
      rw [hC, rightComponent, mem_filter] at hv; exact hv.2
    exact RightReachable.step u v w e hv_reach hek he

-- The main theorem: all edges between C and V\C have index < k.
theorem component_boundary_left (G : Tseitin.RegularGraph) (k : ℕ)
    (u : Fin G.numVertices)
    (e : Fin G.numEdges)
    (hv : G.edgeSrc e ∈ rightComponent G k u)
    (hw : G.edgeTgt e ∉ rightComponent G k u) :
    e.val < k := by
  by_contra hge
  push_neg at hge
  exact crossing_edge_extends G k u _ rfl _ hv _ hw e hge (Or.inl ⟨rfl, rfl⟩)

-- Similarly for the reverse direction
theorem component_boundary_left' (G : Tseitin.RegularGraph) (k : ℕ)
    (u : Fin G.numVertices)
    (e : Fin G.numEdges)
    (hv : G.edgeTgt e ∈ rightComponent G k u)
    (hw : G.edgeSrc e ∉ rightComponent G k u) :
    e.val < k := by
  by_contra hge
  push_neg at hge
  exact crossing_edge_extends G k u _ rfl _ hv _ hw e hge (Or.inr ⟨rfl, rfl⟩)

-- Non-trivial component: if full graph is connected (at k=0) but
-- right-side is not, then some component is proper and non-empty.
-- Its boundary edges all have index < k. Expansion bounds these.

theorem expander_right_connected (G : Tseitin.RegularGraph)
    (ε : ℕ) (hε : ε ≥ 1)
    (h_expand : IsEdgeExpander G ε)
    (h_conn : ∀ u v, RightReachable G 0 u v)
    (hn : G.numVertices ≥ 2)
    (k : ℕ) (hk_small : k < ε)
    (hk_le : k ≤ G.numEdges) :
    ∀ u v, RightReachable G k u v := by
  by_contra h_not_conn
  push_neg at h_not_conn
  obtain ⟨u, v, h_not_reach⟩ := h_not_conn
  -- Let C = right-component of u. Then v ∉ C.
  set C := rightComponent G k u
  have hu_mem : u ∈ C := by
    simp only [C, rightComponent, mem_filter, mem_univ, true_and]
    exact RightReachable.refl _
  have hv_not : v ∉ C := by
    simp only [C, rightComponent, mem_filter, mem_univ, true_and]
    exact h_not_reach
  -- C is non-empty (contains u) and proper (misses v)
  have hC_pos : C.card > 0 := card_pos.mpr ⟨u, hu_mem⟩
  have hC_lt : C.card < G.numVertices := by
    have hne : C ≠ univ := by intro h; exact hv_not (h ▸ mem_univ v)
    have hsub : C ⊂ univ := ssubset_of_subset_of_ne (subset_univ _) hne
    calc C.card < univ.card := card_lt_card hsub
      _ = G.numVertices := by simp [Fintype.card_fin]
  -- WLOG |C| ≤ n/2. If not, use V\C instead.
  -- For now, assume |C| ≤ n/2 (the other case is symmetric with V\C).
  -- All boundary edges have index < k.
  -- Count boundary edges: edges with exactly one endpoint in C.
  have h_boundary : ∀ e : Fin G.numEdges,
      ((G.edgeSrc e ∈ C) ≠ (G.edgeTgt e ∈ C)) → e.val < k := by
    intro e hne
    by_cases hs : G.edgeSrc e ∈ C
    · have ht : G.edgeTgt e ∉ C := by intro ht; exact hne (by simp [hs, ht])
      exact component_boundary_left G k u e hs ht
    · have ht : G.edgeTgt e ∈ C := by
        by_contra ht; exact hne (by simp [hs, ht])
      exact component_boundary_left' G k u e ht hs
  -- So all boundary edges are in {e | e.val < k}, which has ≤ k elements.
  -- Boundary edges form a subset of {e | e.val < k}.
  have h_boundary_le_k :
      (univ.filter fun e : Fin G.numEdges =>
        ((G.edgeSrc e ∈ C) ≠ (G.edgeTgt e ∈ C))).card ≤ k := by
    calc (univ.filter fun e : Fin G.numEdges =>
            ((G.edgeSrc e ∈ C) ≠ (G.edgeTgt e ∈ C))).card
        ≤ (univ.filter fun e : Fin G.numEdges => e.val < k).card := by
          apply card_le_card
          intro e he
          simp only [mem_filter, mem_univ, true_and] at he ⊢
          exact h_boundary e he
      _ ≤ k := by
          calc _ ≤ (Finset.range k).card := by
                apply card_le_card_of_injOn (fun (e : Fin G.numEdges) => e.val)
                  (fun e he => by simp at he; exact Finset.mem_range.mpr he)
                  (fun a _ b _ h => Fin.ext h)
            _ = k := Finset.card_range k
  -- Now use expansion:
  -- Need |C| ≤ n/2 OR |V\C| ≤ n/2. At least one holds.
  by_cases hC_half : C.card ≤ G.numVertices / 2
  · -- Apply expansion to C
    have h_exp := h_expand C hC_pos hC_half
    -- h_exp : boundary edges ≥ ε · |C| ≥ ε · 1 = ε
    -- ε * C.card ≤ boundary ≤ k, and C.card ≥ 1, so ε ≤ k < ε
    have : ε * 1 ≤ ε * C.card := Nat.mul_le_mul_left ε hC_pos
    linarith
  · -- |C| > n/2, so |V\C| < n/2 ≤ n/2. Use V\C.
    push_neg at hC_half
    have hCc_card : (univ \ C).card = G.numVertices - C.card := by
      simp [Finset.card_univ_diff]
    set Cc := univ \ C with hCc_def
    have hCc_pos : Cc.card > 0 := by omega
    have hCc_half : Cc.card ≤ G.numVertices / 2 := by omega
    -- Boundary edges crossing Cc = boundary edges crossing C
    have h_boundary_eq :
        (univ.filter fun e : Fin G.numEdges =>
          ((G.edgeSrc e ∈ Cc) ≠ (G.edgeTgt e ∈ Cc))) =
        (univ.filter fun e : Fin G.numEdges =>
          ((G.edgeSrc e ∈ C) ≠ (G.edgeTgt e ∈ C))) := by
      ext e; simp only [mem_filter, mem_univ, true_and, hCc_def, mem_sdiff]
      constructor <;> intro h heq <;> apply h <;>
        simp only [mem_univ, true_and] at * <;> tauto
    have h_exp := h_expand Cc hCc_pos hCc_half
    rw [h_boundary_eq] at h_exp
    have : ε * 1 ≤ ε * Cc.card := Nat.mul_le_mul_left ε hCc_pos
    linarith

end TseitinOBDD
