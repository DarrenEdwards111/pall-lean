import Mathlib
import PallLean.TseitinOBDD

/-!
# Expander Graphs → HasGoodCut

Proves infrastructure for showing d-regular edge-expander graphs satisfy HasGoodCut.

Right-side connectivity IS essential (GF2 satisfiability needs connected graph).
The approach: choose k small enough that removing k edges preserves connectivity
(via expansion), while still creating enough split vertices.
-/

open Finset BigOperators

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
theorem expander_right_connected (G : Tseitin.RegularGraph)
    (ε : ℕ) (hε : ε ≥ 1)
    (h_expand : IsEdgeExpander G ε)
    (h_conn : ∀ u v, RightReachable G 0 u v)
    (hn : G.numVertices ≥ 2)
    (k : ℕ) (hk_small : k < ε)
    (hk_le : k ≤ G.numEdges) :
    ∀ u v, RightReachable G k u v := by
  sorry

end TseitinOBDD
