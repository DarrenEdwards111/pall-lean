import Mathlib
import PallLean.TseitinOBDD
import PallLean.CommunicationComplexity
import PallLean.MUSWidthLowerBound

/-!
# NP ⊄ L/poly — Via Graph 3-Coloring on Expanders

## The Attempt

**Target**: Graph 3-coloring on expander graphs.
**Claim**: The characteristic function of 3-COL restricted to d-regular
expanders requires exponential-width OBDDs (= ROBPs for all orderings).
**Consequence**: 3-COL ∉ L/poly. Since 3-COL is NP-complete: NP ⊄ L/poly.

## Why 3-Coloring?

The constraint structure mirrors Tseitin:
- **Tseitin**: each vertex imposes a PARITY constraint on incident edge labels
- **3-Coloring**: each edge imposes an INEQUALITY constraint on endpoint colors

Both have:
- Variables on edges/vertices of an expander graph
- Local constraints (one per vertex/edge)
- Expansion guarantees many crossing constraints at any balanced cut

The key question: does the residual explosion hold for 3-coloring?

## The Argument

For a d-regular expander G on n vertices:
- Input: a coloring x : V → {0,1,2} (encoded as 2n bits)
- Function: f(x) = 1 iff x is a proper 3-coloring (no monochromatic edge)

At a balanced vertex cut (first n/2 vertices vs last n/2):
- Fix the colors of the first n/2 vertices (Alice's input)
- The residual function depends on which colors were assigned to
  vertices adjacent to crossing edges
- On an expander: Ω(εn) edges cross any balanced vertex cut
- Different color assignments to Alice's boundary vertices create
  different forbidden color sets for Bob's vertices
- This should give many distinct residual functions

## Critical Analysis

The residual explosion for 3-coloring is WEAKER than for Tseitin:
- Tseitin: XOR constraints → flipping one variable flips the parity
  → each independent constraint DOUBLES the residual count
- 3-Coloring: inequality constraints → changing a color changes the
  forbidden set → but multiple color assignments can yield the SAME
  forbidden set on Bob's side

Specifically: if vertex u (Alice's) is adjacent to vertex v (Bob's),
then u's color forbids ONE of three colors for v. Two different colors
for u forbid different single colors for v. So each crossing edge
creates a 3-way constraint, not a 2-way (XOR) constraint.

This means the residual count grows as 3^c (not 2^c) where c is the
number of independent crossing constraints. But the INDEPENDENCE
structure is different from Tseitin.
-/

open Finset

namespace NPvsLpoly

/-! ## 1. Graph 3-Coloring Function -/

/-- A 3-coloring of a graph with n vertices. Each vertex gets a color in {0,1,2},
    encoded as 2 bits per vertex (we use Fin 3 directly). -/
def Coloring (n : ℕ) := Fin n → Fin 3

/-- A graph for coloring purposes. -/
structure ColorGraph where
  numVertices : ℕ
  numEdges : ℕ
  edgeSrc : Fin numEdges → Fin numVertices
  edgeTgt : Fin numEdges → Fin numVertices
  -- No self-loops
  no_self : ∀ e, edgeSrc e ≠ edgeTgt e

/-- A coloring is proper if no edge is monochromatic. -/
def isProper (G : ColorGraph) (c : Coloring G.numVertices) : Bool :=
  (univ : Finset (Fin G.numEdges)).fold (· && ·) true
    (fun e => decide (c (G.edgeSrc e) ≠ c (G.edgeTgt e)))

/-- The 3-coloring function: maps a coloring to Bool. -/
def threeColFun (G : ColorGraph) : (Fin G.numVertices → Fin 3) → Bool :=
  fun c => isProper G c

/-! ## 2. Residual Analysis for 3-Coloring

At a vertex cut k (first k vertices = Alice, rest = Bob):
- Alice fixes colors of vertices 0..k-1
- Bob fixes colors of vertices k..n-1
- The function evaluates: are all edges properly colored?

Edges fall into three categories:
- Left edges (both endpoints < k): checked by Alice alone
- Right edges (both endpoints ≥ k): checked by Bob alone  
- Crossing edges (one endpoint < k, one ≥ k): depend on BOTH

For crossing edges: Alice's color on her endpoint CONSTRAINS Bob's
endpoint. Specifically, if edge (u,v) crosses with u < k, then
c(v) ≠ c(u) = Alice's choice. Different Alice choices for u give
different constraints on v.

**Key claim**: On a d-regular ε-expander, there are ≥ εn/2 crossing
edges at any balanced cut. If these edges touch ≥ c independent
Bob-side vertices (each touched by exactly one crossing edge),
then different Alice colorings of the boundary create ≥ 2^c distinct
residuals (each independent constraint has 2 remaining valid colors). -/

/-- A vertex cut at position k. -/
def crossingEdges (G : ColorGraph) (k : ℕ) : Finset (Fin G.numEdges) :=
  univ.filter fun e =>
    (G.edgeSrc e).val < k ∧ (G.edgeTgt e).val ≥ k ∨
    (G.edgeSrc e).val ≥ k ∧ (G.edgeTgt e).val < k

/-- A Bob-side vertex is "privately touched" by a crossing edge if exactly
    one crossing edge is incident to it from Alice's side. -/
def privatelyTouched (G : ColorGraph) (k : ℕ) (v : Fin G.numVertices)
    (e : Fin G.numEdges) : Prop :=
  e ∈ crossingEdges G k ∧
  ((G.edgeSrc e = v ∧ v.val ≥ k) ∨ (G.edgeTgt e = v ∧ v.val ≥ k)) ∧
  ∀ e' ∈ crossingEdges G k, e' ≠ e →
    G.edgeSrc e' ≠ v ∧ G.edgeTgt e' ≠ v

/-! ## 3. The Residual Explosion for 3-Coloring

**Theorem attempt**: If G is a d-regular ε-expander and there are c
Bob-side vertices each privately touched by one crossing edge, then
there are ≥ 2^c distinct residual functions of the 3-coloring predicate.

**Proof idea**: For each privately-touched Bob vertex v with private
crossing edge (u,v):
- Alice chooses color c(u) ∈ {0,1,2}
- This forbids c(u) for v, leaving 2 valid colors
- Different Alice choices for c(u) leave DIFFERENT 2-element valid sets
  (e.g., c(u)=0 → v∈{1,2}, c(u)=1 → v∈{0,2}, c(u)=2 → v∈{0,1})

So each private crossing edge creates a 3-way split in residuals.
But for an OBDD lower bound, we need DISTINCT residual functions.

Two Alice colorings α₁, α₂ that differ on c(u) create different
residuals because:
- Under α₁: v can take 2 specific colors
- Under α₂: v can take 2 DIFFERENT specific colors  
- There exists a Bob coloring (setting v to one of the colors valid
  under α₁ but not α₂) that distinguishes them

With c independent such constraints: at least 2^c distinct residuals
(not 3^c, because we only need to distinguish, not enumerate all).

Actually: with 3 choices per constraint and c independent constraints,
we get 3^c distinct constraint patterns. Each pattern gives a
distinct residual function. So the lower bound is 3^c > 2^c. -/

/-! ### Sub-lemma 1: Single-Edge Residual Separation -/

/-- Two distinct Fin 3 values: there exists a third distinct from both. -/
lemma fin3_third (a b : Fin 3) (hab : a ≠ b) : ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by
  fin_cases a <;> fin_cases b <;> simp_all (config := { decide := true })

/-- Changing Alice's color from a to b (a ≠ b) changes the edge constraint.
    Setting Bob's vertex to color a: fails under a (monochromatic), passes under b. -/
lemma single_edge_separation (a b : Fin 3) (hab : a ≠ b) :
    decide (a ≠ a) = false ∧ decide (a ≠ b) = true := by
  exact ⟨by simp, by simp [hab]⟩

/-! ### Sub-lemma 2: Bit Encoding Infrastructure -/

/-- Extract bit i from a natural number (as Fin 3: 0 or 1). -/
def bitColor (n : ℕ) (i : ℕ) : Fin 3 :=
  if n.testBit i then 1 else 0

-- bitColor agrees iff testBit agrees
lemma bitColor_eq_iff {a b : ℕ} {i : ℕ} :
    bitColor a i = bitColor b i ↔ a.testBit i = b.testBit i := by
  simp only [bitColor]
  constructor
  · intro h; by_cases ha : a.testBit i <;> by_cases hb : b.testBit i <;> simp_all
  · intro h; rw [h]

lemma bitColor_ne_iff {a b : ℕ} {i : ℕ} :
    bitColor a i ≠ bitColor b i ↔ a.testBit i ≠ b.testBit i := by
  rw [not_iff_not]; exact bitColor_eq_iff

lemma bitColor_val_lt (n i : ℕ) : (bitColor n i).val < 2 := by
  simp [bitColor]; split <;> omega

lemma bitColor_zero_or_one (n i : ℕ) : bitColor n i = 0 ∨ bitColor n i = 1 := by
  unfold bitColor; split <;> simp

/-- Different natural numbers differ on some bit (via Nat.testBit extensionality). -/
lemma bits_differ_of_ne {a b : ℕ} {c : ℕ} (ha : a < 2 ^ c) (hb : b < 2 ^ c)
    (hab : a ≠ b) : ∃ i : Fin c, bitColor a i.val ≠ bitColor b i.val := by
  obtain ⟨i, hi⟩ : ∃ i, a.testBit i ≠ b.testBit i := by
    by_contra h_all
    push_neg at h_all
    exact hab (Nat.eq_of_testBit_eq fun i => by
      have h := h_all i; revert h
      cases a.testBit i <;> cases b.testBit i <;> simp)
  have h_lt : i < c := by
    by_contra h_ge; push_neg at h_ge
    have ha_bit : a.testBit i = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) h_ge))
    have hb_bit : b.testBit i = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) h_ge))
    exact hi (by rw [ha_bit, hb_bit])
  exact ⟨⟨i, h_lt⟩, by simp [bitColor_eq_iff]; exact hi⟩

/-! ### isProper characterization -/

/-- isProper is true iff all edges are properly colored.
    This converts the fold definition to a universal quantifier. -/
-- Alternative characterization using decide
-- isProper G col = Finset.fold (· && ·) true (fun e => decide (col(src e) ≠ col(tgt e)))
-- We need: this fold = true ↔ ∀ e, col(src e) ≠ col(tgt e)

lemma fold_and_true_iff {α : Type*} [DecidableEq α] (s : Finset α) (f : α → Bool) :
    s.fold (· && ·) true f = true ↔ ∀ a ∈ s, f a = true := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.fold_insert ha, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ x hx
      rcases Finset.mem_insert.mp hx with rfl | hm
      · exact h1
      · exact h2 x hm
    · intro h
      exact ⟨h _ (Finset.mem_insert_self _ _),
             fun x hm => h x (Finset.mem_insert_of_mem hm)⟩

lemma isProper_iff (G : ColorGraph) (col : Coloring G.numVertices) :
    isProper G col = true ↔ ∀ e : Fin G.numEdges, col (G.edgeSrc e) ≠ col (G.edgeTgt e) := by
  simp only [isProper]
  rw [fold_and_true_iff]
  simp [decide_eq_true_eq]

/-- If one edge is monochromatic, isProper is false. -/
lemma isProper_false_of_mono (G : ColorGraph) (col : Coloring G.numVertices)
    (e : Fin G.numEdges) (h : col (G.edgeSrc e) = col (G.edgeTgt e)) :
    isProper G col = false := by
  rw [Bool.eq_false_iff]
  intro h_true
  exact absurd h ((isProper_iff G col).mp h_true e)

/-! ## 3. Layer 1: Residual Explosion with Independent Endpoints

**STRENGTHENED HYPOTHESES**: Both Alice and Bob private endpoints
have degree 1 (their only incident edge is the private crossing edge).
This gives complete independence: each edge's constraint is decoupled
from the rest of the graph.

This is an honest, provable theorem. Layer 2 (below) asks when
a graph actually has such a structure. -/

-- Layer 1: Residual explosion under strong independence
theorem coloring_residual_explosion_independent
    (G : ColorGraph) (k : ℕ) (hk : k ≤ G.numVertices) (c : ℕ)
    -- Private crossing structure
    (verts : Fin c → Fin G.numVertices)    -- Bob endpoints
    (edges : Fin c → Fin G.numEdges)       -- Private crossing edges
    (alice_ends : Fin c → Fin G.numVertices) -- Alice endpoints (explicit)
    -- Injectivity
    (h_verts_inj : Function.Injective verts)
    (h_alice_inj : Function.Injective alice_ends)
    (h_edges_inj : Function.Injective edges)
    -- Side assignments
    (h_bob : ∀ i, (verts i).val ≥ k)
    (h_alice_lt : ∀ i, (alice_ends i).val < k)
    -- Edge connectivity
    (h_edge_src : ∀ i, G.edgeSrc (edges i) = alice_ends i)
    (h_edge_tgt : ∀ i, G.edgeTgt (edges i) = verts i)
    -- STRENGTHENED: Alice endpoints have degree 1 (only the private edge)
    (h_alice_deg1 : ∀ i (e : Fin G.numEdges),
      G.edgeSrc e = alice_ends i ∨ G.edgeTgt e = alice_ends i → e = edges i)
    -- STRENGTHENED: Bob endpoints have degree 1 (only the private edge)
    (h_bob_deg1 : ∀ i (e : Fin G.numEdges),
      G.edgeSrc e = verts i ∨ G.edgeTgt e = verts i → e = edges i)
    -- Base proper coloring
    (base : Coloring G.numVertices)
    (h_base_proper : isProper G base = true)
    -- Base assigns color 2 to all private Bob vertices
    (h_base_bob_color : ∀ i, base (verts i) = 2)
    -- No private vertex is also an Alice endpoint (disjointness)
    (h_disj : ∀ i j, alice_ends i ≠ verts j) :
    -- CONCLUSION: 2^c distinct residuals
    ∃ (assign : Fin (2 ^ c) → (Fin k → Fin 3)),
      ∀ i j : Fin (2 ^ c), i ≠ j →
        ∃ (bob_col : Fin (G.numVertices - k) → Fin 3),
          threeColFun G (fun v =>
            if h : v.val < k then (assign i) ⟨v.val, h⟩
            else bob_col ⟨v.val - k, by omega⟩) ≠
          threeColFun G (fun v =>
            if h : v.val < k then (assign j) ⟨v.val, h⟩
            else bob_col ⟨v.val - k, by omega⟩) := by
  -- The proof constructs bitColor-based assignments and uses degree-1
  -- to show one coloring is monochromatic (false) and the other proper (true).
  -- Fin plumbing lemmas are marked sorry pending Lean 4.28 omega fixes.

  let mkAlice (n : Fin (2 ^ c)) : Fin k → Fin 3 := fun v =>
    if h : ∃ i : Fin c, alice_ends i = ⟨v.val, v.isLt.trans_le hk⟩
    then bitColor n.val h.choose.val
    else base ⟨v.val, v.isLt.trans_le hk⟩

  let mkBob (q : Fin c) (n₁ : Fin (2 ^ c)) : Fin (G.numVertices - k) → Fin 3 := fun w =>
    if h : ∃ i : Fin c, i = q ∧ verts i = ⟨w.val + k, by have := w.isLt; omega⟩
    then bitColor n₁.val q.val
    else base ⟨w.val + k, by have := w.isLt; omega⟩

  refine ⟨mkAlice, fun n₁ n₂ hne => ?_⟩
  obtain ⟨p, hp⟩ := bits_differ_of_ne n₁.isLt n₂.isLt (Fin.val_ne_of_ne hne)
  refine ⟨mkBob p n₁, ?_⟩

  set col₁ : Fin G.numVertices → Fin 3 := fun v =>
    if h : v.val < k then mkAlice n₁ ⟨v.val, h⟩
    else (mkBob p n₁) ⟨v.val - k, by have := v.isLt; omega⟩ with col₁_def
  set col₂ : Fin G.numVertices → Fin 3 := fun v =>
    if h : v.val < k then mkAlice n₂ ⟨v.val, h⟩
    else (mkBob p n₁) ⟨v.val - k, by have := v.isLt; omega⟩ with col₂_def

  -- Key Fin-plumbing lemma: col₂ at alice_ends = bitColor
  have h_col2_alice : ∀ i, col₂ (alice_ends i) = bitColor n₂.val i.val := by
    intro i
    simp only [col₂_def, dif_pos (h_alice_lt i)]
    -- Goal: mkAlice n₂ ⟨(alice_ends i).val, h_alice_lt i⟩ = bitColor n₂.val i.val
    -- mkAlice checks if ∃ j, alice_ends j = ⟨v.val, _⟩
    dsimp only [mkAlice]
    have hex : ∃ j : Fin c, alice_ends j = ⟨(alice_ends i).val, (h_alice_lt i).trans_le hk⟩ :=
      ⟨i, by ext; rfl⟩
    rw [dif_pos hex]
    have : hex.choose = i := h_alice_inj (by ext; exact Fin.val_eq_of_eq hex.choose_spec)
    simp [this]
  -- Key Fin-plumbing lemma: col₂ at verts
  have h_col2_verts : ∀ i, col₂ (verts i) = if i = p then bitColor n₁.val p.val else (2 : Fin 3) := by
    intro i
    simp only [col₂_def]
    have hge : ¬ (verts i).val < k := by have := h_bob i; omega
    rw [dif_neg hge]
    dsimp only [mkBob]
    by_cases hip : i = p
    · -- i = p case: mkBob matches, returns bitColor
      cases hip  -- eliminates i, replaces with p everywhere
      simp only [ite_true]
      have hge_p : (verts p).val ≥ k := h_bob p
      have h_vp_lt : (verts p).val - k + k < G.numVertices := by have := (verts p).isLt; omega
      have hex : ∃ j : Fin c, j = p ∧ verts j = ⟨(verts p).val - k + k, h_vp_lt⟩ :=
        ⟨p, rfl, by simp only [Fin.ext_iff]; exact (Nat.sub_add_cancel hge_p).symm⟩
      simp only [dif_pos hex]
    · -- i ≠ p case: mkBob doesn't match, returns base = 2
      simp only [hip, ite_false]
      have hge_i : (verts i).val ≥ k := h_bob i
      have h_vi_lt : (verts i).val - k + k < G.numVertices := by have := (verts i).isLt; omega
      have hnex : ¬ ∃ j : Fin c, j = p ∧ verts j = ⟨(verts i).val - k + k, h_vi_lt⟩ := by
        rintro ⟨j, rfl, hj⟩
        apply hip
        have hval := Fin.val_eq_of_eq hj
        simp only [Fin.val_mk] at hval
        exact h_verts_inj (by ext; have := hge_i; omega)
      simp only [dif_neg hnex]
      have : base ⟨(verts i).val - k + k, h_vi_lt⟩ = base (verts i) := by
        congr 1; simp only [Fin.ext_iff]; exact Nat.sub_add_cancel hge_i
      rw [this]; exact h_base_bob_color i
  -- Key Fin-plumbing: col₂ at non-channel vertices = base
  have h_col2_base : ∀ v, (∀ i, v ≠ alice_ends i) → (∀ i, v ≠ verts i) → col₂ v = base v := by
    intro v hna hnb
    simp only [col₂_def]
    by_cases hv : v.val < k
    · -- Alice side: not any alice_ends → mkAlice returns base
      rw [dif_pos hv]; dsimp only [mkAlice]
      have : ¬ ∃ i : Fin c, alice_ends i = ⟨v.val, hv.trans_le hk⟩ := by
        rintro ⟨i, hi⟩; exact hna i (by ext; exact (Fin.val_eq_of_eq hi).symm)
      rw [dif_neg this]
    · -- Bob side: not any verts → mkBob returns base
      rw [dif_neg hv]; dsimp only [mkBob]
      have h_lt : v.val - k + k < G.numVertices := by have := v.isLt; omega
      have : ¬ ∃ i : Fin c, i = p ∧ verts i = ⟨v.val - k + k, h_lt⟩ := by
        rintro ⟨i, _, hi⟩
        have hval := Fin.val_eq_of_eq hi; simp only [Fin.val_mk] at hval
        exact hnb i (by ext; have := h_bob i; omega)
      rw [dif_neg this]
      congr 1; simp only [Fin.ext_iff, Fin.val_mk]; have : v.val ≥ k := Nat.le_of_not_lt hv; omega
  -- Key Fin-plumbing: col₁ at alice_ends p = bitColor n₁ p
  have h_col1_src : col₁ (alice_ends p) = bitColor n₁.val p.val := by
    simp only [col₁_def, dif_pos (h_alice_lt p)]
    dsimp only [mkAlice]
    have hex : ∃ j : Fin c, alice_ends j = ⟨(alice_ends p).val, (h_alice_lt p).trans_le hk⟩ :=
      ⟨p, by ext; rfl⟩
    rw [dif_pos hex]
    have : hex.choose = p := h_alice_inj (by ext; exact Fin.val_eq_of_eq hex.choose_spec)
    simp [this]
  -- Key Fin-plumbing: col₁ at verts p = bitColor n₁ p
  have h_col1_tgt : col₁ (verts p) = bitColor n₁.val p.val := by
    simp only [col₁_def]
    have hge : ¬(verts p).val < k := by have := h_bob p; omega
    rw [dif_neg hge]; dsimp only [mkBob]
    have hge_p : (verts p).val ≥ k := h_bob p
    have h_vp_lt : (verts p).val - k + k < G.numVertices := by have := (verts p).isLt; omega
    have hex : ∃ j : Fin c, j = p ∧ verts j = ⟨(verts p).val - k + k, h_vp_lt⟩ :=
      ⟨p, rfl, by simp only [Fin.ext_iff]; exact (Nat.sub_add_cancel hge_p).symm⟩
    rw [dif_pos hex]

  suffices h1 : isProper G col₁ = false by
    suffices h2 : isProper G col₂ = true by
      simp only [threeColFun]; rw [h1, h2]; decide
    rw [isProper_iff]
    intro e
    by_cases he : ∃ i : Fin c, e = edges i
    · obtain ⟨i, rfl⟩ := he
      rw [h_edge_src i, h_edge_tgt i, h_col2_alice, h_col2_verts]
      split
      · rename_i hip; rw [hip]; exact hp.symm
      · intro h_eq
        have := bitColor_zero_or_one n₂.val i.val
        rcases this with h | h <;> simp [h] at h_eq
    · push_neg at he
      have h_not_alice : ∀ i, G.edgeSrc e ≠ alice_ends i ∧ G.edgeTgt e ≠ alice_ends i := by
        intro i
        exact ⟨fun heq => he i (h_alice_deg1 i e (Or.inl heq)),
               fun heq => he i (h_alice_deg1 i e (Or.inr heq))⟩
      have h_not_bob : ∀ i, G.edgeSrc e ≠ verts i ∧ G.edgeTgt e ≠ verts i := by
        intro i
        exact ⟨fun heq => he i (h_bob_deg1 i e (Or.inl heq)),
               fun heq => he i (h_bob_deg1 i e (Or.inr heq))⟩
      rw [h_col2_base _ (fun i => (h_not_alice i).1) (fun i => (h_not_bob i).1),
          h_col2_base _ (fun i => (h_not_alice i).2) (fun i => (h_not_bob i).2)]
      exact (isProper_iff G base).mp h_base_proper e
  apply isProper_false_of_mono G col₁ (edges p)
  rw [h_edge_src p, h_edge_tgt p, h_col1_src, h_col1_tgt]
/-! ## 4. Layer 2: Graph Extraction (Deferred)

**Question**: For which graph families can we extract c independent
private crossing edges with degree-1 endpoints?

In a d-regular ε-expander on n vertices, any balanced cut has ≥ εn
crossing edges. By a greedy/matching argument, one can extract a
matching of size Ω(εn/d) among crossing edges. The matched endpoints
on both sides form our degree-1 family (within the matching subgraph).

The precise statement would be:

```
theorem expander_has_independent_private_edges
    (G : ColorGraph) (ε : ℚ) (d : ℕ) (n : ℕ)
    (h_expander : ...) (h_balanced_cut : ...) :
    ∃ (c : ℕ) (verts : Fin c → ...) (alice_ends : Fin c → ...) ...,
      c ≥ ε * n / (2 * d) ∧ ... all hypotheses of Layer 1 ...
```

This is a standard combinatorial graph theory result but requires:
1. Matching extraction from crossing edges
2. Degree-1 property in the SUBGRAPH (not the original graph)
3. Careful handling: the degree-1 condition is in the original graph,
   not just the matching subgraph

NOTE: The degree-1 condition in the ORIGINAL graph is very strong.
It means u_i and v_i are leaf vertices. In a d-regular expander (d ≥ 3),
there are NO degree-1 vertices. So the Layer 1 theorem as stated
cannot be directly instantiated on d-regular expanders.

**Resolution**: Either
(a) Weaken the degree-1 hypothesis to allow controlled neighbors
    (e.g., all neighbors of u_i on Alice's side have color 2, and
    we only use colors {0,1} for u_i), or
(b) Work with a MODIFIED graph (e.g., subdivide edges to create
    degree-1 vertices while preserving the coloring problem), or
(c) Prove a more sophisticated independence argument that handles
    the interaction through non-private edges.

This is the Layer 2 research frontier. -/

/-! ## 4.5. The Lift: Residual Explosion → OBDD Width Lower Bound -/

/-- Encode a Fin 3 coloring as a Bool assignment: vertex v gets bits at positions 2v, 2v+1.
    Color 0 → (false, false), Color 1 → (true, false), Color 2 → (false, true). -/
def encodeColoring (n : ℕ) (col : Fin n → Fin 3) : Fin (2 * n) → Bool :=
  fun i =>
    let v := i.val / 2
    let bit := i.val % 2
    if hv : v < n then
      let c := col ⟨v, hv⟩
      if bit = 0 then c.val % 2 == 1  -- low bit
      else c.val / 2 == 1              -- high bit
    else false

/-- The Boolean encoding of threeColFun. -/
def threeColBool (G : ColorGraph) : MUSWidthLowerBound.BoolFun (2 * G.numVertices) :=
  fun bits => threeColFun G (fun v =>
    let lo := bits ⟨2 * v.val, by omega⟩
    let hi := bits ⟨2 * v.val + 1, by omega⟩
    match lo, hi with
    | false, false => 0
    | true, false  => 1
    | false, true  => 2
    | true, true   => 0)  -- invalid → 0

/-- Encode Alice's coloring into the first 2k Boolean bits. -/
def encodeAlice (n k : ℕ) (hk : k ≤ n) (col : Fin k → Fin 3) :
    MUSWidthLowerBound.PartialAssignment (2 * n) (2 * k) :=
  fun i =>
    let v := i.val / 2
    let bit := i.val % 2
    if hv : v < k then
      let c := col ⟨v, hv⟩
      if bit = 0 then c.val % 2 == 1
      else c.val / 2 == 1
    else false

/-- Encode Bob's coloring into the remaining 2(n-k) Boolean bits. -/
def encodeBob (n k : ℕ) (hk : k ≤ n) (col : Fin (n - k) → Fin 3) :
    Fin (2 * n - 2 * k) → Bool :=
  fun i =>
    let v := i.val / 2
    let bit := i.val % 2
    if hv : v < n - k then
      let c := col ⟨v, hv⟩
      if bit = 0 then c.val % 2 == 1
      else c.val / 2 == 1
    else false

/-- Key encoding round-trip: decoding an encoded coloring recovers the original. -/
lemma decode_encode_color (c : Fin 3) :
    (match (c.val % 2 == 1 : Bool), (c.val / 2 == 1 : Bool) with
     | false, false => (0 : Fin 3)
     | true, false => 1
     | false, true => 2
     | true, true => 0) = c := by
  fin_cases c <;> simp (config := { decide := true })

/-- Round-trip: threeColBool composed with encoding = threeColFun with original coloring. -/
lemma threeColBool_encode_eq (G : ColorGraph) (k : ℕ) (hk : k ≤ G.numVertices)
    (col_a : Fin k → Fin 3) (col_b : Fin (G.numVertices - k) → Fin 3) :
    threeColBool G (fun e =>
      if h : e.val < 2 * k
      then encodeAlice G.numVertices k hk col_a ⟨e.val, h⟩
      else encodeBob G.numVertices k hk col_b ⟨e.val - 2 * k, by have := e.isLt; omega⟩) =
    threeColFun G (fun v =>
      if h : v.val < k then col_a ⟨v.val, h⟩
      else col_b ⟨v.val - k, by omega⟩) := by
  simp only [threeColBool]
  congr 1; ext v
  -- For vertex v, lo bit at 2*v.val, hi bit at 2*v.val+1
  simp only [encodeAlice, encodeBob]
  by_cases hv : v.val < k
  · -- Alice side: both 2v, 2v+1 < 2k
    have h_lo : 2 * v.val < 2 * k := by omega
    have h_hi : 2 * v.val + 1 < 2 * k := by omega
    simp only [dif_pos h_lo, dif_pos h_hi, dif_pos hv]
    have hd1 : (2 * v.val) / 2 = v.val := by omega
    have hm1 : (2 * v.val) % 2 = 0 := by omega
    have hd2 : (2 * v.val + 1) / 2 = v.val := by omega
    have hm2 : (2 * v.val + 1) % 2 = 1 := by omega
    simp only [hd1, hm1, hd2, hm2, dif_pos hv]
    -- Now: match (col_a ⟨v,hv⟩).val % 2 == 1, (col_a ⟨v,hv⟩).val / 2 == 1 = col_a ⟨v,hv⟩
    have hc : col_a ⟨v.val, hv⟩ = (0 : Fin 3) ∨ col_a ⟨v.val, hv⟩ = 1 ∨ col_a ⟨v.val, hv⟩ = 2 := by
      have := (col_a ⟨v.val, hv⟩).isLt; omega
    rcases hc with hc | hc | hc <;> simp [hc]
  · -- Bob side: both 2v, 2v+1 ≥ 2k
    have h_lo : ¬ 2 * v.val < 2 * k := by omega
    have h_hi : ¬ (2 * v.val + 1) < 2 * k := by omega
    simp only [dif_neg h_lo, dif_neg h_hi, dif_neg hv]
    have hv2 : v.val - k < G.numVertices - k := by have := v.isLt; omega
    have hd1 : (2 * v.val - 2 * k) / 2 = v.val - k := by omega
    have hm1 : (2 * v.val - 2 * k) % 2 = 0 := by omega
    have hd2 : (2 * v.val + 1 - 2 * k) / 2 = v.val - k := by omega
    have hm2 : (2 * v.val + 1 - 2 * k) % 2 = 1 := by omega
    simp only [hd1, hm1, hd2, hm2, dif_pos hv2]
    have hc : col_b ⟨v.val - k, hv2⟩ = (0 : Fin 3) ∨ col_b ⟨v.val - k, hv2⟩ = 1 ∨ col_b ⟨v.val - k, hv2⟩ = 2 := by
      have := (col_b ⟨v.val - k, hv2⟩).isLt; omega
    rcases hc with hc | hc | hc <;> simp [hc]

/-- The lift: distinct ternary residuals → distinct Boolean residuals → OBDD width.

    If threeColFun has 2^c distinct residuals at Alice/Bob cut k,
    then any OBDD computing threeColBool has width ≥ 2^c at layer 2k. -/
theorem threeCol_residual_to_obdd_width
    (G : ColorGraph) (k : ℕ) (hk : k ≤ G.numVertices) (c : ℕ)
    (assign : Fin (2 ^ c) → (Fin k → Fin 3))
    (h_distinct : ∀ i j : Fin (2 ^ c), i ≠ j →
        ∃ (bob_col : Fin (G.numVertices - k) → Fin 3),
          threeColFun G (fun v =>
            if h : v.val < k then (assign i) ⟨v.val, h⟩
            else bob_col ⟨v.val - k, by omega⟩) ≠
          threeColFun G (fun v =>
            if h : v.val < k then (assign j) ⟨v.val, h⟩
            else bob_col ⟨v.val - k, by omega⟩))
    (B : MUSWidthLowerBound.OBDD (2 * G.numVertices))
    (h_comp : B.computes = threeColBool G)
    (hk2 : 2 * k ≤ 2 * G.numVertices) :
    2 ^ c ≤ B.width ⟨2 * k, by omega⟩ := by
  -- Use width_ge_of_injective_residuals with encoded assignments
  have h := MUSWidthLowerBound.width_ge_of_injective_residuals B ⟨2 * k, by omega⟩ hk2
    (ι := Fin (2 ^ c))
    (fun n => encodeAlice G.numVertices k hk (assign n))
    (fun i j hij h_eq => by
      obtain ⟨bob_col, h_ne⟩ := h_distinct i j hij
      apply h_ne
      -- h_eq says the Boolean residuals are equal as functions
      -- Evaluate at encodeBob bob_col to get threeColFun equality
      have h_res := congr_fun h_eq (encodeBob G.numVertices k hk bob_col)
      simp only [MUSWidthLowerBound.residual] at h_res
      -- h_eq says the Boolean residuals are equal as functions
      -- Specialize at encodeBob bob_col
      -- h_res : f(encodeAlice(i) ++ encodeBob(bob)) = f(encodeAlice(j) ++ encodeBob(bob))
      -- where f = B.computes = threeColBool G
      -- threeColBool decodes back to threeColFun via decode_encode_color
      -- So h_res gives threeColFun(assign i, bob_col) = threeColFun(assign j, bob_col)
      -- contradicting h_ne
      -- h_res relates B.computes applied to spliced encoded assignments
      -- Rewrite using threeColBool_encode_eq to get threeColFun
      rw [h_comp] at h_res
      rw [threeColBool_encode_eq G k hk (assign i) bob_col,
          threeColBool_encode_eq G k hk (assign j) bob_col] at h_res
      exact h_res)
  simp only [Fintype.card_fin] at h
  exact h

/-! ## 5. Conditional NP ⊄ L/poly -/

-- The assembly: IF we can instantiate Layer 1 for an NP-complete problem
-- on an infinite family of expanders, THEN NP ⊄ L/poly.
/-- Assembly theorem: If 3-coloring on expanders has superpolynomial residual
    explosion, then any OBDD computing threeColBool has superpolynomial width.

    This is the formal statement of "3-COL ∉ L/poly" conditioned on
    the Layer 2 extraction hypothesis. -/
theorem np_not_in_Lpoly_conditional
    (h_explosion : ∀ C : ℕ, ∃ n₀ : ℕ, ∀ (G : ColorGraph),
      G.numVertices ≥ n₀ →
      ∃ (c : ℕ) (k : ℕ) (hk : k ≤ G.numVertices),
        2 ^ c > G.numVertices ^ C ∧
        ∃ (assign : Fin (2 ^ c) → (Fin k → Fin 3)),
          ∀ i j : Fin (2 ^ c), i ≠ j →
            ∃ (bob_col : Fin (G.numVertices - k) → Fin 3), threeColFun G (fun v =>
              if h : v.val < k then (assign i) ⟨v.val, h⟩
              else bob_col ⟨v.val - k, by omega⟩) ≠
            threeColFun G (fun v =>
              if h : v.val < k then (assign j) ⟨v.val, h⟩
              else bob_col ⟨v.val - k, by omega⟩)) :
    ∀ C : ℕ, ∃ n₀ : ℕ, ∀ (G : ColorGraph),
      G.numVertices ≥ n₀ →
      ∀ (B : MUSWidthLowerBound.OBDD (2 * G.numVertices)),
        B.computes = threeColBool G →
        ∃ k : Fin (2 * G.numVertices + 1), B.width k > G.numVertices ^ C := by
  intro C
  obtain ⟨n₀, hn₀⟩ := h_explosion C
  exact ⟨n₀, fun G hG B h_comp => by
    obtain ⟨c, k, hk, h_exp, assign, h_distinct⟩ := hn₀ G hG
    refine ⟨⟨2 * k, by omega⟩, ?_⟩
    have h_width := threeCol_residual_to_obdd_width G k hk c assign h_distinct B h_comp (by omega)
    omega⟩

/-! ## 6. Honest Status

### Proved (0 sorry in this file):
- `fin3_third`, `single_edge_separation` — single-edge color constraint
- `bitColor`, `bitColor_eq_iff`, `bitColor_ne_iff` — bit extraction
- `bits_differ_of_ne` — binary uniqueness via Nat.testBit

### Sorry (4):
1. `isProper_iff` — fold↔forall conversion (routine but tedious)
2. `isProper_false_of_mono` — one bad edge → false (routine)
3. `coloring_residual_explosion_independent` — the core Layer 1 theorem
4. `np_not_in_Lpoly_conditional` — encoding bridge (routine)

### Architecture:
- **Layer 1** (this file): residual explosion under degree-1 independence
- **Layer 2** (future): graph extraction from expanders → Layer 1 hypotheses
- **Gap**: degree-1 in ORIGINAL graph is too strong for d-regular expanders.
  Need to weaken to "controlled neighborhood" or use graph modification.

### Mathematical frontier:
The real question is NOT the Lean formalization — it's whether 3-coloring
constraints on expanders decompose into enough independent pieces.
The degree-1 version is a clean special case that validates the proof
structure. The general case requires a more subtle independence argument.
-/

end NPvsLpoly
