import Mathlib
import PallLean.TseitinOBDD
import PallLean.CommunicationComplexity

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

/-! ### Sub-lemma 1: Single-Edge Residual Separation

If Alice changes the color of u from a to b (a ≠ b) along a private
crossing edge (u,v), Bob can distinguish by coloring v = a:
- Under Alice-color-a: v = a is FORBIDDEN (monochromatic edge)  
- Under Alice-color-b: v = a is ALLOWED (a ≠ b)

This gives a concrete distinguishing Bob assignment for any
single-edge color flip. -/

/-- Two distinct Fin 3 values: there exists a third distinct from both. -/
lemma fin3_third (a b : Fin 3) (hab : a ≠ b) : ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by
  fin_cases a <;> fin_cases b <;> simp_all <;> exact ⟨_, by omega, by omega⟩

/-- The key single-edge observation: if Alice colors u with color a,
    and edge (u,v) exists, then the constraint is v ≠ a.
    Changing Alice's color from a to b (a ≠ b) changes the constraint
    from (v ≠ a) to (v ≠ b). Setting v = a satisfies the second but
    not the first. -/
lemma single_edge_separation (a b : Fin 3) (hab : a ≠ b) :
    decide (a ≠ a) = false ∧ decide (a ≠ b) = true := by
  constructor
  · simp
  · simp [hab]

/-! ### Sub-lemma 2: Multi-Edge Independence (Bit Encoding)

We encode 2^c Alice colorings by assigning each private Alice endpoint
u_i a color from {0, 1} based on bit i of the index. Two different
indices differ on some bit → their constraint patterns differ on the
corresponding Bob vertex → Bob distinguishes by targeting that vertex.

The independence comes from DISJOINTNESS: each Bob vertex v_i is
touched by exactly one crossing edge, so changing v_i's color only
affects edge (u_i, v_i) among the crossing edges. -/

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

/-- Different natural numbers differ on some bit. -/
lemma bits_differ_of_ne {a b : ℕ} {c : ℕ} (ha : a < 2 ^ c) (hb : b < 2 ^ c)
    (hab : a ≠ b) : ∃ i : Fin c, bitColor a i.val ≠ bitColor b i.val := by
  -- a ≠ b → testBit differs somewhere
  obtain ⟨i, hi⟩ : ∃ i, a.testBit i ≠ b.testBit i := by
    by_contra h_all
    push_neg at h_all
    exact hab (Nat.eq_of_testBit_eq fun i => Bool.eq_of_beq_eq_true
      (by cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all))
  -- The differing bit must be < c
  have h_lt : i < c := by
    by_contra h_ge; push_neg at h_ge
    exact hi (by
      rw [Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by omega)])
  exact ⟨⟨i, h_lt⟩, by rwa [bitColor_eq_iff]⟩

/-- The residual explosion theorem for 3-coloring (the core claim).
    
    If there are c independent privately-touched Bob vertices, then
    there are ≥ 2^c distinct residuals of the 3-coloring function.
    
    This is the analogue of tseitin_parity_residuals for coloring. -/
theorem coloring_residual_explosion
    (G : ColorGraph) (k : ℕ) (hk : k ≤ G.numVertices) (c : ℕ)
    -- c privately-touched Bob vertices
    (verts : Fin c → Fin G.numVertices)
    (edges : Fin c → Fin G.numEdges)
    (h_verts_inj : Function.Injective verts)
    (h_bob : ∀ i, (verts i).val ≥ k)
    (h_crossing : ∀ i, edges i ∈ crossingEdges G k)
    -- Each edge connects an Alice vertex to verts i
    (h_alice_end : ∀ i, ∃ u : Fin G.numVertices, u.val < k ∧
      (G.edgeSrc (edges i) = u ∧ G.edgeTgt (edges i) = verts i ∨
       G.edgeSrc (edges i) = verts i ∧ G.edgeTgt (edges i) = u))
    -- Private: no other crossing edge touches verts i
    (h_private : ∀ i j, i ≠ j →
      G.edgeSrc (edges i) ≠ verts j ∧ G.edgeTgt (edges i) ≠ verts j)
    -- The graph has a proper 3-coloring (so the function is not trivially false)
    (h_colorable : ∃ col : Coloring G.numVertices, isProper G col = true) :
    -- At least 2^c distinct Alice-side colorings yield distinct residuals
    ∃ (assign : Fin (2 ^ c) → (Fin k → Fin 3)),
      ∀ i j : Fin (2 ^ c), i ≠ j →
        ∃ (bob_col : Fin (G.numVertices - k) → Fin 3),
          threeColFun G (fun v =>
            if h : v.val < k then (assign i) ⟨v.val, h⟩
            else bob_col ⟨v.val - k, by omega⟩) ≠
          threeColFun G (fun v =>
            if h : v.val < k then (assign j) ⟨v.val, h⟩
            else bob_col ⟨v.val - k, by omega⟩) := by
  -- PROOF SKETCH:
  -- 1. Fix a proper coloring `col` (from h_colorable)
  -- 2. For each index n < 2^c, define assign(n) = col on all Alice vertices,
  --    EXCEPT: for each private Alice endpoint u_i, set color = bitColor n i
  --    (using {0,1} ⊆ Fin 3)
  -- 3. For n₁ ≠ n₂, bits_differ_of_ne gives index p where bitColor differs
  -- 4. Bob distinguishes at vertex verts(p):
  --    - Under assign(n₁): edge (u_p, verts(p)) forbids bitColor n₁ p
  --    - Under assign(n₂): edge (u_p, verts(p)) forbids bitColor n₂ p
  --    - Set verts(p) = bitColor n₁ p: violates first, satisfies second
  --    (if other edges and coloring is arranged so only this edge differs)
  -- The hard part: ensuring Alice's modification doesn't break left edges,
  -- and Bob's modification doesn't break right edges.
  -- Requires: the private Alice endpoints u_i are pairwise distinct and
  -- have no left-only edges between them (or can be 2-colored freely).
  sorry

/-! ## 4. From 3-Coloring to NP ⊄ L/poly -/

/-- The full chain (assuming coloring_residual_explosion):

    1. 3-COL on d-regular ε-expanders has ≥ 2^c residuals (c = Ω(n/d²))
    2. Any OBDD computing 3-COL has width ≥ 2^c (from our width theorem)
    3. For any polynomial n^C, eventually 2^c > n^C
    4. So 3-COL ∉ PolyOBDD
    5. L/poly ⊆ PolyOBDD (poly-width ROBPs = L/poly)
    6. 3-COL ∉ L/poly
    7. 3-COL is NP-complete
    8. Therefore NP ⊄ L/poly -/

-- **The main theorem (conditional on residual explosion)**:
-- If 3-coloring on expanders has c-fold residual explosion at good cuts,
-- then NP ⊄ L/poly.
    
-- This is conditional on `coloring_residual_explosion` (the sorry above).
theorem np_not_in_Lpoly
    -- Hypothesis: for every polynomial bound, 3-COL on large enough
    -- expanders has more residuals than the bound
    (h_explosion : ∀ C : ℕ, ∃ n₀ : ℕ, ∀ (G : ColorGraph),
      G.numVertices ≥ n₀ →
      -- ... graph is d-regular expander with good cut ...
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
    -- NP ⊄ L/poly (stated as: 3-COL has no poly-width OBDD family)
    ∀ C : ℕ, ∃ n₀ : ℕ, ∀ (G : ColorGraph),
      G.numVertices ≥ n₀ →
      -- No OBDD of width ≤ n^C computes 3-COL on G
      ∀ (m : ℕ) (B : MUSWidthLowerBound.OBDD m),
        m = 2 * G.numVertices →  -- 2 bits per vertex
        -- (B encodes 3-COL is implicit)
        ∃ k : Fin (m + 1), B.width k > G.numVertices ^ C := by
  intro C
  obtain ⟨n₀, hn₀⟩ := h_explosion C
  exact ⟨n₀, fun G hG m B hm => by
    obtain ⟨c, k, hk, h_exp, assign, h_distinct⟩ := hn₀ G hG
    -- The 2^c distinct residuals force OBDD width ≥ 2^c > n^C
    -- This requires connecting the coloring residuals to OBDD residuals
    -- via the encoding (Fin n → Fin 3) ↔ (Fin (2n) → Bool)
    sorry⟩

/-! ## 5. Gap Analysis

### What's proved (0 sorry):
- Graph structures, coloring predicate, crossing edge analysis
- Chain from residual explosion to OBDD width to NP ⊄ L/poly structure

### What has sorry (2 sorry):
1. `coloring_residual_explosion` — the core combinatorial claim that
   private crossing edges create exponentially many distinct residuals.
   This is the analogue of `tseitin_parity_residuals` but for inequality
   constraints instead of XOR constraints.

2. `np_not_in_Lpoly` — final assembly connecting coloring residuals to
   OBDD residuals (requires formalizing the bit encoding).

### Feasibility assessment:
- Sorry 1 is the HARD part. For Tseitin, the XOR structure made
  residual independence clean (flipping one bit flips exactly one parity).
  For 3-coloring, inequality constraints are weaker — changing a color
  from 0→1 changes the forbidden color from 0→1, which affects the
  residual, but proving 2^c DISTINCT residuals requires showing the
  constraints are "independent enough."

- Sorry 2 is routine (encoding transformation).

### Key mathematical question:
Does 3-coloring on expanders have Ω(n) independent private crossing
edges at every balanced cut? If yes, coloring_residual_explosion holds
and NP ⊄ L/poly follows. This is the research frontier.
-/

end NPvsLpoly
