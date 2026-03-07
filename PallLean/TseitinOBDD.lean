import Mathlib
import PallLean.MUSWidthLowerBound
import PallLean.TseitinDefs

/-!
# Tseitin OBDD Width Lower Bound

## Goal

Prove that ANY OBDD computing the Tseitin clause-subset satisfiability
function on an expander graph requires exponential width.

This extends the unit clause OBDD theorem (MUSWidthLowerBound.lean)
from a toy P-time family to a genuinely NP-hard family.

## Mathematical Argument

For a Tseitin formula on a d-regular expander graph G = (V, E):
- Variables = edge parity bits, one per edge (|E| = m)
- Each vertex v gives a parity constraint: ⊕_{e ∋ v} x_e = label(v)
- If label parity is odd, the system is UNSAT
- Each odd-labeled vertex v gives a MUS consisting of all clause
  groups involving edges incident to v

### Cut Rank Argument

For ANY ordering of the m edge variables:
1. At some cut position k, define S(k) = vertices with incident edges
   on BOTH sides of the cut
2. **Expansion property**: for a good expander, |S(k)| ≥ cn for some
   constant c > 0 and some cut position k
3. Each vertex in S(k) contributes an independent parity constraint
   on the "right side" variables
4. Different partial assignments to "left side" edges incident to S(k)
   vertices create different residual functions
5. Therefore width ≥ 2^|S(k)| ≥ 2^(cn) at level k

### Why This Works for All Orderings (Unlike Unit Clauses)

Unit clause OBDD bound required a SPECIFIC interleaving ordering.
The Tseitin/expander bound works for ALL orderings because:
- Expansion guarantees many split vertices at some cut, regardless of ordering
- This is exactly what makes expanders useful in complexity theory

## Structure

1. Define the Tseitin clause-subset-SAT function
2. Define "split vertices" at a cut
3. State the expansion property
4. Prove: split vertices → distinct residuals → high width
-/

namespace TseitinOBDD

open Finset BigOperators MUSWidthLowerBound

/-! ## 1. Edge ordering and split vertices -/

/-- An edge ordering: a bijection from edge indices to positions. -/
abbrev EdgeOrdering (m : ℕ) := Equiv.Perm (Fin m)

/-- The set of "split vertices" at cut position k under ordering σ:
    vertices that have at least one incident edge in positions < k
    AND at least one incident edge in positions ≥ k. -/
def splitVertices (G : Tseitin.RegularGraph) (σ : EdgeOrdering G.numEdges)
    (k : Fin (G.numEdges + 1)) : Finset (Fin G.numVertices) :=
  Finset.univ.filter fun v =>
    -- v has an edge in the "left" (positions < k)
    (∃ e : Fin G.numEdges, (G.edgeSrc e = v ∨ G.edgeTgt e = v) ∧
      (σ e).val < k.val) ∧
    -- v has an edge in the "right" (positions ≥ k)
    (∃ e : Fin G.numEdges, (G.edgeSrc e = v ∨ G.edgeTgt e = v) ∧
      (σ e).val ≥ k.val)

/-! ## 2. Expansion property -/

/-- A graph has the cut-expansion property if for every edge ordering,
    there exists a cut with many split vertices. -/
def HasCutExpansion (G : Tseitin.RegularGraph) (c : ℕ) : Prop :=
  ∀ σ : EdgeOrdering G.numEdges,
    ∃ k : Fin (G.numEdges + 1),
      (splitVertices G σ k).card ≥ c

/-- Key graph-theoretic fact: d-regular expanders have linear cut expansion.

    For any edge ordering of a d-regular expander on n vertices,
    there exists a cut with ≥ n/(2d) split vertices.

    Proof sketch: By pigeonhole on the m+1 cut positions.
    For each vertex v, the d edges incident to v span a range
    of positions [min_pos(v), max_pos(v)]. The vertex is split
    at all cuts k with min_pos(v) < k ≤ max_pos(v).
    The number of such positions is ≥ 1 (since d ≥ 2).
    Summing over all n vertices, total split-vertex-cut pairs ≥ n.
    By pigeonhole, some cut has ≥ n/(m+1) ≥ n/(nd+1) ≥ 1/(d+1)·n
    split vertices. -/
theorem expander_has_cut_expansion (G : Tseitin.RegularGraph)
    (hn : G.numVertices ≥ 2 * G.degree + 1) :
    HasCutExpansion G (G.numVertices / (2 * G.degree)) := by
  intro σ
  -- Count total (vertex, cut) pairs where vertex is split
  -- Each vertex v with degree d has edges at d distinct positions.
  -- v is split at all cuts strictly between min and max position of its edges.
  -- That's ≥ 1 cut per vertex (since d ≥ 2, min < max).
  -- Total pairs ≥ n. Cuts range over m+1 ≤ nd+1 positions.
  -- Pigeonhole: some cut has ≥ n/(nd+1) ≥ 1/(d+1) · n vertices.
  -- Since d ≤ 10 and n ≥ 2d+1, this is ≥ n/(2d).
  sorry

/-! ## 3. Tseitin parity function on edge subsets -/

/-- The Tseitin parity function on edge-inclusion bits.

    Given a graph G and vertex labels, the function on edge subsets z ∈ {0,1}^m:
    f(z) = true iff, for every vertex v, the XOR of included incident edges
    matches the label.

    This captures the parity structure of Tseitin formulas. -/
def tseitinSubsetSAT (G : Tseitin.RegularGraph)
    (labels : Fin G.numVertices → Bool) : BoolFun G.numEdges :=
  fun z =>
    decide (∀ v : Fin G.numVertices,
      -- Parity = count of true edges mod 2
      (Finset.univ.filter (fun e : Fin G.numEdges =>
        (G.edgeSrc e = v ∨ G.edgeTgt e = v) ∧ z e = true)).card % 2
      = if labels v then 1 else 0)

/-! ## 4. The main width theorem -/

/-- **Main theorem**: For Tseitin on expanders, any OBDD has exponential width.

    More precisely: for a d-regular expander G on n vertices with
    n ≥ 2d+1, any OBDD computing tseitinSubsetSAT with edge ordering σ
    has width ≥ 2^(n/(2d)) at some level.

    This is NP-hard (Tseitin is coNP-complete) and the bound holds
    for ALL orderings (not just specific interleavings). -/
theorem tseitin_obdd_width (G : Tseitin.RegularGraph)
    (labels : Fin G.numVertices → Bool)
    (hn : G.numVertices ≥ 2 * G.degree + 1)
    (B : OBDD G.numEdges)
    (h_comp : B.computes = tseitinSubsetSAT G labels) :
    ∃ k : Fin (G.numEdges + 1),
      B.width k ≥ 2 ^ (G.numVertices / (2 * G.degree)) := by
  -- Step 1: Get the cut with many split vertices (expansion)
  obtain ⟨k, hk⟩ := expander_has_cut_expansion G hn (Equiv.refl _)
  use k
  -- Step 2: Each split vertex contributes an independent parity constraint
  -- Different left-side assignments create different residual functions
  -- because they determine different parity requirements on the right side
  -- Step 3: Width ≥ 2^(#split vertices) ≥ 2^(n/(2d))
  sorry

/-! ## 5. The separation theorem -/

/-- **Corollary**: No polynomial-width OBDD computes Tseitin on expanders.

    For any polynomial bound p(n), for large enough expanders,
    the OBDD width exceeds p(n). -/
theorem tseitin_not_poly_obdd :
    ∀ C : ℕ,
    ∃ n₀ : ℕ, ∀ (G : Tseitin.RegularGraph),
      G.numVertices ≥ n₀ →
      G.numVertices ≥ 2 * G.degree + 1 →
      ∀ (labels : Fin G.numVertices → Bool)
        (B : OBDD G.numEdges)
        (h_comp : B.computes = tseitinSubsetSAT G labels),
      ∃ k, B.width k > G.numVertices ^ C := by
  intro C
  -- For large enough n: 2^(n/(2d)) > n^C
  -- Since d ≤ 10 (from RegularGraph), n/(2d) ≥ n/20
  -- 2^(n/20) > n^C for n ≥ some n₀(C)
  sorry

/-! ## Status

### Proved:
- splitVertices definition ✅
- HasCutExpansion definition ✅
- tseitinSubsetSAT definition ✅
- restricted_model_separation (in SearchToOBDDBridge) ✅

### Sorry's (3):
1. `expander_has_cut_expansion` — pigeonhole on vertex-cut pairs
2. `tseitin_obdd_width` — main theorem, needs residual injectivity for Tseitin
3. `tseitin_not_poly_obdd` — corollary, needs 2^(n/20) > n^C

### The key mathematical step:
The core difficulty is proving that split vertices create distinct residuals
for the Tseitin parity function. This is where the parity structure
(XOR constraints) matters — each split vertex's parity constraint
means the residual function depends on the left-side edge assignments
through independent linear (mod 2) conditions.

For unit clauses, residuals were conjunctions of negations.
For Tseitin, residuals are XOR-based parity checks — even stronger
for creating distinct functions (linear algebra over GF(2) gives
exact 2^k distinct residuals for k independent constraints).
-/

end TseitinOBDD
