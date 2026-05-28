import Mathlib

/-!
# Expander–Tseitin width kernel (Ben-Sasson–Wigderson core, expansion doing the work)

**STATUS: A REAL, RESTRICTED THEOREM — not an assumed field, and not P≠NP.**

This file proves the genuine combinatorial heart of the Ben-Sasson–Wigderson
lower bound for Tseitin formulas on expander graphs: the place where the
*expansion property does the work*.

Tseitin variables are the edges of a graph; the parity constraint at a vertex
`v` is the F₂ indicator of the edges incident to `v`.  The key lemma proved here
is exact and unconditional:

  `edgeSupport (⊕_{v ∈ S} constraint v)  =  ∂S`   (the edge boundary of `S`).

Interior edges of `S` appear in two vertex constraints and cancel mod 2; boundary
edges appear once and survive.  Therefore, on a graph with vertex expansion `c`,
*any* combination of a medium vertex set's constraints has support (= width)
at least `c · |S|`: you cannot derive a narrow consequence from a medium set of
axioms.  This is the BSW "expansion ⇒ width" core, and expansion enters as a
genuine hypothesis (`HasExpansion`), not a free predicate.

**Honest scope.**
* This is the *width* kernel.  The full BSW theorem (width lower bound ⇒
  exponential resolution *size*) builds on this and is cited, not formalized here.
* It is a *restricted* lower bound (width / proof-complexity flavour).  By the
  standing analysis, restricted bounds do not scale to general `P` vs `NP`, and
  the bridge "every P-time decider induces a low-width object" is P≠NP-strength.
  Nothing here claims otherwise.

What is new relative to the rest of this directory: the lower bound is *derived*
from the graph structure and a real expansion hypothesis, with `edgeSupport = ∂S`
proved — it is not assumed via a collision field or an unrestricted quantifier.
-/

namespace PallLean.Paper93.DeepMath.PathB

open Finset

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]

/-- The F₂ support of an edge-vector. -/
def edgeSupport (f : Edge → ZMod 2) : Finset Edge :=
  univ.filter (fun e => f e ≠ 0)

/-- A Tseitin graph: each edge carries its endpoint set, with exactly two
endpoints (a genuine simple-graph edge, no loops). -/
structure TseitinGraph (V Edge : Type*) [Fintype V] [DecidableEq V]
    [Fintype Edge] [DecidableEq Edge] : Type _ where
  endpoints : Edge → Finset V
  card_endpoints : ∀ e, (endpoints e).card = 2

namespace TseitinGraph

variable (G : TseitinGraph V Edge)

/-- The F₂ constraint vector of vertex `v`: indicator of the edges incident to
`v`. -/
def constraint (v : V) (e : Edge) : ZMod 2 :=
  if v ∈ G.endpoints e then 1 else 0

/-- The F₂ combination of the vertex constraints over a vertex set `S`. -/
def combination (S : Finset V) (e : Edge) : ZMod 2 :=
  ∑ v ∈ S, G.constraint v e

/-- The edge boundary of a vertex set: edges with exactly one endpoint in `S`. -/
def boundary (S : Finset V) : Finset Edge :=
  univ.filter (fun e => (G.endpoints e ∩ S).card = 1)

/-- The combination value at edge `e` is the parity of the number of endpoints
of `e` lying in `S`. -/
theorem combination_eq_card (S : Finset V) (e : Edge) :
    G.combination S e = ((G.endpoints e ∩ S).card : ZMod 2) := by
  unfold combination constraint
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_comm]

/-- **Core lemma (expansion's lever):** the support of the F₂ combination of the
constraints over `S` is exactly the edge boundary `∂S`.  Interior edges cancel
mod 2; boundary edges survive. -/
theorem support_combination_eq_boundary (S : Finset V) :
    edgeSupport (G.combination S) = G.boundary S := by
  ext e
  simp only [edgeSupport, boundary, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [combination_eq_card]
  have hle : (G.endpoints e ∩ S).card ≤ 2 :=
    le_trans (Finset.card_le_card Finset.inter_subset_left) (le_of_eq (G.card_endpoints e))
  constructor
  · intro h
    have hnd : ¬ (2 ∣ (G.endpoints e ∩ S).card) := fun hd =>
      h ((CharP.cast_eq_zero_iff (ZMod 2) 2 _).2 hd)
    rw [Nat.dvd_iff_mod_eq_zero] at hnd
    omega
  · intro h
    rw [h]
    decide

/-- Vertex expansion: every nonempty set of at most half the vertices has edge
boundary at least `c` times its size.  Real expander graphs (e.g. Ramanujan
graphs) satisfy this with a constant `c`; here it is a genuine hypothesis on the
graph, not a free predicate. -/
def HasExpansion (c : ℕ) : Prop :=
  ∀ S : Finset V, 1 ≤ S.card → 2 * S.card ≤ Fintype.card V →
    c * S.card ≤ (G.boundary S).card

/-- **Expansion ⇒ width.** On a graph with expansion `c`, the combination of any
medium vertex set's constraints has support (width) at least `c · |S|`.  This is
the BSW core: no narrow consequence from a medium set of axioms.  Expansion does
the work, via `support_combination_eq_boundary`. -/
theorem combination_support_card_ge_of_expansion {c : ℕ}
    (hexp : G.HasExpansion c) (S : Finset V)
    (h1 : 1 ≤ S.card) (h2 : 2 * S.card ≤ Fintype.card V) :
    c * S.card ≤ (edgeSupport (G.combination S)).card := by
  rw [G.support_combination_eq_boundary]
  exact hexp S h1 h2

/-- **No vanishing medium combination.** With expansion `c ≥ 1`, no medium
vertex set's constraint-combination is the zero vector: a vanishing combination
(the F₂ trace of deriving a contradiction) requires more than half the vertices —
forcing the argument toward the global all-vertex parity, exactly as in the
Tseitin unsatisfiability argument. -/
theorem exists_combination_ne_zero_of_expansion {c : ℕ}
    (hc : 1 ≤ c) (hexp : G.HasExpansion c) (S : Finset V)
    (h1 : 1 ≤ S.card) (h2 : 2 * S.card ≤ Fintype.card V) :
    ∃ e, G.combination S e ≠ 0 := by
  have hge : c * S.card ≤ (edgeSupport (G.combination S)).card :=
    combination_support_card_ge_of_expansion G hexp S h1 h2
  have h11 : 1 ≤ c * S.card := by simpa using Nat.mul_le_mul hc h1
  have hpos : 0 < (edgeSupport (G.combination S)).card := lt_of_lt_of_le (by omega) hge
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  exact ⟨e, by simpa [edgeSupport, Finset.mem_filter, Finset.mem_univ] using he⟩

end TseitinGraph

/-! ## Kernel-only axiom trace -/

#print axioms TseitinGraph.combination_eq_card
#print axioms TseitinGraph.support_combination_eq_boundary
#print axioms TseitinGraph.combination_support_card_ge_of_expansion
#print axioms TseitinGraph.exists_combination_ne_zero_of_expansion

end PallLean.Paper93.DeepMath.PathB
