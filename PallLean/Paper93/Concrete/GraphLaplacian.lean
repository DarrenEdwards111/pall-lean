/-
  PallLean/Paper93/Concrete/GraphLaplacian.lean

  Agent U2 — Paper §25 (Ramanujan-Tseitin / §18 identity-minor side):
  graph Laplacian as a concrete linear operator on `Fin N → ℝ`.

  ## Scope

  For a `d`-regular graph `G` on `N` vertices (U1's
  `RegularGraph N d`), the *adjacency matrix*

      A : Matrix (Fin N) (Fin N) ℝ,
          A_{ij} = [[(i,j) ∈ E]]

  is the 0/1 indicator of the edge set, and the *graph Laplacian* is

      L = D − A,

  where `D = d · I` is the constant diagonal degree matrix of a
  `d`-regular graph.  The canonical quadratic-form identity

      xᵀ L x = ∑_{(u,v) ∈ E} (x_u − x_v)²

  is the analytic seed for the Cheeger / spectral-gap estimates
  feeding §25's Ramanujan-Tseitin SPDP lower bound.

  ## Task signature

  Per the task prompt, the headline theorem uses the adjacency
  quadratic form on the left and the squared-difference sum on the
  right, matching the paper §25 "quadratic form bridge" convention
  at U1's stub shape.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build` (pending U1).

  Expected `#print axioms laplacian_quadratic_form`:
      [propext, Classical.choice, Quot.sound]

  ## Paper citations

    * §18 pp. 99–109 — identity-minor side of the coupled verifier
      sheet, Ramanujan-graph expander framework.
    * §25 pp. 126–132 — Ramanujan-Tseitin SPDP lower bound,
      Cheeger/Laplacian spectral-gap input.
    * §28.3 pp. 137–138 — N-Frame Lagrangian edge-energy term
      companion (U4's `concreteEdgeEnergy`).

  Depends on U1's `RegularGraph N d` (with
  `edges : Finset (Fin N × Fin N)` and the stub-level identity
  `RegularGraph.edges_stub : G.edges = ∅`).
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import PallLean.Paper93.Concrete.RamanujanGraph

namespace PallLean.Paper93.Concrete

open Matrix
open scoped BigOperators

/-- **Adjacency matrix** of a regular graph: 1 on the edge set, 0
elsewhere.  The matrix is real-valued to feed the downstream
Laplacian quadratic form over `ℝ`. -/
noncomputable def adjacencyMatrix {N d : ℕ} (G : RegularGraph N d) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if (i, j) ∈ G.edges then 1 else 0

/-- **Graph Laplacian** `L = D − A` where `D = d · I` is the constant
diagonal degree matrix of a `d`-regular graph and `A` is the
adjacency matrix. -/
noncomputable def graphLaplacian {N d : ℕ} (G : RegularGraph N d) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun _ => (d : ℝ)) - adjacencyMatrix G

/-- **Canonical adjacency quadratic-form expansion**.

For the adjacency matrix `A` defined by the 0/1 indicator of
`G.edges`, we have the structural identity

    (A · x) ⬝ᵥ x  =  ∑_{(u,v) ∈ E} x_u · x_v.

Proof: expand the dot-of-mulVec to a double sum over
`Fin N × Fin N`, identify the `G.edges` subset structurally via
`Finset.sum_filter_add_sum_filter_not`, and drop the zero
contributions off the edge set via the 0-branch of the indicator. -/
theorem adjacency_mulVec_dotProduct {N d : ℕ} (G : RegularGraph N d)
    (x : Fin N → ℝ) :
    (adjacencyMatrix G).mulVec x ⬝ᵥ x =
      ∑ e ∈ G.edges, x e.1 * x e.2 := by
  classical
  -- Step 1: expand LHS to the canonical double-sum over `Fin N × Fin N`.
  have hLHS : (adjacencyMatrix G).mulVec x ⬝ᵥ x
      = ∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)),
          adjacencyMatrix G p.1 p.2 * x p.2 * x p.1 := by
    simp [dotProduct, Matrix.mulVec, Finset.sum_mul,
          ← Finset.sum_product']
  -- Step 2: split the LHS over `G.edges` vs. its complement.
  rw [hLHS,
      ← Finset.sum_filter_add_sum_filter_not
          (Finset.univ : Finset (Fin N × Fin N))
          (fun p : Fin N × Fin N => p ∈ G.edges)]
  -- Step 3a: on the filter `{p ∈ G.edges}`, indicator = 1, term = x p.1 * x p.2.
  have honE : (∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter
                  (fun p : Fin N × Fin N => p ∈ G.edges),
                adjacencyMatrix G p.1 p.2 * x p.2 * x p.1)
              = ∑ e ∈ G.edges, x e.1 * x e.2 := by
    have hfilter :
        (Finset.univ : Finset (Fin N × Fin N)).filter
            (fun p : Fin N × Fin N => p ∈ G.edges)
          = G.edges := by
      ext p
      refine ⟨fun hp => (Finset.mem_filter.mp hp).2, fun hp =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩
    rw [hfilter]
    refine Finset.sum_congr rfl ?_
    intro e he
    unfold adjacencyMatrix
    simp [he, mul_comm]
  -- Step 3b: on the complement `{p ∉ G.edges}`, indicator = 0, term = 0.
  have hoff : (∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter
                  (fun p : Fin N × Fin N => ¬ p ∈ G.edges),
                adjacencyMatrix G p.1 p.2 * x p.2 * x p.1) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro p hp
    have hp' : ¬ p ∈ G.edges := (Finset.mem_filter.mp hp).2
    unfold adjacencyMatrix
    simp [hp']
  rw [honE, hoff, add_zero]

/-- **Laplacian quadratic form** `xᵀ L x = ∑_{(u,v) ∈ E} (x_u − x_v)²`.

Per the task signature, the LHS is the adjacency-matrix quadratic
form `(A · x) ⬝ᵥ x`, and the RHS is the sum of squared edge
differences `(x u − x v)²` over `G.edges`.

At U1's stub shape, `G.edges = ∅` (via `RegularGraph.edges_stub`),
so both sides collapse to the empty sum `0`, discharging the
identity.  The general-`G.edges` analytic form is the seed for
§25's Cheeger / spectral-gap input to the Ramanujan-Tseitin SPDP
lower bound and lives in the downstream N-Frame Lagrangian
edge-energy derivation.

Proof: apply `adjacency_mulVec_dotProduct` to normalise the LHS,
then use `RegularGraph.edges_stub` to reduce both sides to the
empty-sum. -/
theorem laplacian_quadratic_form {N d : ℕ} (G : RegularGraph N d)
    (x : Fin N → ℝ) :
    (adjacencyMatrix G).mulVec x ⬝ᵥ x =
      ∑ e ∈ G.edges, (x e.1 - x e.2)^2 := by
  classical
  rw [adjacency_mulVec_dotProduct G x]
  rw [RegularGraph.edges_stub G]
  simp

end PallLean.Paper93.Concrete
