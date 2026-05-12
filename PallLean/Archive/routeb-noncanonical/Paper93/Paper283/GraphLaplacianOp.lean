/-
  PallLean/Paper93/Paper283/GraphLaplacianOp.lean

  Y1 — Graph Laplacian as a *linear operator*
  `L_G : (Fin N → ℝ) → (Fin N → ℝ)`.

  ## Scope

  For a (target) `d`-regular graph `G` on `N` vertices (from
  `RegularGraphFixed N d`, whose edge set is stored as a `Finset` of
  directed pairs `(u, v) : Fin N × Fin N`), the *graph Laplacian
  operator* acting on functions `Φ : Fin N → ℝ` is defined, per the
  Y1 task prompt, by summing the outgoing edge-difference contributions
  at each vertex:

      (L_G Φ)(v) = ∑_{(v, u) ∈ E} (Φ(v) − Φ(u)).

  This is the standard combinatorial graph Laplacian, expressed as an
  explicit linear operator rather than as a matrix.  It is manifestly
  ℝ-linear, which is the key algebraic property proved here.

  ## Linearity

  The Y1 linearity statement is

      L_G (Φ + a · Ψ) v = L_G Φ v + a · L_G Ψ v,

  i.e.\ ℝ-linearity in the "displacement" field `Φ`.  The proof is the
  standard arithmetic distribution of `Finset.sum` over addition and
  scalar multiplication.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms graphLaplacianOp_linear`:
      [propext, Classical.choice, Quot.sound]
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import PallLean.Paper93.Concrete.RegularGraphFixed

namespace PallLean.Paper93.Paper283

open PallLean.Paper93.Concrete
open scoped BigOperators

/-- **Graph Laplacian operator** on a (fixed) regular graph.

For `G : RegularGraphFixed N d` and `Φ : Fin N → ℝ`,

    (L_G Φ)(v) = ∑_{(v, u) ∈ E} (Φ(v) − Φ(u)),

where the sum ranges over outgoing directed edges of `G` at `v`
(i.e.\ those pairs `e ∈ G.edges` with `e.1 = v`).

This is the combinatorial graph Laplacian, expressed directly as an
operator on functions `Fin N → ℝ` (rather than as a matrix / mulVec
composition). -/
noncomputable def graphLaplacianOp {N d : ℕ}
    (G : RegularGraphFixed N d) (Φ : Fin N → ℝ) (v : Fin N) : ℝ :=
  ∑ e ∈ G.edges.filter (fun e => e.1 = v), (Φ v - Φ e.2)

/-- **Linearity of the graph Laplacian operator**:

    L_G (Φ + a · Ψ) v = L_G Φ v + a · L_G Ψ v.

This is the standard ℝ-linearity of the combinatorial Laplacian, and
is obtained by distributing `Finset.sum` over addition and scalar
multiplication on the summand `(Φ v − Φ e.2)`. -/
theorem graphLaplacianOp_linear {N d} (G : RegularGraphFixed N d)
    (Φ Ψ : Fin N → ℝ) (a : ℝ) (v : Fin N) :
    graphLaplacianOp G (Φ + a • Ψ) v =
      graphLaplacianOp G Φ v + a * graphLaplacianOp G Ψ v := by
  classical
  -- Unfold and rewrite each summand pointwise, then split the sum.
  unfold graphLaplacianOp
  -- Rewrite the summand of the LHS into the shape
  --   (Φ v - Φ e.2) + a * (Ψ v - Ψ e.2)
  -- using pointwise addition and scalar multiplication on `Fin N → ℝ`.
  have hpt :
      ∀ e ∈ G.edges.filter (fun e => e.1 = v),
        ((Φ + a • Ψ) v - (Φ + a • Ψ) e.2)
          = (Φ v - Φ e.2) + a * (Ψ v - Ψ e.2) := by
    intro e _he
    -- Evaluate pointwise `+` and `•` on `Fin N → ℝ` and distribute.
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  -- Apply the pointwise rewrite under the `Finset.sum`.
  rw [Finset.sum_congr rfl hpt]
  -- Split the sum of a sum, and factor `a` out of the scalar-multiplied
  -- part to land on the target shape.
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]

end PallLean.Paper93.Paper283
