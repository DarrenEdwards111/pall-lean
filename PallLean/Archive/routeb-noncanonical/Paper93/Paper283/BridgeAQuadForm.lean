/-
  PallLean/Paper93/Paper283/BridgeAQuadForm.lean

  Paper §28.3 — Bridge A (quadratic-form facet): connect the per-vertex
  local energy to the per-vertex PSD quadratic form

      Φᵀ · L_v · Φ,

  where `L_v` is the local Laplacian at vertex `v`, presented here as the
  edge-sum of squared differences over directed edges incident to `v`.

  ## Scope (Z7)

  This file records only the local quadratic form and two direct facts:

    * `localQuadForm_nonneg`  — the form is nonnegative as a sum of
      squares (the PSD facet of Bridge A);
    * `localQuadForm_zero_if_aligned` — the form vanishes when `Φ` is
      constant along every incident edge.

  It is the minimal, paper-faithful bridge between the analytic local
  energy term (see `BridgeALocalEnergy.lean`) and the algebraic PSD
  quadratic form. No matrix machinery is imported beyond the `Matrix`
  namespace; the quadratic form is expressed edge-wise, which is the
  identity `Φᵀ · L_v · Φ = Σ_{e ∋ v} (Φ_{e.1} − Φ_{e.2})²` for the
  local Laplacian `L_v`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import PallLean.Paper93.Concrete.RegularGraphFixed

namespace PallLean.Paper93.Paper283

open Matrix
open scoped BigOperators

/-- The local quadratic form at vertex `v`: `Φᵀ · L_v · Φ`, where
    `L_v` is the local Laplacian given by the edge sum at `v`.

    Concretely, this is the sum of `(Φ_{e.1} − Φ_{e.2})²` over every
    directed edge `e ∈ G.edges` incident to `v`. -/
noncomputable def localQuadForm {N d : ℕ}
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (Φ : Fin N → ℝ) (v : Fin N) : ℝ :=
  ∑ e ∈ G.edges.filter (fun e => e.1 = v ∨ e.2 = v), (Φ e.1 - Φ e.2)^2

/-- The local quadratic form is nonnegative (PSD facet):
    it is a finite sum of squares. -/
theorem localQuadForm_nonneg {N d : ℕ}
    {G : PallLean.Paper93.Concrete.RegularGraphFixed N d}
    {Φ : Fin N → ℝ} {v : Fin N} :
    0 ≤ localQuadForm (N := N) (d := d) G Φ v :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- If `Φ` is constant along every edge incident to `v`, the local
    quadratic form vanishes. This is the degeneracy facet of Bridge A:
    the local `L_v`-form sees zero energy on locally-aligned `Φ`. -/
theorem localQuadForm_zero_if_aligned {N d : ℕ}
    {G : PallLean.Paper93.Concrete.RegularGraphFixed N d}
    {v : Fin N}
    (Φ : Fin N → ℝ)
    (h : ∀ e ∈ G.edges.filter (fun e => e.1 = v ∨ e.2 = v), Φ e.1 = Φ e.2) :
    localQuadForm (G := G) Φ v = 0 := by
  unfold localQuadForm
  apply Finset.sum_eq_zero
  intro e he
  have := h e he
  simp [this]

end PallLean.Paper93.Paper283
