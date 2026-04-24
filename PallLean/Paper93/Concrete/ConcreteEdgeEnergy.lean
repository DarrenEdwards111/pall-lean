/-
  PallLean/Paper93/Concrete/ConcreteEdgeEnergy.lean

  Agent U4 — Paper §28.3 "N-Frame Lagrangian: observer edge-energy term".

  ## Scope

  Concrete real-valued edge-energy term of the paper §28.3 N-Frame
  action

      S_NF[Φ; P]
        = α ∑_{{u,v} ∈ E_n} (Φ_u - Φ_v)^2
        + β ∑_{v ∈ V_n} (1 - χ(v) · sgn Φ_v)_+
        + λ · B(A(P))

  (paper §28.3 pp. 137–138). Here we materialise the first term,
  the *edge-energy*

      α · ∑_{(u,v) ∈ E} (Φ_u - Φ_v)^2,

  as a concrete function on U1's `RegularGraph N d` graph structure
  and U3's `CoordMap N` observer-coordinate map.

  The term is always non-negative when `α ≥ 0`, and vanishes on the
  trivial zero-field coordinate map `trivialCoord N`. Both facts are
  recorded below; they are the analytic seed for the Euler–Lagrange
  descent from the trivial gauge towards the universal observer
  gauge `Π⋆` (paper §7.1 p. 25 / §28.3 p. 137).

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms concreteEdgeEnergy_nonneg`:
      [propext, Classical.choice, Quot.sound]

  ## Paper citations

    * §7.1 p. 25 — universal observer gauge `Π⋆` on SPDP row space.
    * §28.3 pp. 137–138 — N-Frame Lagrangian action `S_NF[Φ; P]`.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import PallLean.Paper93.Concrete.RegularGraph
import PallLean.Paper93.Concrete.CoordinateMap

namespace PallLean.Paper93.Concrete

open scoped BigOperators

/-- **Concrete edge-energy** `α · ∑_{(u,v) ∈ E} (Φ_u - Φ_v)^2`.

Real-valued first term of the paper §28.3 N-Frame action
`S_NF[Φ; P]`, built directly from U1's `RegularGraph N d` edge
Finset and U3's `CoordMap N` observer-coordinate map. -/
noncomputable def concreteEdgeEnergy {N d : ℕ} (α : ℝ)
    (G : RegularGraph N d) (Φ : CoordMap N) : ℝ :=
  α * ∑ e ∈ G.edges, (Φ.values e.1 - Φ.values e.2)^2

/-- **Non-negativity** of the edge-energy for any non-negative
coupling `α ≥ 0`. -/
theorem concreteEdgeEnergy_nonneg {N d : ℕ} (α : ℝ)
    (G : RegularGraph N d) (Φ : CoordMap N)
    (hα : 0 ≤ α) : 0 ≤ concreteEdgeEnergy α G Φ := by
  unfold concreteEdgeEnergy
  apply mul_nonneg hα
  apply Finset.sum_nonneg
  intros
  exact sq_nonneg _

/-- **Vanishing on the trivial coordinate map.**

The trivial zero-field coordinate map `trivialCoord N` is the
degenerate starting vertex of the coupled gauge/coordinate
variational problem (paper §28.3 p. 137 Euler–Lagrange); the
edge-energy vanishes identically there. -/
theorem concreteEdgeEnergy_trivial_eq_zero {N d : ℕ} (α : ℝ)
    (G : RegularGraph N d) :
    concreteEdgeEnergy α G (trivialCoord N) = 0 := by
  unfold concreteEdgeEnergy trivialCoord
  simp

end PallLean.Paper93.Concrete
