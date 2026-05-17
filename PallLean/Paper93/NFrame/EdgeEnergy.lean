/-
  PallLean/Paper93/NFrame/EdgeEnergy.lean

  Agent T1 (retry) — Paper §28.3 N-Frame Lagrangian edge-energy term
  `α ∑_{(u,v) ∈ E}(Φ_u - Φ_v)²` — observer-consistency regularisation
  on a Ramanujan-like path graph.

  ## Scope

  Paper §28.3 pp. 137–138 defines the N-Frame action

      S_NF[Φ; P]
        = α · ∑_{{u,v} ∈ E_n} (Φ_u - Φ_v)²
        + β · ∑_{v ∈ V_n} (1 - χ(v) · sgn Φ_v)_+
        + λ · B(A(P)).

  The first summand is the graph-Laplacian **observer-consistency
  regulariser**: a non-negative quadratic form on the
  `(V_n, E_n)` Ramanujan-like expander graph penalising gauge
  choices `Π` whose induced coordinates `Φ` vary rapidly across
  adjacent vertices. This file formalises the combinatorial shell
  of that term for the simplest concrete observer graph — the
  **path graph** `P_N = (Fin N, {(i, i+1)})` — which is the
  small-diameter skeleton used to seed a Ramanujan-like expander
  in paper §28.3.

  Because the concrete vertex labelling `Φ : V_n → ℝ` is not yet
  fixed in the `CandidateGauge` structure of `LagrangianFunctional.lean`
  (paper §7.1 p. 25 only pins the projection `Π`, not the coordinate
  values `Φ_v`), we follow the S1 stub convention and use a
  rank-indexed proxy energy `α · finrank(range Π)`. This is
  deliberately the same proxy as
  `Lagrangian.rankCollapsePenalty` — it yields a non-negative real
  scaling with `α` and vanishing at the trivial rank-zero gauge
  `Π = 0`, in line with paper §28.3's Euler–Lagrange vertex at
  the rank-zero gauge.

  Later NFrame files may refine this definition to the honest
  graph Laplacian `α · ∑_{(u,v) ∈ E} (Φ_u - Φ_v)²` once a
  canonical coordinate map `Φ : V_n → ℝ` is attached to a
  candidate gauge (e.g. via its trace on a fixed SPDP row basis).

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms edgeEnergyTerm_nonneg`:
      [propext, Classical.choice, Quot.sound]

  ## Paper citations

    * §7.1 pp. 25–26 — N-Frame Lagrangian and Global God-Move gauge Π⋆.
    * §28.3 pp. 137–138 — analytic reformulation: action `S_NF[Φ; P]`,
      edge-energy observer-consistency term
      `α ∑_{(u,v) ∈ E} (Φ_u - Φ_v)²`, Euler–Lagrange conditions.
-/
import PallLean.Paper93.NFrame.LagrangianFunctional
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace PallLean
namespace Paper93
namespace NFrame

open scoped BigOperators

/-! ## 1. Observer graph (Ramanujan-like path skeleton)

Paper §28.3 p. 137: fix an expander graph `G_n = (V_n, E_n)` on
which the edge-energy regulariser acts. We take the canonical
path-graph skeleton `P_N` on `Fin N` — the simplest Ramanujan-like
graph (spectral gap ≥ `2(1 - cos(π/N))`) — to stage the combinatorial
edge set.
-/

/-- **Observer graph** edges on `Fin N`: the path-graph pairs
`(i, i+1)` for `i < N-1` (paper §28.3 Ramanujan-like skeleton).

The path graph `P_N` has `N-1` directed edges and is the
combinatorial base on which the N-Frame edge-energy term is
evaluated at the skeletal level. -/
def observerGraph (N : ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun p => p.1.val + 1 = p.2.val)

/-! ## 2. Honest graph-Laplacian edge-energy term

Paper §28.3 edge-energy term `α · ∑_{(u,v) ∈ E_n} (Φ_u - Φ_v)²`.
This is a real analytic object on a finite observer graph and a vertex field
`Φ : Fin N → ℝ`, independent of the legacy gauge-rank proxy below.
-/

/-- **Graph Laplacian edge-energy** of a vertex field on a finite directed edge
set:

`α · ∑_{(u,v) ∈ E} (Φ u - Φ v)^2`.

For symmetric edge sets this is twice the usual undirected Dirichlet energy;
for the path skeleton `observerGraph N` it is the directed path energy used as
the first concrete observer-consistency term. -/
noncomputable def graphLaplacianEdgeEnergy {N : ℕ} (α : ℝ)
    (E : Finset (Fin N × Fin N)) (Φ : Fin N → ℝ) : ℝ :=
  α * E.sum (fun e => (Φ e.1 - Φ e.2) ^ 2)

/-- The unweighted graph edge-energy is a sum of squares. -/
theorem graphLaplacianEdgeEnergy_sum_nonneg {N : ℕ}
    (E : Finset (Fin N × Fin N)) (Φ : Fin N → ℝ) :
    0 ≤ E.sum (fun e => (Φ e.1 - Φ e.2) ^ 2) := by
  exact Finset.sum_nonneg (fun e _ => sq_nonneg (Φ e.1 - Φ e.2))

/-- **Non-negativity of the honest graph-Laplacian edge-energy.**
For `0 ≤ α`, `α · ∑(Φ_u - Φ_v)^2 ≥ 0`. -/
theorem graphLaplacianEdgeEnergy_nonneg {N : ℕ} (α : ℝ) (hα : 0 ≤ α)
    (E : Finset (Fin N × Fin N)) (Φ : Fin N → ℝ) :
    0 ≤ graphLaplacianEdgeEnergy α E Φ := by
  unfold graphLaplacianEdgeEnergy
  exact mul_nonneg hα (graphLaplacianEdgeEnergy_sum_nonneg E Φ)

/-- The honest edge-energy vanishes on every constant field. -/
theorem graphLaplacianEdgeEnergy_const {N : ℕ} (α c : ℝ)
    (E : Finset (Fin N × Fin N)) :
    graphLaplacianEdgeEnergy α E (fun _ : Fin N => c) = 0 := by
  unfold graphLaplacianEdgeEnergy
  simp

/-- The concrete path-skeleton observer energy. -/
noncomputable def observerGraphEdgeEnergy (N : ℕ) (α : ℝ)
    (Φ : Fin N → ℝ) : ℝ :=
  graphLaplacianEdgeEnergy α (observerGraph N) Φ

/-- Non-negativity on the observer path skeleton. -/
theorem observerGraphEdgeEnergy_nonneg (N : ℕ) (α : ℝ) (hα : 0 ≤ α)
    (Φ : Fin N → ℝ) :
    0 ≤ observerGraphEdgeEnergy N α Φ :=
  graphLaplacianEdgeEnergy_nonneg α hα (observerGraph N) Φ

/-! ## 3. Legacy gauge-rank compatibility wrapper

At the S1-compatible level (see `LagrangianFunctional.lean`), gauges expose
only their projection `Π`; no canonical coordinate extraction
`CandidateGauge N → (Fin N → ℝ)` has been fixed.  We therefore keep the old
rank-indexed wrapper for existing downstream theorems, but the real analytic
term above is now available for the variational route.
-/

/-- **Edge-energy term** `α · E_graph(Π)` of the N-Frame Lagrangian
(paper §28.3 p. 137 edge-energy `α ∑ (Φ_u - Φ_v)²`).

At the present S1-compatible stub level we return
`α · finrank(range Π)` as a non-negative real proxy: this scales
linearly in the edge-energy coefficient `α` and vanishes for the
rank-zero (trivial) gauge, matching the Euler–Lagrange vertex
behaviour of paper §28.3. The honest graph-Laplacian sum is now formalised
above as `observerGraphEdgeEnergy`; this wrapper remains only until a concrete
coordinate map `Φ : Fin N → ℝ` is attached to `CandidateGauge`. -/
noncomputable def edgeEnergyTerm {N : ℕ} (α : ℝ)
    (gauge : CandidateGauge N) : ℝ :=
  α * (Module.finrank ℚ (LinearMap.range gauge.projection) : ℝ)

/-- **Non-negativity** of the edge-energy term (paper §28.3 p. 137:
sum-of-squares structure of `α ∑ (Φ_u - Φ_v)²` on the observer graph).

For `0 ≤ α` the stub proxy `α · finrank(range Π)` is a product of
two non-negative reals, hence non-negative. This matches the
non-negativity of the honest edge-energy regulariser on the
Ramanujan-like path graph and is consumed by
`nframeLagrangian_nonneg` downstream. -/
theorem edgeEnergyTerm_nonneg {N : ℕ} (α : ℝ) (hα : 0 ≤ α)
    (gauge : CandidateGauge N) : 0 ≤ edgeEnergyTerm α gauge := by
  unfold edgeEnergyTerm
  exact mul_nonneg hα (Nat.cast_nonneg _)

/-! ## 4. Kernel-only sanity checks

Exercise the public API at elaboration time. The two `example`s
below are discharged at parse time by the definitions and the
`edgeEnergyTerm_nonneg` lemma above, keeping the kernel-only
axiom profile `[propext, Classical.choice, Quot.sound]`. -/

noncomputable example (N : ℕ) : ℝ :=
  edgeEnergyTerm (N := N) 0 (trivialGauge N)

example (N : ℕ) : 0 ≤ edgeEnergyTerm (N := N) 0 (trivialGauge N) :=
  edgeEnergyTerm_nonneg 0 le_rfl (trivialGauge N)

#print axioms graphLaplacianEdgeEnergy_sum_nonneg
#print axioms graphLaplacianEdgeEnergy_nonneg
#print axioms graphLaplacianEdgeEnergy_const
#print axioms observerGraphEdgeEnergy_nonneg
#print axioms edgeEnergyTerm_nonneg

end NFrame
end Paper93
end PallLean
