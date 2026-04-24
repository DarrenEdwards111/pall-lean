/-
  PallLean/Paper93/Concrete/FullLagrangianFixed.lean

  Agent U17 (V12 fix) — Paper §28.3 "Full three-term concrete N-Frame
  Lagrangian", rebuilt on the *fixed* V1 `RegularGraphFixed` and the
  paper-faithful `PallLean.Paper93.NFrame.logDetBarrier` (barrier term).

  ## Why this file exists

  The earlier U17 file `FullConcreteLagrangian.lean` was built on top
  of the original (hypothesis-laden, uninhabited-for-odd-N) `RegularGraph`
  type from U1, and pulled in U4/U9/U12 wrappers that themselves rest on
  that broken U1.  The V1 fix in
  `PallLean/Paper93/Concrete/RegularGraphFixed.lean` replaces `RegularGraph`
  with `RegularGraphFixed`, a hypothesis-free `Finset (Fin N × Fin N)`
  edge-set wrapper that is *total* for every `N`.  This file mirrors the
  U17 deliverable against the fixed type:

      fullLagrangianFixed α β γ G gauge
        := α · ∑_{(u,v) ∈ G.edges} (Φ_u − Φ_v)^2
         + β · finrank ℚ (range (gauge.projection))
         + γ · logDetBarrier(gauge.toCandidateGauge)

  where:

    * the first (edge-energy) term is taken literally as a concrete
      sum-of-squared-differences over the fixed edge finset of
      `G : RegularGraphFixed N d` (U1/V1);
    * the second (rank-collapse) term is the paper's
      `γ · rank(Π)` coefficient on the finrank of the projection range
      (paper §28.3 Bridge B);
    * the third (log-det barrier) term is the paper-faithful N-Frame
      structural log-det barrier
      `PallLean.Paper93.NFrame.logDetBarrier` (paper §28.3 pp. 137–138
      amplituhedron-type determinantal barrier).

  The central deliverable is non-negativity under non-negative weights.

  ## Paper citations

    * §7.1 pp. 25–26 — Global God-Move gauge `Π⋆`, N-Frame Lagrangian
      and amplituhedron positive geometry.
    * §28.3 pp. 137–138 — analytic reformulation: concrete action
      functional `S_NF[Φ; P]`, Bridge A (local energy ⇒ local rank),
      Bridge B (determinantal barrier ⇒ global rank).

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms fullLagrangianFixed_nonneg`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Concrete.RegularGraphFixed
import PallLean.Paper93.Concrete.CoordinateMap
import PallLean.Paper93.NFrame.LogDetBarrier
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace PallLean.Paper93.Concrete

/-! ## Full three-term concrete N-Frame Lagrangian on the fixed graph

We combine the three additive terms of paper §28.3's concrete N-Frame
action functional against `RegularGraphFixed N d` (U1/V1) and the
paper-faithful `NFrame.logDetBarrier`. -/

/-- **Full three-term concrete N-Frame Lagrangian** on `RegularGraphFixed`
(paper §28.3 pp. 137–138, full concrete action `S_NF[Φ; P]`).

    fullLagrangianFixed α β γ G gauge
      = α · ∑_{(u,v) ∈ G.edges} (Φ_u − Φ_v)^2
      + β · finrank ℚ (range gauge.projection)
      + γ · logDetBarrier(gauge.toCandidateGauge).

With non-negative weights `α, β, γ ≥ 0` and the non-negativity of each
additive component, the Lagrangian is non-negative (see
`fullLagrangianFixed_nonneg`). -/
noncomputable def fullLagrangianFixed {N d : ℕ} (α β γ : ℝ)
    (G : RegularGraphFixed N d)
    (gauge : ObserverGauge N) : ℝ :=
  α * (∑ e ∈ G.edges, (gauge.coord.values e.1 - gauge.coord.values e.2)^2) +
  β * (Module.finrank ℚ (LinearMap.range gauge.toCandidateGauge.projection) : ℝ) +
  γ * PallLean.Paper93.NFrame.logDetBarrier gauge.toCandidateGauge

/-- **Non-negativity of the full three-term concrete N-Frame Lagrangian**
(paper §28.3: all three additive pieces are non-negative under their
sign conventions with non-negative couplings).

The proof composes:

  * Non-negativity of the edge-energy sum
    `∑_{(u,v) ∈ G.edges} (Φ_u − Φ_v)^2 ≥ 0`  via `Finset.sum_nonneg`
    and `sq_nonneg`.
  * Non-negativity of `finrank ℚ (range projection) : ℝ`          via
    `Nat.cast_nonneg`.
  * Non-negativity of `logDetBarrier`                              via
    `PallLean.Paper93.NFrame.logDetBarrier_nonneg`.

Combining these three non-negative terms with non-negative scalar
weights `α, β, γ ≥ 0` yields a non-negative sum. -/
theorem fullLagrangianFixed_nonneg {N d α β γ}
    (G : RegularGraphFixed N d) (gauge : ObserverGauge N)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) :
    0 ≤ fullLagrangianFixed α β γ G gauge := by
  unfold fullLagrangianFixed
  have h1 : 0 ≤ ∑ e ∈ G.edges,
      (gauge.coord.values e.1 - gauge.coord.values e.2)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h2 : (0 : ℝ) ≤
      (Module.finrank ℚ
        (LinearMap.range gauge.toCandidateGauge.projection) : ℝ) :=
    Nat.cast_nonneg _
  have h3 : 0 ≤ PallLean.Paper93.NFrame.logDetBarrier
      gauge.toCandidateGauge :=
    PallLean.Paper93.NFrame.logDetBarrier_nonneg
      (gauge := gauge.toCandidateGauge)
  positivity

/-! ## Kernel-only axiom trace -/

#print axioms fullLagrangianFixed_nonneg

end PallLean.Paper93.Concrete
