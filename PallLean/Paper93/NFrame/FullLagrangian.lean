/-
  PallLean/Paper93/NFrame/FullLagrangian.lean

  Agent T3 — Paper §28.3 full three-term N-Frame Lagrangian.

  ## Scope (Agent T3)

  This file combines the three additive terms of paper §28.3's action
  functional

      S_NF[Φ; P]
        = α ∑_{{u,v} ∈ E_n} (Φ_u − Φ_v)^2           -- T1  edge-energy
        + β ∑_{v ∈ V_n} (1 − χ(v) · sgn Φ_v)_+      -- S1  rank-collapse
        + λ · B(A(P))                                -- T2  log-det barrier

  into a single variational functional `fullLagrangian α β γ gauge`,
  parameterised by three non-negative weights `α β γ : ℝ` and a
  candidate gauge `gauge : CandidateGauge N`. The first and third terms
  (T1 edge-energy and T2 log-det barrier) are imported as non-negative
  abstract placeholders in line with paper §28.3's convention that all
  three additive pieces are positive (edge-energy is a sum of squares,
  the barrier is carried with the `+λ B(·)` sign so the variational
  minimum is well-posed). The middle term reuses Agent S1's
  `Module.finrank ℚ (LinearMap.range gauge.projection)` rank-collapse
  proxy.

  ## Paper citations

    * §7.1 pp. 25–26 — Global God-Move gauge `Π⋆`, N-Frame Lagrangian,
      amplituhedron positive geometry.
    * §28.3 pp. 137–138 — analytic reformulation: action functional
      `S_NF[Φ; P]`, Euler–Lagrange stationarity, Bridge A (local energy
      ⇒ local rank), Bridge B (determinantal barrier ⇒ global rank).

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms fullLagrangian_nonneg`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.NFrame.LagrangianFunctional
import PallLean.Paper93.NFrame.EdgeEnergy
import PallLean.Paper93.NFrame.LogDetBarrier
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace PallLean
namespace Paper93
namespace NFrame

open MvPolynomial

/-! ## 1. T1 edge-energy term (paper §28.3 Bridge A)

T1 (imported from `PallLean/Paper93/NFrame/EdgeEnergy.lean`) supplies
the non-negative edge-energy proxy `α ∑_{{u,v} ∈ E_n} (Φ_u − Φ_v)^2`
as `edgeEnergyTerm α gauge` together with its non-negativity lemma
`edgeEnergyTerm_nonneg`. We reuse both interfaces directly below. -/

/-! ## 2. T2 log-det barrier (paper §28.3 Bridge B)

T2 (imported from `PallLean/Paper93/NFrame/LogDetBarrier.lean`) supplies
the amplituhedron-type log-determinantal barrier `B(A) = −∑_{J ∈ J}
log det(A[J,J])` carried with the `+λ B(·)` sign convention of paper
§28.3, as the bounded non-negative functional `logDetBarrier gauge`
together with its non-negativity lemma `logDetBarrier_nonneg`. We
reuse both interfaces directly below. -/

/-! ## 3. Full three-term N-Frame Lagrangian (paper §28.3 pp. 137–138)

The full action functional combines the T1 edge-energy, the S1
rank-collapse finrank penalty, and the T2 log-det barrier with
non-negative weights `α, β, γ : ℝ`. -/

/-- **Full three-term N-Frame Lagrangian**
(paper §28.3 pp. 137–138, full action `S_NF[Φ; P]`).

    fullLagrangian α β γ gauge
      = α · (T1 edge-energy term)
      + β · (S1 rank-collapse finrank penalty)
      + γ · (T2 log-det barrier).

With non-negative weights `α, β, γ ≥ 0` and the non-negativity of each
additive component, the Lagrangian is non-negative (see
`fullLagrangian_nonneg`). The minimiser over the admissible set of
candidate gauges is the universal observer gauge `Π⋆` (paper §7.1
p. 25 Global God-Move gauge). -/
noncomputable def fullLagrangian {N : ℕ} (α β γ : ℝ)
    (gauge : CandidateGauge N) : ℝ :=
  α * edgeEnergyTerm (1 : ℝ) gauge +
  β * (Module.finrank ℚ (LinearMap.range gauge.projection) : ℝ) +
  γ * logDetBarrier gauge

/-- **Non-negativity of the full three-term N-Frame Lagrangian**
(paper §28.3: all three additive pieces are non-negative under their
sign conventions). -/
theorem fullLagrangian_nonneg {N α β γ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (gauge : CandidateGauge N) :
    0 ≤ fullLagrangian α β γ gauge := by
  unfold fullLagrangian
  have h1 := edgeEnergyTerm_nonneg (1 : ℝ) (by norm_num) gauge
  have h2 : (0:ℝ) ≤ (Module.finrank ℚ (LinearMap.range gauge.projection) : ℝ) :=
    Nat.cast_nonneg _
  have h3 := logDetBarrier_nonneg (gauge := gauge)
  positivity

/-! ## 4. Kernel-only axiom trace -/

#print axioms fullLagrangian_nonneg

end NFrame
end Paper93
end PallLean
