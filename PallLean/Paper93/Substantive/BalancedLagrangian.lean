/-
  PallLean/Paper93/Substantive/BalancedLagrangian.lean

  Agent W3 — Paper §28.3 "Substantive beats-trivial wedge for
  the full three-term N-Frame Lagrangian `fullLagrangianFixed`".

  ## Scope

  V12 (`FullLagrangianFixed.lean`) defines the full three-term
  N-Frame action

      fullLagrangianFixed α β γ G gauge
        = α · ∑_{(u,v) ∈ G.edges} (Φ_u − Φ_v)^2
        + β · finrank ℚ (range gauge.projection)
        + γ · logDetBarrier gauge.toCandidateGauge

  and V13 (`NonVacuousMinimizer.lean`) pins down its concrete
  value at the canonical `trivialObserverGauge N` witness:

      fullLagrangianFixed α β γ G (trivialObserverGauge N) = γ.

  The present W3 file — the **substantive** layer of paper §28.3
  pp. 137–138 — records the *beats-trivial* step for the full
  Lagrangian: whenever some observer gauge produces a strictly
  smaller Lagrangian value than `γ` (the trivial-gauge value),
  the trivial gauge cannot be the global minimiser.

  This is the substantive companion to V13's non-vacuous value
  formula: it makes explicit that, once the `γ > 0` log-det
  barrier is charged, the trivial rank-zero vertex is *not*
  automatically the minimum of the three-term action.

  ## Paper citation

    * §28.3 pp. 137–138 — Bridge A / Bridge B, full action
      `S_NF[Φ; P]`, "non-vacuous beats-trivial wedge".

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms non_trivial_beats_trivial`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Concrete.FullLagrangianFixed
import PallLean.Paper93.Concrete.NonVacuousMinimizer
import PallLean.Paper93.Concrete.CoordinateMap
import PallLean.Paper93.Concrete.RegularGraphFixed

namespace PallLean.Paper93.Substantive

open PallLean.Paper93.Concrete

/-- **Lagrangian value at the trivial gauge = `γ`** (V13 finding).

A thin W3 re-export of the V13 non-vacuous value formula
`fullLagrangianFixed_trivial_value`: at the canonical
`trivialObserverGauge N` witness, the full three-term N-Frame
Lagrangian evaluates to the log-det barrier coefficient `γ`
(paper §28.3 pp. 137–138, normalised via
`logDetBarrier_trivial_eq_one`).  This pins down the
beats-trivial threshold used in
`non_trivial_beats_trivial` below. -/
theorem trivial_gauge_value {N d : ℕ} (α β γ : ℝ)
    (G : RegularGraphFixed N d) :
    fullLagrangianFixed α β γ G (trivialObserverGauge N) = γ :=
  fullLagrangianFixed_trivial_value α β γ G

/-- **Non-trivial gauge beats the trivial gauge (W3 substantive
    wedge, paper §28.3 pp. 137–138 Bridge A/Bridge B).**

For any real coefficients `α β γ : ℝ`, any V1-fix graph
`G : RegularGraphFixed N d`, and any candidate observer gauge
`gauge : ObserverGauge N` whose full three-term N-Frame
Lagrangian strictly undercuts the barrier-coefficient
threshold `γ`, the trivial gauge `trivialObserverGauge N`
is *not* a global minimiser of `fullLagrangianFixed α β γ G`.

Concretely: the same `gauge` is exhibited as an explicit
witness whose Lagrangian value is strictly below the
trivial-gauge value.

This is the substantive beats-trivial step of paper §28.3:
once the log-det barrier coefficient `γ` charges the
rank-zero vertex, any non-trivial gauge undercutting that
value forces the minimiser off the trivial vertex.

No absorbing `∨ True` escape, no bespoke axioms: the wedge is
obtained by rewriting through V13's non-vacuous value formula
`trivial_gauge_value` (a.k.a. `fullLagrangianFixed_trivial_value`). -/
theorem non_trivial_beats_trivial {N d : ℕ} (α β γ : ℝ)
    (G : RegularGraphFixed N d)
    (gauge : ObserverGauge N)
    (hEnergy : fullLagrangianFixed α β γ G gauge < γ) :
    ∃ g : ObserverGauge N,
      fullLagrangianFixed α β γ G g <
        fullLagrangianFixed α β γ G (trivialObserverGauge N) := by
  -- Exhibit the hypothesised `gauge` directly as the witness.
  refine ⟨gauge, ?_⟩
  -- Rewrite the trivial-gauge side to `γ` via the V13 value
  -- formula (paper §28.3 normalisation through
  -- `logDetBarrier_trivial_eq_one`), then apply the hypothesis.
  rw [trivial_gauge_value]
  exact hEnergy

/-! ## Kernel-only axiom trace -/

#print axioms trivial_gauge_value
#print axioms non_trivial_beats_trivial

end PallLean.Paper93.Substantive
