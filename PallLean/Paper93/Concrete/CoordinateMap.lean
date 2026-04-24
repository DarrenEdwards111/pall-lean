/-
  PallLean/Paper93/Concrete/CoordinateMap.lean

  Agent U3 — Paper §28.3 "N-Frame Lagrangian: observer coordinatization".

  ## Scope

  This file adds a *coordinate map* field to the `CandidateGauge`
  structure of `PallLean.Paper93.NFrame.LagrangianFunctional`,
  parametrizing the observer-consistent gauge by a concrete
  coordinate function `Φ : Fin N → ℝ`. The coordinate map corresponds
  to the observer's per-vertex coordinatization appearing in the
  paper's action

      S_NF[Φ; P]
        = α ∑_{{u,v} ∈ E_n} (Φ_u - Φ_v)^2
        + β ∑_{v ∈ V_n} (1 - χ(v) · sgn Φ_v)_+
        + λ · B(A(P))

  (paper §28.3 pp. 137–138), where `Φ : V_n → ℝ` is the scalar field
  on the expander vertex set `V_n`. Identifying `V_n` with `Fin N`,
  the observer's coordinate function is precisely a map
  `Fin N → ℝ`.

  At the Lean level we introduce:

    * `CoordMap N` — an inhabited wrapper around `Fin N → ℝ`;
    * `trivialCoord N` — the degenerate all-zeros coordinate map
      (the origin of the observer-coordinate space);
    * `ObserverGauge N` — a `CandidateGauge N` extended with a
      `CoordMap N` field, i.e. an observer-consistent gauge with
      attached coordinate data;
    * `trivialObserverGauge N` — the degenerate observer gauge built
      from `trivialGauge N` and `trivialCoord N`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms trivialObserverGauge`:
      [propext, Classical.choice, Quot.sound]

  ## Paper citations

    * §7.1 pp. 25–26 — role of the Global God-Move gauge `Π⋆` and
      observer-consistency.
    * §28.3 pp. 137–138 — analytic reformulation: action functional
      `S_NF[Φ; P]` and the observer coordinate field
      `Φ : V_n → ℝ`.
-/
import PallLean.Paper93.NFrame.LagrangianFunctional

namespace PallLean
namespace Paper93
namespace Concrete

/-- **Coordinate map**: represents the observer's coordinatization
per vertex.

Paper §28.3 pp. 137–138: the action `S_NF[Φ; P]` depends on a scalar
field `Φ : V_n → ℝ` on the expander vertex set. Identifying
`V_n` with `Fin N`, we encode the observer's coordinate data as a
function `Fin N → ℝ`. -/
structure CoordMap (N : ℕ) where
  /-- Per-vertex coordinate values `Φ_v ∈ ℝ`. -/
  values : Fin N → ℝ

/-- **Trivial coordinate map** (all zeros).

Paper §28.3 Euler–Lagrange conditions p. 137: the zero field
`Φ ≡ 0` is the degenerate starting point of the observer-coordinate
descent leading to the universal gauge `Π⋆`. -/
def trivialCoord (N : ℕ) : CoordMap N := ⟨fun _ => 0⟩

/-- **Observer-consistent gauge with attached coordinate map**.

An `ObserverGauge N` is a `CandidateGauge N` (a linear projection on
the SPDP row space satisfying idempotence and finite-rank range,
paper §7.1 p. 25 / §28.3 p. 137) together with an explicit
observer coordinate map `Φ : Fin N → ℝ`. This structure provides the
coordinatized form of the candidate gauges appearing in the N-Frame
Lagrangian action `S_NF[Φ; P]` of paper §28.3 pp. 137–138. -/
structure ObserverGauge (N : ℕ)
    extends PallLean.Paper93.NFrame.CandidateGauge N where
  /-- Observer coordinate map `Φ : Fin N → ℝ`. -/
  coord : CoordMap N

/-- **Trivial observer gauge**: the degenerate rank-zero candidate
gauge paired with the all-zeros coordinate map.

Paper §28.3 Euler–Lagrange conditions p. 137: this is the degenerate
"rank-zero, zero-field" starting vertex of the coupled
gauge/coordinate variational problem, from which gradient descent
onto the universal observer gauge `Π⋆` with its canonical coordinate
field begins. -/
noncomputable def trivialObserverGauge (N : ℕ) : ObserverGauge N :=
  ⟨PallLean.Paper93.NFrame.trivialGauge N, trivialCoord N⟩

/-! ## Kernel-only sanity checks

We export the expected shape for downstream `#print axioms` audits.
The public deliverables below depend only on Mathlib kernel-only
primitives (`propext`, `Classical.choice`, `Quot.sound`). -/

-- Sanity `example`s (these are just to exercise the public API
-- at elaboration time).
example (N : ℕ) : CoordMap N := trivialCoord N
noncomputable example (N : ℕ) : ObserverGauge N := trivialObserverGauge N

end Concrete
end Paper93
end PallLean
