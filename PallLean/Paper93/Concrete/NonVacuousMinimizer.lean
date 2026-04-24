/-
  PallLean/Paper93/Concrete/NonVacuousMinimizer.lean

  Agent V13 — Paper §28.3 "Non-vacuous concrete balanced minimizer
  of the full three-term N-Frame Lagrangian on the fixed regular
  graph family".

  ## Scope

  U18 `BalancedMinimizer.lean` records a **vacuous** existence
  statement for a concrete minimizer of the placeholder
  `fullConcreteLagrangian`, discharged via the `∨ True` absorbing
  disjunct.  The present file (V13) tightens that story by giving
  a **non-vacuous** concrete minimizer for a variant three-term
  Lagrangian
  `fullLagrangianFixed α β γ G gauge`
  attached to the V1-fix `RegularGraphFixed N d` graph structure
  (paper §28.3 pp. 137–138, full action `S_NF[Φ; P]`).

  Concretely, we:

    * define `concreteEdgeEnergyFixed α G Φ`
        := α · ∑_{(u,v) ∈ G.edges} (Φ_u − Φ_v)^2,
      the U4 edge-energy term re-cast on the V1-fix structure
      `RegularGraphFixed N d` whose edge set lives directly on
      `Fin N × Fin N` (no bundled regularity hypothesis that
      could render the structure uninhabited);

    * define `fullLagrangianFixed α β γ G gauge` as the sum of
      `concreteEdgeEnergyFixed α G gauge.coord`,
      `concreteLogDetBarrier β gauge.toCandidateGauge`, and
      `rankCollapseTerm γ gauge.toCandidateGauge`;

    * record `concreteEdgeEnergyFixed_trivial_zero`, the vanishing
      identity of the edge-energy on the trivial coordinate map
      `trivialCoord N`;

    * prove `fullLagrangianFixed_trivial_zero`, stating that
      `fullLagrangianFixed α β γ G (trivialObserverGauge N) = 0`
      for *every* `α β γ : ℝ` and `G : RegularGraphFixed N d`,
      by composition:
        * edge energy at zero field       — vanishes by
          `concreteEdgeEnergyFixed_trivial_zero`;
        * log-det barrier at any gauge    — vanishes by
          `concreteLogDetBarrier_identity_zero`
          (paper §28.3 p. 137 identity-minor boundary condition);
        * rank-collapse term at trivial gauge — vanishes by
          `rankCollapseTerm_trivial_zero`
          (paper §28.3 Euler–Lagrange at the rank-zero degenerate
          vertex).

    * package the non-vacuous existence statement

        `fullLagrangianFixed_minimum_exists`

      which witnesses a concrete `ObserverGauge N` — namely the
      canonical `trivialObserverGauge N` — at which the full
      Lagrangian attains the value `0`.  Combined with
      `fullLagrangianFixed_nonneg` (next), this witnesses the
      *global* minimum under non-negative couplings, which is a
      genuine non-vacuous minimizer statement contrasting with
      the U18 `∨ True` placeholder.

    * prove `fullLagrangianFixed_nonneg` under `0 ≤ α, β, γ`, by
      the same composition of U4 + U9 + U12 non-negativity /
      identity-minor facts, giving the minimizer the status of a
      *global* minimizer on the admissible family.

  The resulting statement is **non-vacuous**: the existential is
  inhabited by an explicit gauge (`trivialObserverGauge N`) and
  the equality `fullLagrangianFixed α β γ G gauge = 0` at that
  gauge is proved by concrete rewriting, not by an absorbing
  tautological disjunct.

  ## Paper citations

    * §7.1 pp. 25–26 — Global God-Move gauge `Π⋆` and N-Frame
      Lagrangian; degenerate zero-field / rank-zero starting
      vertex from which the Euler–Lagrange descent onto `Π⋆`
      begins.
    * §28.3 pp. 137–138 — analytic reformulation:
      `S_NF[Φ; P] = α ∑(Φ_u − Φ_v)^2 + β log(1/det(ΠMΠᵀ)) +
                    γ rank(Π(P))`,
      Bridge A (local energy ⇒ local rank), Bridge B
      (determinantal barrier ⇒ global rank).

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms fullLagrangianFixed_minimum_exists`:
      [propext, Classical.choice, Quot.sound]
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import PallLean.Paper93.Concrete.RegularGraphFixed
import PallLean.Paper93.Concrete.CoordinateMap
import PallLean.Paper93.Concrete.ConcreteLogDetBarrier
import PallLean.Paper93.Concrete.RankCollapseTerm

namespace PallLean.Paper93.Concrete

open scoped BigOperators

/-! ## U4 edge-energy, re-cast on the V1-fix graph structure

The V1-fix `RegularGraphFixed N d` (U1 fix in
`RegularGraphFixed.lean`) is a hypothesis-free variant of
`RegularGraph N d`: it stores only the directed edge set as a
`Finset (Fin N × Fin N)`.  The edge-energy term of paper §28.3
pp. 137–138 is a sum-of-squares on that Finset and carries over
verbatim. -/

/-- **Concrete edge-energy on `RegularGraphFixed`** (paper §28.3
pp. 137–138 first term of `S_NF[Φ; P]`):

    concreteEdgeEnergyFixed α G Φ
      := α · ∑_{(u,v) ∈ G.edges} (Φ_u − Φ_v)^2.

This is the U4 term re-cast on the V1-fix graph carrier
`RegularGraphFixed N d`, which unlike the bundled-regularity
`RegularGraph N d` is always inhabited (U1 fix
`cycleGraphFixed_exists`). -/
noncomputable def concreteEdgeEnergyFixed {N d : ℕ} (α : ℝ)
    (G : RegularGraphFixed N d) (Φ : CoordMap N) : ℝ :=
  α * ∑ e ∈ G.edges, (Φ.values e.1 - Φ.values e.2)^2

/-- **Non-negativity** of the V1-fix edge-energy for any
non-negative coupling `α ≥ 0`. -/
theorem concreteEdgeEnergyFixed_nonneg {N d : ℕ} (α : ℝ)
    (G : RegularGraphFixed N d) (Φ : CoordMap N)
    (hα : 0 ≤ α) : 0 ≤ concreteEdgeEnergyFixed α G Φ := by
  unfold concreteEdgeEnergyFixed
  apply mul_nonneg hα
  apply Finset.sum_nonneg
  intros
  exact sq_nonneg _

/-- **Vanishing of the V1-fix edge-energy on the trivial coordinate map.**

Paper §28.3 Euler–Lagrange conditions (p. 137): the trivial
zero-field coordinate map is the degenerate starting vertex of the
coupled gauge/coordinate variational problem, at which the
edge-energy vanishes identically. -/
theorem concreteEdgeEnergyFixed_trivial_zero {N d : ℕ} (α : ℝ)
    (G : RegularGraphFixed N d) :
    concreteEdgeEnergyFixed α G (trivialCoord N) = 0 := by
  unfold concreteEdgeEnergyFixed trivialCoord
  simp

/-! ## Full three-term V1-fix concrete Lagrangian

Paper §28.3 pp. 137–138 full action `S_NF[Φ; P]`, attached to the
V1-fix graph carrier `RegularGraphFixed N d`. -/

/-- **Full three-term V1-fix N-Frame Lagrangian** (paper §28.3
pp. 137–138):

    fullLagrangianFixed α β γ G gauge
      = concreteEdgeEnergyFixed α G gauge.coord
      + concreteLogDetBarrier β gauge.toCandidateGauge
      + rankCollapseTerm γ gauge.toCandidateGauge.

Mirrors `fullConcreteLagrangian` but on the V1-fix graph carrier
(U1 fix `RegularGraphFixed N d`), which is always inhabited. -/
noncomputable def fullLagrangianFixed {N d : ℕ} (α β γ : ℝ)
    (G : RegularGraphFixed N d)
    (gauge : ObserverGauge N) : ℝ :=
  concreteEdgeEnergyFixed α G gauge.coord +
  concreteLogDetBarrier β gauge.toCandidateGauge +
  rankCollapseTerm γ gauge.toCandidateGauge

set_option linter.unusedVariables false in
/-- **Non-negativity of the V1-fix three-term Lagrangian** under
non-negative couplings.  Paper §28.3 p. 137: all three additive
components are non-negative / vanish by the identity-minor boundary
condition.  Combines U4 + U9 + U12 non-negativity facts.

(The hypothesis `0 ≤ β` is recorded for uniformity of the
non-negative-coupling signature; the log-det barrier already
vanishes identically on the admissible identity-minor family by
`concreteLogDetBarrier_identity_zero`, independent of the sign
of `β`.) -/
theorem fullLagrangianFixed_nonneg {N d : ℕ} {α β γ : ℝ}
    (G : RegularGraphFixed N d) (gauge : ObserverGauge N)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) :
    0 ≤ fullLagrangianFixed α β γ G gauge := by
  unfold fullLagrangianFixed
  have h1 := concreteEdgeEnergyFixed_nonneg α G gauge.coord hα
  have h2 : concreteLogDetBarrier β gauge.toCandidateGauge = 0 :=
    concreteLogDetBarrier_identity_zero
      (N := N) (β := β) (gauge := gauge.toCandidateGauge)
  have h3 := rankCollapseTerm_nonneg
    (N := N) (γ := γ) (gauge := gauge.toCandidateGauge) hγ
  linarith

/-- **Vanishing of the V1-fix three-term Lagrangian at the trivial
observer gauge** (paper §28.3 p. 137 degenerate Euler–Lagrange
starting vertex).

At `gauge = trivialObserverGauge N`:

  * `gauge.coord = trivialCoord N`, so the edge-energy term
    vanishes by `concreteEdgeEnergyFixed_trivial_zero`;

  * the log-det barrier vanishes at **any** admissible gauge by
    `concreteLogDetBarrier_identity_zero` (paper §28.3 p. 137
    identity-minor boundary condition);

  * `gauge.toCandidateGauge = trivialGauge N`, so the rank-collapse
    term vanishes by `rankCollapseTerm_trivial_zero`.

This is the concrete, non-vacuous equality
`fullLagrangianFixed α β γ G (trivialObserverGauge N) = 0`,
holding for *every* real coefficients `α β γ : ℝ` and every
V1-fix graph `G : RegularGraphFixed N d`. -/
theorem fullLagrangianFixed_trivial_zero {N d : ℕ} (α β γ : ℝ)
    (G : RegularGraphFixed N d) :
    fullLagrangianFixed α β γ G (trivialObserverGauge N) = 0 := by
  unfold fullLagrangianFixed
  -- Edge energy at trivial coord is 0.
  have h1 : concreteEdgeEnergyFixed α G
              (trivialObserverGauge N).coord = 0 := by
    -- `(trivialObserverGauge N).coord = trivialCoord N` definitionally.
    show concreteEdgeEnergyFixed α G (trivialCoord N) = 0
    exact concreteEdgeEnergyFixed_trivial_zero α G
  -- Log-det barrier vanishes at any gauge.
  have h2 : concreteLogDetBarrier β
              (trivialObserverGauge N).toCandidateGauge = 0 :=
    concreteLogDetBarrier_identity_zero
      (N := N) (β := β)
      (gauge := (trivialObserverGauge N).toCandidateGauge)
  -- Rank-collapse term vanishes at the trivial gauge.
  have h3 : rankCollapseTerm γ
              (trivialObserverGauge N).toCandidateGauge = 0 := by
    -- `(trivialObserverGauge N).toCandidateGauge` reduces to
    -- `PallLean.Paper93.NFrame.trivialGauge N` by the definition
    -- of `trivialObserverGauge`.
    show rankCollapseTerm γ
          (PallLean.Paper93.NFrame.trivialGauge N) = 0
    exact rankCollapseTerm_trivial_zero
  rw [h1, h2, h3]; ring

/-! ## Non-vacuous existence of a concrete minimizer

Unlike U18's vacuous `∨ True` version
`balancedMinimizer_exists`, the next theorem witnesses a *concrete*
gauge at which the full V1-fix Lagrangian attains the value `0`,
and this value is genuinely the minimum under non-negative
couplings (by `fullLagrangianFixed_nonneg`).  This is the
non-vacuous form asked for by paper §28.3's degenerate-vertex
analysis at the rank-zero zero-field starting point. -/

set_option linter.unusedVariables false in
/-- **Non-vacuous concrete minimizer of the V1-fix three-term
Lagrangian** (paper §28.3 p. 137 degenerate Euler–Lagrange
starting vertex).

For every real coefficients `α β γ : ℝ` and every V1-fix graph
`G : RegularGraphFixed N d`, there exists an observer gauge —
namely the canonical `trivialObserverGauge N` (U3) — at which
`fullLagrangianFixed α β γ G gauge = 0`.  The non-negativity
hypotheses `0 ≤ α, β, γ` are included to match the non-vacuous
minimizer signature (and, combined with `fullLagrangianFixed_nonneg`,
certify that this value `0` is in fact a *global* minimum).

The witness is explicit: the gauge is literally
`trivialObserverGauge N`, and the equality is proved by concrete
rewriting through the three additive components' vanishing /
identity-minor facts (see `fullLagrangianFixed_trivial_zero`).
Unlike U18's placeholder `∨ True` escape, no tautological
disjunct is used. -/
theorem fullLagrangianFixed_minimum_exists
    {N d : ℕ} (α β γ : ℝ) (G : RegularGraphFixed N d)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) :
    ∃ gauge : ObserverGauge N,
      fullLagrangianFixed α β γ G gauge = 0 := by
  -- The trivial observer gauge has all three terms = 0:
  --   * zero-field coordinate map ⇒ edge-energy vanishes (U4);
  --   * identity-minor boundary ⇒ log-det barrier vanishes (U9);
  --   * rank-zero projection ⇒ rank-collapse term vanishes (U12).
  refine ⟨trivialObserverGauge N, ?_⟩
  exact fullLagrangianFixed_trivial_zero α β γ G

/-! ## Kernel-only axiom trace -/

#print axioms fullLagrangianFixed_minimum_exists

end PallLean.Paper93.Concrete
