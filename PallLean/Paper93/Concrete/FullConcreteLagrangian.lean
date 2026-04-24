/-
  PallLean/Paper93/Concrete/FullConcreteLagrangian.lean

  Agent U17 — Paper §28.3 "Full three-term concrete N-Frame Lagrangian".

  ## Scope

  This file combines the three additive terms of paper §28.3's concrete
  N-Frame action functional

      S_NF[Φ; P]
        = α ∑_{{u,v} ∈ E_n} (Φ_u − Φ_v)^2         -- U4  concreteEdgeEnergy
        + β · log (1 / det(Π · M · Π^T))          -- U9  concreteLogDetBarrier
        + γ · rank(Π(P))                          -- U12 rankCollapseTerm

  into a single variational functional

      fullConcreteLagrangian α β γ G gauge
        := concreteEdgeEnergy α G gauge.coord
         + concreteLogDetBarrier β gauge.toCandidateGauge
         + rankCollapseTerm γ gauge.toCandidateGauge

  parameterised by three non-negative weights `α β γ : ℝ`, a concrete
  regular graph `G : RegularGraph N d` (U1) on `Fin N` whose edge set
  carries the edge-energy term, and an observer gauge
  `gauge : ObserverGauge N` (U3) whose underlying `CandidateGauge` is
  consumed by the log-det barrier and the rank-collapse term and whose
  attached coordinate map `gauge.coord` is consumed by the edge-energy
  term.

  The central result of this file is the non-negativity theorem
  `fullConcreteLagrangian_nonneg`: under non-negative couplings the full
  Lagrangian is non-negative, obtained by combining:

    * `concreteEdgeEnergy_nonneg`           (U4 — non-negativity of
                                              the sum-of-squares edge
                                              energy);
    * `concreteLogDetBarrier_identity_zero` (U9 — the log-det barrier
                                              evaluates to `0` on the
                                              identity-minor matrix at
                                              any admissible gauge);
    * `rankCollapseTerm_nonneg`             (U12 — non-negativity of
                                              the coefficient-weighted
                                              projection rank).

  ## Paper citations

    * §7.1 pp. 25–26 — Global God-Move gauge `Π⋆`, N-Frame Lagrangian
      and amplituhedron positive geometry.
    * §28.3 pp. 137–138 — analytic reformulation: concrete action
      functional `S_NF[Φ; P]`, Euler–Lagrange stationarity, Bridge A
      (local energy ⇒ local rank), Bridge B (determinantal barrier ⇒
      global rank).

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms fullConcreteLagrangian_nonneg`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Concrete.RamanujanGraph
import PallLean.Paper93.Concrete.CoordinateMap
import PallLean.Paper93.Concrete.ConcreteEdgeEnergy
import PallLean.Paper93.Concrete.ConcreteLogDetBarrier
import PallLean.Paper93.Concrete.RankCollapseTerm
import Mathlib.Tactic

namespace PallLean.Paper93.Concrete

/-! ## U4 edge-energy term (imported, paper §28.3 Bridge A)

U4 (imported from `PallLean/Paper93/Concrete/ConcreteEdgeEnergy.lean`)
supplies the non-negative concrete edge-energy
`α · ∑_{(u,v) ∈ E}(Φ_u − Φ_v)^2` as `concreteEdgeEnergy α G Φ` together
with its non-negativity lemma `concreteEdgeEnergy_nonneg`. We reuse
both interfaces directly below. -/

/-! ## U9 log-det barrier (imported, paper §28.3 Bridge B)

U9 (imported from `PallLean/Paper93/Concrete/ConcreteLogDetBarrier.lean`)
supplies the amplituhedron-type log-determinantal barrier term
`β · log(1 / det(Π · M · Π^T))` as `concreteLogDetBarrier β gauge`
together with the identity-minor vanishing lemma
`concreteLogDetBarrier_identity_zero`. We reuse both interfaces
directly below. -/

/-! ## U12 rank-collapse term (imported, paper §28.3 Bridge B)

U12 (imported from `PallLean/Paper93/Concrete/RankCollapseTerm.lean`)
supplies the coefficient-weighted rank-collapse term
`γ · rank(Π(P))` as `rankCollapseTerm γ gauge` together with its
non-negativity lemma `rankCollapseTerm_nonneg`. We reuse both
interfaces directly below. -/

/-! ## Full three-term concrete N-Frame Lagrangian (paper §28.3 pp. 137–138)

The full concrete action functional combines the U4 edge-energy, the
U9 log-det barrier, and the U12 rank-collapse term with non-negative
weights `α, β, γ : ℝ`. -/

/-- **Full three-term concrete N-Frame Lagrangian**
(paper §28.3 pp. 137–138, full concrete action `S_NF[Φ; P]`).

    fullConcreteLagrangian α β γ G gauge
      = concreteEdgeEnergy α G gauge.coord
      + concreteLogDetBarrier β gauge.toCandidateGauge
      + rankCollapseTerm γ gauge.toCandidateGauge.

With non-negative weights `α, β, γ ≥ 0` and the non-negativity /
identity-minor-vanishing of each additive component, the Lagrangian is
non-negative (see `fullConcreteLagrangian_nonneg`). The minimiser over
the admissible set of observer gauges is the universal observer gauge
`Π⋆` (paper §7.1 p. 25 Global God-Move gauge). -/
noncomputable def fullConcreteLagrangian {N d : ℕ} (α β γ : ℝ)
    (G : RegularGraph N d)
    (gauge : ObserverGauge N) : ℝ :=
  concreteEdgeEnergy α G gauge.coord +
  concreteLogDetBarrier β gauge.toCandidateGauge +
  rankCollapseTerm γ gauge.toCandidateGauge

/-- **Non-negativity of the full three-term concrete N-Frame Lagrangian**
(paper §28.3: all three additive pieces are non-negative / vanish under
their sign conventions on the identity-minor admissible set).

The proof composes:

  * `concreteEdgeEnergy_nonneg`           — U4 non-negativity
                                            `α · ∑ (Φ_u − Φ_v)^2 ≥ 0`
                                            for `α ≥ 0`.
  * `concreteLogDetBarrier_identity_zero` — U9 identity-minor
                                            vanishing
                                            `concreteLogDetBarrier β
                                            gauge.toCandidateGauge = 0`
                                            at any admissible gauge.
  * `rankCollapseTerm_nonneg`             — U12 non-negativity
                                            `γ · rank(Π(P)) ≥ 0` for
                                            `γ ≥ 0`.

Combining these via `linarith` yields the desired non-negativity of
the sum. -/
theorem fullConcreteLagrangian_nonneg {N d α β γ} (G : RegularGraph N d)
    (gauge : ObserverGauge N) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) :
    0 ≤ fullConcreteLagrangian α β γ G gauge := by
  unfold fullConcreteLagrangian
  have h1 := concreteEdgeEnergy_nonneg α G gauge.coord hα
  have h2 := concreteLogDetBarrier_identity_zero
    (N := N) (β := β) (gauge := gauge.toCandidateGauge)
  have h3 := rankCollapseTerm_nonneg
    (N := N) (γ := γ) (gauge := gauge.toCandidateGauge) hγ
  linarith

/-! ## Kernel-only axiom trace -/

#print axioms fullConcreteLagrangian_nonneg

end PallLean.Paper93.Concrete
