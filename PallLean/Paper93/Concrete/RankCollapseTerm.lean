/-
  PallLean/Paper93/Concrete/RankCollapseTerm.lean

  Agent U12 — Paper §28.3 "N-Frame Lagrangian: rank-collapse term".

  ## Scope

  This file packages the rank-collapse Lagrangian term
  `γ · rank(Π(P))` appearing in paper §28.3 Bridge B
  "determinantal barrier ⇒ global rank" (pp. 137–138). We expose:

    * `projectionRank gauge`       — U11 interface: the ℚ-finrank of
                                     `gauge.projection`'s range cast
                                     to `ℝ`;
    * `projectionRank_nonneg`      — non-negativity of that rank;
    * `projectionRank_trivial`     — vanishing at the `trivialGauge`;
    * `rankCollapseTerm γ gauge`   — the coefficient-weighted
                                     rank-collapse term
                                     `γ · projectionRank gauge`;
    * `rankCollapseTerm_nonneg`    — non-negativity of the term under
                                     a non-negative coefficient;
    * `rankCollapseTerm_trivial_zero`
                                   — vanishing of the term at the
                                     `trivialGauge`.

  This completes the concrete packaging of the rank-collapse
  component of the N-Frame Lagrangian.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms rankCollapseTerm_nonneg`:
      [propext, Classical.choice, Quot.sound]

  ## Paper citations

    * §7.1 pp. 25–26 — role of the Global God-Move gauge `Π⋆` and
      the rank-minimizing Lagrangian.
    * §28.3 pp. 137–138 — analytic reformulation: action functional
      `S_NF[Φ; P]` and Bridge B "determinantal barrier ⇒ global rank".
-/
import PallLean.Paper93.NFrame.LagrangianFunctional

namespace PallLean.Paper93.Concrete

/-- **Projection rank** (U11 interface) of a candidate gauge,
cast to `ℝ`.

The ℚ-finrank of the range of `gauge.projection`, viewed as a
non-negative real number. This is the "observer-projected
dimension" quantity used in paper §28.3 Bridge B. -/
noncomputable def projectionRank
    {N : ℕ} (gauge : PallLean.Paper93.NFrame.CandidateGauge N) : ℝ :=
  (Module.finrank ℚ (LinearMap.range gauge.projection) : ℝ)

/-- **Non-negativity of the projection rank.**

`projectionRank gauge` is the ℚ-finrank of `gauge.projection`'s
range cast to `ℝ`, hence non-negative by `Nat.cast_nonneg`. -/
theorem projectionRank_nonneg {N : ℕ}
    {gauge : PallLean.Paper93.NFrame.CandidateGauge N} :
    0 ≤ projectionRank gauge := by
  unfold projectionRank
  exact Nat.cast_nonneg _

/-- **Vanishing of the projection rank at the trivial gauge.**

`trivialGauge N` has projection `= 0`, whose range is `⊥` and
whose ℚ-finrank is `0`. Hence `projectionRank (trivialGauge N) = 0`. -/
theorem projectionRank_trivial {N : ℕ} :
    projectionRank (PallLean.Paper93.NFrame.trivialGauge N) = 0 := by
  unfold projectionRank
  -- `trivialGauge N` has `projection := 0`; its range is `⊥`.
  show (Module.finrank ℚ
          (LinearMap.range
            (PallLean.Paper93.NFrame.trivialGauge N).projection) : ℝ) = 0
  have hrange : LinearMap.range
      (PallLean.Paper93.NFrame.trivialGauge N).projection = ⊥ := by
    -- `(trivialGauge N).projection = 0` by definition.
    show LinearMap.range
        (0 : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ) = ⊥
    exact LinearMap.range_zero
  rw [hrange]
  -- `Module.finrank ℚ (⊥ : Submodule ℚ _) = 0`.
  simp

/-- **Rank-collapse Lagrangian term** at coefficient `γ`.

Paper §28.3 Bridge B (pp. 137–138): the determinantal barrier
lower-bounds the global rank of the SPDP row space; the
rank-collapse term in the Lagrangian is the coefficient-weighted
rank proxy `γ · rank(Π(P))`.

Here we use `projectionRank gauge` (the ℚ-finrank of `gauge.projection`'s
range, cast to `ℝ`) as the concrete "rank(Π(P))" quantity. -/
noncomputable def rankCollapseTerm {N : ℕ} (γ : ℝ)
    (gauge : PallLean.Paper93.NFrame.CandidateGauge N) : ℝ :=
  γ * projectionRank gauge

/-- **Non-negativity of the rank-collapse term** under a non-negative
coefficient `γ ≥ 0`. Paper §28.3 p. 137: all additive components of
the N-Frame Lagrangian are non-negative by construction. -/
theorem rankCollapseTerm_nonneg {N : ℕ} {γ : ℝ}
    {gauge : PallLean.Paper93.NFrame.CandidateGauge N}
    (hγ : 0 ≤ γ) : 0 ≤ rankCollapseTerm (N := N) γ gauge :=
  mul_nonneg hγ projectionRank_nonneg

/-- **Vanishing of the rank-collapse term at the trivial gauge.**

Paper §28.3 Euler–Lagrange conditions (p. 137): the degenerate
rank-zero starting vertex of the variational problem has vanishing
rank-collapse contribution. -/
theorem rankCollapseTerm_trivial_zero {N : ℕ} {γ : ℝ} :
    rankCollapseTerm γ (PallLean.Paper93.NFrame.trivialGauge N) = 0 := by
  unfold rankCollapseTerm
  rw [projectionRank_trivial, mul_zero]

end PallLean.Paper93.Concrete
