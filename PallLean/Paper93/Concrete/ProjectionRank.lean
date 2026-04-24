/-
  PallLean/Paper93/Concrete/ProjectionRank.lean

  U11 — Concrete rank-of-projection measure for the rank-collapse
  Lagrangian term (paper §28.3 Bridge B: "determinantal barrier ⇒
  global rank").

  ## Scope

  This file isolates the *concrete* ℝ-valued rank measure
  `projectionRank gauge := (Module.finrank ℚ (range gauge.projection) : ℝ)`
  that already appears inside the abstract
  `Lagrangian.rankCollapsePenalty` of
  `PallLean/Paper93/NFrame/LagrangianFunctional.lean`, and
  pairs it with two basic structural lemmas:

    * `projectionRank_nonneg` — the rank, viewed as a real number, is
      non-negative (`Nat.cast_nonneg`);
    * `projectionRank_trivial` — the zero projection has rank `0`
      (via Mathlib's `finrank_bot` for submodules).

  These facts capture the paper's "rank-zero vertex" of the variational
  problem (paper §28.3 Euler–Lagrange conditions, p. 137): the trivial
  gauge `Π = 0` is the starting point of the gradient descent onto the
  Global God-Move projection `Π⋆`, where the rank-collapse penalty is
  minimised. The ℝ-valued projection-rank is the direct proxy for
  Bridge B's "global rank" quantity.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build PallLean.Paper93.Concrete.ProjectionRank`.

  Expected `#print axioms projectionRank_trivial`:
      [propext, Classical.choice, Quot.sound]

  ## Paper citations

    * §7.1 pp. 25–26 — the universal observer gauge `Π⋆` and its
      rank-minimising variational description.
    * §28.3 pp. 137–138 — N-Frame Lagrangian, Bridge B
      (determinantal barrier ⇒ global rank).
-/

import PallLean.Paper93.NFrame.LagrangianFunctional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace PallLean.Paper93.Concrete

open MvPolynomial

/-- **Concrete projection rank** of a candidate gauge.

The rank-collapse Lagrangian term of paper §28.3 (Bridge B
"determinantal barrier ⇒ global rank") is proxied concretely by the
ℚ-dimension of the range of the gauge's projection, cast to a real
number. This matches the `rankCollapsePenalty` term already used
inside `Lagrangian.rankCollapsePenalty` of
`PallLean/Paper93/NFrame/LagrangianFunctional.lean`.

Paper p. 25 §7.1: a candidate gauge `Π` is a linear projection on the
ambient SPDP row space, and its "rank" is the ℚ-dimension of its
range. The universal God-Move projection `Π⋆` is the rank-minimiser
of the admissible set of such gauges (paper §28.3 Euler–Lagrange
conditions, p. 137). -/
noncomputable def projectionRank {N : ℕ}
    (gauge : PallLean.Paper93.NFrame.CandidateGauge N) : ℝ :=
  (Module.finrank ℚ (LinearMap.range gauge.projection) : ℝ)

/-- The concrete projection rank is non-negative.

Paper §28.3 p. 137: the rank-collapse Lagrangian term is a
non-negative component of the N-Frame action `S_NF[Φ; P]`. This is
immediate from `Nat.cast_nonneg` on the ℕ-valued `Module.finrank`. -/
theorem projectionRank_nonneg
    {N : ℕ} {gauge : PallLean.Paper93.NFrame.CandidateGauge N} :
    0 ≤ projectionRank (N := N) gauge :=
  Nat.cast_nonneg _

/-- The trivial zero gauge has projection rank `0`.

Paper §28.3 p. 137 Euler–Lagrange conditions: the "rank-zero vertex"
of the variational problem is the trivial gauge `Π = 0`, whose range
is `⊥` and whose ℚ-dimension is `0`. This matches
`Lagrangian.rankCollapsePenalty_trivialGauge`-type identities used
throughout the NFrame chain, and provides the base case for the
admissible Lagrangian infimum `lagrangianNatMin N = 0`
(cf. `PallLean/Paper93/NFrame/PSideCollapse.lean`). -/
theorem projectionRank_trivial {N : ℕ} :
    projectionRank (PallLean.Paper93.NFrame.trivialGauge N) = 0 := by
  unfold projectionRank PallLean.Paper93.NFrame.trivialGauge
  -- `LinearMap.range (0 : V →ₗ V) = ⊥`, and `finrank ⊥ = 0`.
  have hrange :
      LinearMap.range
        (0 : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ) = ⊥ :=
    LinearMap.range_zero
  rw [hrange]
  -- `finrank ℚ (⊥ : Submodule ℚ _) = 0`, cast to ℝ.
  rw [finrank_bot ℚ (MvPolynomial (Fin N) ℚ)]
  exact_mod_cast rfl

end PallLean.Paper93.Concrete
