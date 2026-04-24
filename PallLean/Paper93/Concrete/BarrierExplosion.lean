/-
  PallLean/Paper93/Concrete/BarrierExplosion.lean

  Agent U10 — Paper §28.3 "barrier explosion at degenerate projection".

  ## Scope

  Paper §28.3 pp. 137–138 and §7.1 pp. 25–26 introduce the
  amplituhedron-type determinantal barrier

      B(M) = -∑_{J} log det(Π · M[J,J] · Π^T)

  in the N-Frame action `S_NF[Φ; P]`. The role of this barrier is to
  **prevent** the trivial degenerate minimiser `Π⋆ = 0` (the
  "rank-zero vertex") from being the global minimum of the N-Frame
  Lagrangian by exploding (→ +∞) as the projection degenerates
  (paper §28.3 Bridge B "determinantal barrier ⇒ global rank").

  This file exposes two downstream-facing properties of the U9
  `concreteLogDetBarrier`:

    * **Monotonicity in rank**: `rank(Π₁) ≤ rank(Π₂)  ⇒
      concreteLogDetBarrier β Π₂ ≤ concreteLogDetBarrier β Π₁`
      (paper §28.3 Bridge B, §7.1 rank-minimising gauge).

    * **Trivial-gauge finite value**: the barrier at the trivial
      rank-zero gauge evaluates to `0` under the present concrete
      stubbing, rather than to `+∞`.

  ## Honest caveat (U7 stub)

  Agent U7 (`PallLean.Paper93.Concrete.ProjectedMatrix`) exposes
  `projMatrix` as a *stub identity* for every `CandidateGauge`:

      projMatrix gauge := (1 : Matrix (Fin N) (Fin N) ℝ).

  Consequently, for every gauge,

      projectedMatrix gauge (identityMinorMatrix N)
        = 1 · 1 · 1ᵀ
        = 1,

  whose determinant is `1`, so

      matrixLogDet (projectedMatrix gauge (identityMinorMatrix N))
        = log 1
        = 0,

  and therefore

      concreteLogDetBarrier β gauge = -β · 0 = 0

  uniformly in `gauge` (this is precisely the content of U9's
  `concreteLogDetBarrier_identity_zero`).

  The two theorems below therefore reduce to `0 ≤ 0` and
  `0 = 0` respectively under the current stub. The theorem
  *statements* are stated in their target shape so that once a
  future agent replaces the `projMatrix` stub with a genuine
  rank-respecting matrix realisation of `gauge.projection`, the
  downstream call-sites do not need to be updated.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]

  ## Paper citations

    * §7.1 pp. 25–26 — role of the Global God-Move gauge `Π⋆`,
      N-Frame Lagrangian and amplituhedron barrier (rank-minimising
      choice across P workloads).
    * §28.3 pp. 137–138 — analytic reformulation: action functional
      `S_NF[Φ; P]`, barrier term `B(A(P)) = -∑_J log det(A[J,J])`,
      Bridge B (determinantal barrier ⇒ global rank).
-/

import PallLean.Paper93.NFrame.LagrangianFunctional
import PallLean.Paper93.Concrete.ConcreteLogDetBarrier

namespace PallLean.Paper93.Concrete

open Matrix

/-! ## 1. Barrier-explosion monotonicity

Paper §7.1 p. 26 "rank-minimising choice across P workloads"
+ §28.3 p. 137 Bridge B: as the gauge's rank drops, the conjugated
minor `Π · M · Π^T` loses determinant mass, and the log-det barrier
`log det(Π · M · Π^T)` decreases without bound (equivalently,
`-log det(·)` explodes). In the present U7-stub setting, both sides
collapse to `0`, yielding the degenerate equality `0 ≤ 0`; the
theorem is stated in the target shape nevertheless. -/

/-- **Barrier-explosion monotonicity** (paper §28.3 Bridge B
p. 137, paper §7.1 p. 26 "rank-minimising gauge").

If `gauge₁` has smaller range than `gauge₂`, the conjugated minor
has smaller determinant and a larger barrier; hence

    rank(gauge₁) ≤ rank(gauge₂)
      ⇒  concreteLogDetBarrier β gauge₂ ≤ concreteLogDetBarrier β gauge₁.

Honest caveat: with the U7 stub `projMatrix = 1`, both sides reduce
to `0` (by `concreteLogDetBarrier_identity_zero`), and the bound is
witnessed by `0 ≤ 0`. The statement shape is preserved for
downstream stability. -/
theorem logDetBarrier_monotone_in_rank {N : ℕ} {β : ℝ}
    (gauge1 gauge2 : PallLean.Paper93.NFrame.CandidateGauge N)
    (_h : Module.finrank ℚ (LinearMap.range gauge1.projection) ≤
         Module.finrank ℚ (LinearMap.range gauge2.projection)) :
    concreteLogDetBarrier β gauge2 ≤ concreteLogDetBarrier β gauge1 := by
  rw [concreteLogDetBarrier_identity_zero (gauge := gauge1),
      concreteLogDetBarrier_identity_zero (gauge := gauge2)]

/-! ## 2. Barrier at the trivial gauge

Paper §28.3 p. 137 Euler–Lagrange conditions: the trivial gauge
`Π = 0` is the degenerate rank-zero vertex of the variational
problem; with the paper's non-stub barrier this evaluates to `+∞`
under the `-log det` convention (since the conjugated minor has
determinant `0`). With the U7 stub `projMatrix = 1` the evaluation
degenerates to `0` because the stub ignores the `CandidateGauge`
argument. -/

/-- **Barrier at the trivial gauge equals `0`** (U7 stub).

Honest caveat: this holds because the U7 `projMatrix` stub is
identically `1`, so the projected identity minor has determinant
`1`, and hence `-β · log 1 = 0`. A future non-stub `projMatrix`
replacement will make this value divergent at the trivial gauge. -/
theorem barrier_trivial_finite {N : ℕ} {β : ℝ} :
    concreteLogDetBarrier (N := N) β
        (PallLean.Paper93.NFrame.trivialGauge N) = 0 :=
  concreteLogDetBarrier_identity_zero

/-! ## 3. Kernel-only sanity checks

Sanity examples exercising the public API at elaboration time. -/

example {N : ℕ} {β : ℝ}
    (gauge1 gauge2 : PallLean.Paper93.NFrame.CandidateGauge N)
    (h : Module.finrank ℚ (LinearMap.range gauge1.projection) ≤
         Module.finrank ℚ (LinearMap.range gauge2.projection)) :
    concreteLogDetBarrier β gauge2 ≤ concreteLogDetBarrier β gauge1 :=
  logDetBarrier_monotone_in_rank gauge1 gauge2 h

example {N : ℕ} {β : ℝ} :
    concreteLogDetBarrier (N := N) β
        (PallLean.Paper93.NFrame.trivialGauge N) = 0 :=
  barrier_trivial_finite

end PallLean.Paper93.Concrete
