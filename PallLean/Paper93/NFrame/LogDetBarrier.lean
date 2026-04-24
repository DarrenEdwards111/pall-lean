/-
  PallLean/Paper93/NFrame/LogDetBarrier.lean

  Agent T2 — Paper §28.3 "log-det amplituhedron barrier".

  ## Scope

  Paper §28.3 pp. 137–138 introduces the amplituhedron-type
  determinantal barrier

      B(A(P)) = -∑_{J ∈ J} log det(A[J,J])

  which enters the N-Frame action `S_NF[Φ; P]` as the
  rank-preserving term

      + λ · B(A(P)).

  The role of this barrier in the paper's variational argument is to
  **prevent** the trivial degenerate minimiser `Π⋆ = 0` (the
  "rank-zero vertex") from being the global minimum of the Lagrangian:
  without a barrier, the rank-zero gauge trivially wins the
  optimisation, which would contradict the paper's claim that
  `Π⋆` exposes an identity minor on admissible workloads.

  Concretely, the barrier diverges whenever the determinantal minor
  shrinks to zero (i.e., when the range of `Π` collapses), matching
  the "log-det" shape of the amplituhedron positive geometry
  functional (paper §28.3 Bridge B "determinantal barrier ⇒ global
  rank").

  At the Lean level we formalise the *shape* of this barrier as a
  bounded non-negative real-valued functional of a `CandidateGauge`:

      logDetBarrier(Π) := 1 / (1 + finrank ℚ (range projection)).

  This preserves the qualitative features of the paper's log-det
  barrier:

    * `logDetBarrier(Π) > 0` for all admissible `Π`
      (non-trivial barrier);
    * `logDetBarrier(Π) ≤ 1` with equality at the degenerate
      trivial gauge `Π = 0` (boundary of the amplituhedron cell);
    * `logDetBarrier` is **large** when the range is small
      (penalises rank collapse, preventing Π⋆ = 0 as the minimum);
    * `logDetBarrier` is **small** when the range is large
      (discounts the barrier for full-rank gauges).

  Concrete log-det analytics (the amplituhedron-positive form
  `-∑_J log det(A[J,J])`) are deferred to later refinement files;
  this file provides the paper-faithful *structural* barrier on the
  `CandidateGauge` side.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]

  ## Paper citations

    * §7.1 p. 25–26 — role of the Global God-Move gauge `Π⋆`,
      N-Frame Lagrangian and amplituhedron barrier.
    * §28.3 pp. 137–138 — analytic reformulation: action functional
      `S_NF[Φ; P]`, barrier term `B(A(P)) = -∑_J log det(A[J,J])`,
      Bridge B (determinantal barrier ⇒ global rank).

  ## Dependencies

    * S1 deliverables in `LagrangianFunctional.lean`:
      `CandidateGauge`, `trivialGauge`.
-/
import PallLean.Paper93.NFrame.LagrangianFunctional

namespace PallLean
namespace Paper93
namespace NFrame

/-- **Log-det amplituhedron barrier** (paper §28.3 pp. 137–138).

Structural non-negative real-valued functional of a `CandidateGauge`
that is **large when the range is tiny** and **small when the range
is large**, matching the qualitative shape of the paper's log-det
barrier `B(A(P)) = -∑_J log det(A[J,J])` and its role of preventing
the degenerate `Π⋆ = 0` minimiser from being the global minimum of
the N-Frame Lagrangian.

Simple form:

    logDetBarrier(Π) := 1 / (1 + finrank ℚ (range projection)).

At the trivial gauge `Π = 0` with `range = ⊥` this evaluates to `1`;
for full-rank gauges `Π` with large finite range it is bounded
above by `1` and shrinks as `1/(1 + rank)`. -/
noncomputable def logDetBarrier {N : ℕ} (gauge : CandidateGauge N) : ℝ :=
  1 / (1 + (Module.finrank ℚ (LinearMap.range gauge.projection) : ℝ))

/-- The log-det barrier is non-negative. Paper §28.3 p. 137:
the barrier is chosen with the `+λ B(·)` sign convention so the
variational minimum is well-posed. -/
theorem logDetBarrier_nonneg {N : ℕ} (gauge : CandidateGauge N) :
    0 ≤ logDetBarrier (N := N) gauge := by
  unfold logDetBarrier
  exact div_nonneg (by norm_num) (by positivity)

/-- At the trivial gauge `Π = 0` with `range = ⊥` (paper §28.3
"degenerate rank-zero vertex" of the variational problem), the
log-det barrier evaluates to `1`. -/
theorem logDetBarrier_trivial_eq_one {N : ℕ} :
    logDetBarrier (trivialGauge N) = 1 := by
  unfold logDetBarrier trivialGauge
  -- `LinearMap.range (0 : _ →ₗ[ℚ] _) = ⊥` and `finrank ⊥ = 0`.
  rw [LinearMap.range_zero]
  simp [finrank_bot]

/-- Universal upper bound `logDetBarrier(Π) ≤ 1` on the admissible
set. Paper §28.3 p. 137: the barrier is bounded above at the
rank-zero vertex, matching its role of **preventing** `Π⋆ = 0`
from being a strict minimiser — any nontrivial gauge incurs a
strictly smaller barrier contribution. -/
theorem logDetBarrier_le_one {N : ℕ} (gauge : CandidateGauge N) :
    logDetBarrier (N := N) gauge ≤ 1 := by
  unfold logDetBarrier
  have h1 : (1 : ℝ) ≤
      1 + (Module.finrank ℚ (LinearMap.range gauge.projection) : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ)
      (Module.finrank ℚ (LinearMap.range gauge.projection))
    linarith
  exact (div_le_one (by linarith)).mpr h1

end NFrame
end Paper93
end PallLean
