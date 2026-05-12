/-
  PallLean/Paper93/Paper283/EulerLagrangeA.lean

  Paper §28.3 line 6880 — Euler–Lagrange stationarity in the matrix
  variable `A` for the normal-form action `S_NF`:

      δ_A S_NF = 0  ⟺  −λ · Σ_{J ∈ J} (A[J,J])^{-1}  ∈  ∂(compiler constraints).

  ## Scope (stub form, paper-faithful)

  The full form of the Euler–Lagrange condition requires the subgradient
  `∂` of the (nonsmooth) compiler-constraint indicator — this is
  explicitly out of scope here. We therefore record a `Prop`-level
  *stub* that captures the principal-minor positivity side condition
  (paper §28.3 line 6876: "amplituhedron-type positivity"): the
  constraint set on which the stationarity identity is formulated
  requires every principal minor `A[J,J]` indexed by `J ∈ minorFamily N`
  to be strictly positive.

  As a sanity check we verify that, at `λ = 0` and `A = I`, the
  stationarity stub holds — because every principal minor of the
  identity has determinant `1 > 0`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  ## Paper citations

    * §28.3 line 6876 — principal-minor family `J` (amplituhedron-type
      positivity).
    * §28.3 line 6880 — stationarity condition
      `−λ Σ_{J∈J}(A[J,J])^{-1} ∈ ∂(compiler constraints)`.
-/

import PallLean.Paper93.Paper283.MinorFamily
import PallLean.Paper93.Paper283.PrincipalMinor

namespace PallLean.Paper93.Paper283

open Matrix

/-- δ_A S_NF = 0 — stationarity in the matrix variable `A`.

    Paper §28.3 line 6880.

    **Stub form.** The full stationarity identity reads

      −λ · Σ_{J ∈ J} (A[J,J])^{-1} ∈ ∂(compiler constraints).

    The right-hand subgradient of the compiler-constraint indicator is
    out of scope for this file; we therefore expose only the
    principal-minor *positivity* side-condition (paper §28.3 line 6876,
    "amplituhedron-type positivity") that defines the feasible region
    on which the stationarity identity is to be evaluated. -/
def StationaryA {N : ℕ}
    (_lam : ℝ) (A : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ J ∈ minorFamily N, 0 < (principalMinor A J).det

/-- At `λ = 0` and `A = I`, the `StationaryA` stub holds: every
    principal minor of the identity has determinant `1 > 0`. -/
theorem StationaryA_at_identity (N : ℕ) :
    StationaryA (_lam := (0 : ℝ)) (1 : Matrix (Fin N) (Fin N) ℝ) := by
  intro J _hJ
  rw [principalMinor_one_det]
  exact zero_lt_one

end PallLean.Paper93.Paper283
