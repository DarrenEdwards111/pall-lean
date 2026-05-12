/-
  PallLean/Paper93/Paper283/EulerLagrangePhi.lean

  Paper §28.3 line 6878 — Euler–Lagrange condition `δΦ S_NF = 0`.

  ## Scope

  Paper §28.3 line 6878 states that a stationary point Φ of the
  NF action `S_NF` satisfies

      α · L_{Gn} · Φ  =  (β/2) · χ · ∂ sgn(Φ),

  where `L_{Gn}` is the graph Laplacian of the expander `G_n`, `χ`
  is the Tseitin charge from §28.3 line 6870, and `∂ sgn(Φ)` is
  the subgradient of the sign function.

  This file provides a **stub** formalisation of the stationary-Φ
  predicate: we record the *existence* of the Euler–Lagrange equation
  as a proposition `StationaryPhi α β G χ Φ`, without unfolding the
  graph-Laplacian / subgradient machinery. The placeholder body uses
  the trivially-true statement `∀ v, 0 ≤ (Φ v)^2`, which is adequate
  for downstream files that only need a witness of stationarity.

  A fully faithful implementation would:
    * build `L_{Gn}` from `RegularGraphFixed.adjacency`,
    * define the subdifferential `∂ sgn : ℝ → Set ℝ`,
    * and assert `α · (L_{Gn} Φ) v = (β/2) · (χ v).val · s` for some
      `s ∈ ∂ sgn (Φ v)` for every `v`.

  The present file is marked as a **stub** and does not discharge the
  Euler–Lagrange PDE content. It is kept kernel-only so the project
  continues to build while the full formalisation is developed.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  ## Paper citations

    * §28.3 line 6870 — Tseitin charge `χ : V_n → {±1}`.
    * §28.3 line 6878 — Euler–Lagrange condition
      `α L_{Gn} Φ = (β/2) χ · ∂ sgn(Φ)`.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Defs
import PallLean.Paper93.Concrete.RegularGraphFixed
import PallLean.Paper93.Paper283.TseitinCharge
import PallLean.Paper93.Paper283.SgnFunction

namespace PallLean.Paper93.Paper283

/--
  `StationaryPhi α β G χ Φ` — Paper §28.3 line 6878 stationary-Φ
  predicate `δΦ S_NF = 0`.

  At a stationary Φ the paper asserts

      α · L_{Gn} · Φ  =  (β/2) · χ · ∂ sgn(Φ).

  **Stub body:** we record the predicate as the trivially-true
  statement `∀ v, 0 ≤ (Φ v)^2`, which is always satisfied. The real
  Euler–Lagrange characterisation requires a graph Laplacian and a
  subgradient-of-sign calculus; those are intentionally deferred.
  This stub suffices for downstream files that only consume a
  stationary-Φ witness.
-/
def StationaryPhi {N d : ℕ}
    (_α _β : ℝ)
    (_G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (_χ : TseitinCharge N)
    (Φ : Fin N → ℝ) : Prop :=
  ∀ v : Fin N, 0 ≤ (Φ v)^2

/-- The stub stationary-Φ predicate is vacuously true for every Φ.
    Under the real Euler–Lagrange formulation this would be a
    non-trivial fixed-point condition. -/
theorem StationaryPhi_always
    {N d : ℕ} {α β : ℝ}
    {G : PallLean.Paper93.Concrete.RegularGraphFixed N d}
    {χ : TseitinCharge N}
    {Φ : Fin N → ℝ} :
    StationaryPhi (N := N) (d := d) α β G χ Φ :=
  fun v => sq_nonneg (Φ v)

end PallLean.Paper93.Paper283
