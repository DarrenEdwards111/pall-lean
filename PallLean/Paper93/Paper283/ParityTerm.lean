/-
  PallLean/Paper93/Paper283/ParityTerm.lean

  Paper §28.3 — Full parity term `β Σ_{v ∈ V_n} (1 − χ(v) · sgn Φ_v)_+`.

  ## Scope

  This file records the Paper §28.3 *full parity term* appearing in the
  full Lagrangian functional: the sum over all vertices of the per-vertex
  parity violation (see `PallLean/Paper93/Paper283/ParityViolation.lean`),
  scaled by a nonnegative coupling constant `β`. We provide:

    * `parityTerm β χ Φ` — the full Paper §28.3 parity term
      `β Σ_{v ∈ V_n} (1 − χ(v) · sgn Φ_v)_+`;
    * `parityTerm_nonneg`   — `0 ≤ parityTerm β χ Φ` whenever `0 ≤ β`;
    * `parityTerm_aligned_zero` — if every per-vertex violation vanishes
      (charge aligned with `sgn Φ`), the full parity term vanishes.

  ## Imports (X1, X3)

    * `PallLean.Paper93.Paper283.TseitinCharge` (X1) — the Tseitin charge
      type `TseitinCharge N = Fin N → {−1, 1} ⊂ ℤ` from paper §28.3 line
      6870.
    * `PallLean.Paper93.Paper283.ParityViolation` (X3) — the per-vertex
      parity violation `(1 − χ(v) · sgn Φ_v)_+` together with its
      nonnegativity lemma `parityViolation_nonneg`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  ## Paper citations

    * §28.3 — full parity term
      `β Σ_{v ∈ V_n} (1 − χ(v) · sgn Φ_v)_+` in the full Lagrangian.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import PallLean.Paper93.Paper283.TseitinCharge
import PallLean.Paper93.Paper283.ParityViolation

namespace PallLean.Paper93.Paper283

open scoped BigOperators

/-- Full parity term: sum of per-vertex parity violations over all
    vertices `v ∈ V_n = Fin N`, scaled by the coupling constant `β`.
    Paper §28.3: `β Σ_{v ∈ V_n} (1 − χ(v) · sgn Φ_v)_+`. -/
noncomputable def parityTerm {N : ℕ}
    (β : ℝ) (χ : TseitinCharge N) (Φ : Fin N → ℝ) : ℝ :=
  β * ∑ v : Fin N, parityViolation χ Φ v

/-- The full parity term is nonnegative whenever the coupling constant
    `β` is nonnegative. -/
theorem parityTerm_nonneg {N : ℕ} {β : ℝ}
    {χ : TseitinCharge N} {Φ : Fin N → ℝ} (hβ : 0 ≤ β) :
    0 ≤ parityTerm (N := N) β χ Φ := by
  unfold parityTerm
  apply mul_nonneg hβ
  exact Finset.sum_nonneg (fun v _ => parityViolation_nonneg χ Φ v)

/-- The full parity term vanishes whenever every per-vertex parity
    violation vanishes (charge fully aligned with `sgn Φ`). -/
theorem parityTerm_aligned_zero {N : ℕ} {β : ℝ}
    {χ : TseitinCharge N} {Φ : Fin N → ℝ}
    (haligned : ∀ v, parityViolation χ Φ v = 0) :
    parityTerm (N := N) β χ Φ = 0 := by
  unfold parityTerm
  simp [haligned]

end PallLean.Paper93.Paper283
