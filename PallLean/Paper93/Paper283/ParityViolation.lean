/-
  PallLean/Paper93/Paper283/ParityViolation.lean

  Paper §28.3 — Per-vertex parity violation `(1 - χ(v) · sgn Φ_v)_+`.

  ## Scope

  This file records the Paper §28.3 per-vertex parity violation term
  `(1 − χ(v) · sgn Φ_v)_+` appearing in the full Lagrangian functional
  (see `PallLean/Paper93/NFrame/FullLagrangian.lean`,
  `PallLean/Paper93/NFrame/EdgeEnergy.lean`,
  `PallLean/Paper93/NFrame/LagrangianFunctional.lean`). We provide:

    * `parityViolation χ Φ v` — the per-vertex parity violation;
    * `parityViolation_nonneg` — the violation is always nonnegative;
    * `parityViolation_zero_when_aligned` — the violation vanishes when
      the sign of `Φ v` matches the charge `χ v`, i.e. when
      `(χ v).val · sgn (Φ v) ≥ 1`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  ## Paper citations

    * §28.3 — per-vertex parity violation
      `(1 − χ(v) · sgn Φ_v)_+` in the full Lagrangian.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import PallLean.Paper93.Paper283.SgnFunction
import PallLean.Paper93.Paper283.TseitinCharge

namespace PallLean.Paper93.Paper283

/-- Per-vertex parity violation: large when `Φ v` doesn't match `χ v`'s sign.
    Paper §28.3: `(1 - χ(v) · sgn Φ_v)_+`. -/
noncomputable def parityViolation {N : ℕ}
    (χ : TseitinCharge N) (Φ : Fin N → ℝ) (v : Fin N) : ℝ :=
  posPart (1 - ((χ v).val : ℝ) * sgn (Φ v))

/-- The per-vertex parity violation is always nonnegative. -/
theorem parityViolation_nonneg {N : ℕ}
    (χ : TseitinCharge N) (Φ : Fin N → ℝ) (v : Fin N) :
    0 ≤ parityViolation χ Φ v :=
  posPart_nonneg _

/-- The parity violation vanishes when `Φ v` has the same sign as `χ v`
    with `(χ v).val · sgn (Φ v) ≥ 1` (i.e. the signs are aligned and
    nonzero). -/
theorem parityViolation_zero_when_aligned {N : ℕ}
    (χ : TseitinCharge N) (Φ : Fin N → ℝ) (v : Fin N)
    (h : ((χ v).val : ℝ) * sgn (Φ v) ≥ 1) :
    parityViolation χ Φ v = 0 := by
  unfold parityViolation posPart
  have hle : 1 - ((χ v).val : ℝ) * sgn (Φ v) ≤ 0 := by linarith
  exact max_eq_right hle

end PallLean.Paper93.Paper283
