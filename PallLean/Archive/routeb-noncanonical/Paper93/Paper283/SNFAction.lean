/-
  PallLean/Paper93/Paper283/SNFAction.lean

  Paper §28.3 — Full N-Frame action functional.

  ## Scope

  The paper §28.3 full N-Frame (NF) action reads

      S_NF[Φ ; P]
        =   α · Σ_{(u,v) ∈ E(G)} (Φ_u − Φ_v)²             -- edge energy
          + β · Σ_{v ∈ V}    (1 − χ(v) · sgn Φ_v)_+       -- parity term
          + λ · B(A)                                       -- amplituhedron barrier

  where:

    * `G`        is a (d-regular) expander graph on `Fin N`
                 (see `PallLean.Paper93.Concrete.RegularGraphFixed`);
    * `χ`        is a Tseitin charge `Fin N → {±1}`
                 (see `PallLean.Paper93.Paper283.TseitinCharge`);
    * `Φ`        is the NF phase field `Fin N → ℝ`;
    * `A`        is the amplituhedron matrix (positivity is encoded
                 by principal-minor barriers);
    * `parityTerm β χ Φ`      — full β-weighted parity term
                 (see `PallLean.Paper93.Paper283.ParityTerm`);
    * `amplituhedronBarrier A` — principal-minor log-det barrier
                 (see `PallLean.Paper93.Paper283.AmplituhedronBarrier`).

  This file defines:

    * `SNFAction α β λ G χ Φ A`   — the full three-term action;

  and proves the paper-faithful collapse lemma required by the X8
  obligation:

    * `SNFAction_nonneg_at_identity` — collapsing S_NF at A = 1 with
                                        an aligned phase field reduces
                                        it to α · (edge energy).

  ## Imports (X1/X4/X6/X7 + Concrete)

    * `PallLean.Paper93.Paper283.TseitinCharge`       (X1 Tseitin charge);
    * `PallLean.Paper93.Paper283.ParityTerm`          (X4 full parity term);
    * `PallLean.Paper93.Paper283.ParityViolation`     (per-vertex parity);
    * `PallLean.Paper93.Paper283.AmplituhedronBarrier` (X7 B(A) barrier);
    * `PallLean.Paper93.Concrete.RegularGraphFixed`    (edge set container).

  ## Paper citations

    * §28.3 line 6870 — Tseitin charge χ : V_n → {±1};
    * §28.3 line 6876 — amplituhedron principal-minor family J;
    * §28.3 — three-term action  α·edges + β·parity + λ·barrier.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import PallLean.Paper93.Paper283.TseitinCharge
import PallLean.Paper93.Paper283.ParityViolation
import PallLean.Paper93.Paper283.ParityTerm
import PallLean.Paper93.Paper283.AmplituhedronBarrier
import PallLean.Paper93.Concrete.RegularGraphFixed

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open Matrix

/-- Paper §28.3 — full N-Frame action

        S_NF[Φ ; P]
          = α · Σ_{(u,v) ∈ E(G)} (Φ_u − Φ_v)²
          + β · Σ_v (1 − χ(v) · sgn Φ_v)_+
          + λ · B(A).

    We use `lam` in place of the paper's `λ` (which is a reserved
    keyword in Lean 4). -/
noncomputable def SNFAction {N d : ℕ}
    (α β lam : ℝ)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (χ : TseitinCharge N)
    (Φ : Fin N → ℝ)
    (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  α * (∑ e ∈ G.edges, (Φ e.1 - Φ e.2)^2) +
  parityTerm β χ Φ +
  lam * amplituhedronBarrier A

/-- Paper §28.3 — collapse at `A = 1` with an aligned phase field:
    the full N-Frame action reduces to the pure edge-energy term.

    * The parity term vanishes by `parityTerm_aligned_zero` whenever
      every per-vertex parity violation is zero.
    * The amplituhedron barrier vanishes at `A = 1` by
      `amplituhedronBarrier_identity`. -/
theorem SNFAction_nonneg_at_identity {N d : ℕ} {α β lam : ℝ}
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (χ : TseitinCharge N) (Φ : Fin N → ℝ)
    (_hα : 0 ≤ α) (_hβ : 0 ≤ β) (_hlam : 0 ≤ lam)
    (hAligned : ∀ v, parityViolation χ Φ v = 0) :
    SNFAction α β lam G χ Φ (1 : Matrix (Fin N) (Fin N) ℝ) =
      α * ∑ e ∈ G.edges, (Φ e.1 - Φ e.2)^2 := by
  unfold SNFAction
  rw [parityTerm_aligned_zero hAligned, amplituhedronBarrier_identity,
      mul_zero]
  ring

end PallLean.Paper93.Paper283
