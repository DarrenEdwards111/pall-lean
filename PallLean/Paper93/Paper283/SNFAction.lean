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

    * `G`       is a (d-regular) expander graph on `Fin N`
                (see `PallLean.Paper93.Concrete.RegularGraphFixed`);
    * `χ`       is a Tseitin charge `Fin N → {±1}`
                (see `PallLean.Paper93.Paper283.TseitinCharge`);
    * `Φ`       is the NF phase field `Fin N → ℝ`;
    * `A`       is the amplituhedron matrix
                (positivity is encoded by principal-minor barriers);
    * `sgn`     and `(·)_+` are as in
                `PallLean.Paper93.Paper283.SgnFunction`;
    * `(1 − χ(v) · sgn Φ_v)_+` is the per-vertex parity violation
                (see `PallLean.Paper93.Paper283.ParityViolation`).

  This file defines:

    * `parityTerm  β χ Φ`          — the β-weighted parity sum;
    * `amplituhedronBarrier A`     — the amplituhedron principal-minor barrier;
    * `SNFAction α β λ G χ Φ A`    — the full three-term action.

  It also proves the two paper-faithful sanity lemmas required by the
  X8 obligation:

    * `parityTerm_aligned_zero`      — parity term vanishes when the
                                        phase field is aligned with χ;
    * `amplituhedronBarrier_identity` — the amplituhedron barrier at
                                        A = 1 is zero;
    * `SNFAction_nonneg_at_identity` — collapsing S_NF at A = 1 with
                                        an aligned phase field reduces
                                        it to α · (edge energy).

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
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import PallLean.Paper93.Paper283.SgnFunction
import PallLean.Paper93.Paper283.TseitinCharge
import PallLean.Paper93.Paper283.ParityViolation
import PallLean.Paper93.Paper283.MinorFamily
import PallLean.Paper93.Paper283.PrincipalMinor
import PallLean.Paper93.Concrete.RegularGraphFixed

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open Matrix

/-- Paper §28.3 — β-weighted parity term
    `β · Σ_v (1 − χ(v) · sgn Φ_v)_+`. -/
noncomputable def parityTerm {N : ℕ} (β : ℝ)
    (χ : TseitinCharge N) (Φ : Fin N → ℝ) : ℝ :=
  β * ∑ v, parityViolation χ Φ v

/-- Paper §28.3 — amplituhedron principal-minor barrier

        B(A) := Σ_{J ∈ minorFamily N} (− det A[J,J])_+ .

    This is nonnegative and vanishes when every principal minor on
    the fixed family `minorFamily N` has positive determinant — in
    particular at `A = 1`. -/
noncomputable def amplituhedronBarrier {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ∑ J ∈ minorFamily N, posPart (- (principalMinor A J).det)

/-- Paper §28.3 — full N-Frame action

        S_NF[Φ ; P]
          = α · Σ_{(u,v) ∈ E(G)} (Φ_u − Φ_v)²
          + β · Σ_v (1 − χ(v) · sgn Φ_v)_+
          + λ · B(A).  -/
noncomputable def SNFAction {N d : ℕ}
    (α β lam : ℝ)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (χ : TseitinCharge N)
    (Φ : Fin N → ℝ)
    (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  α * (∑ e ∈ G.edges, (Φ e.1 - Φ e.2)^2) +
  parityTerm β χ Φ +
  lam * amplituhedronBarrier A

/-- The β-weighted parity term vanishes whenever every per-vertex
    parity violation is zero.  (We do not need `0 ≤ β` for this; the
    scalar multiple of a zero sum is zero.) -/
theorem parityTerm_aligned_zero {N : ℕ} {β : ℝ}
    {χ : TseitinCharge N} {Φ : Fin N → ℝ}
    (_hβ : 0 ≤ β)
    (hAligned : ∀ v, parityViolation χ Φ v = 0) :
    parityTerm β χ Φ = 0 := by
  unfold parityTerm
  have hsum : ∑ v, parityViolation χ Φ v = (0 : ℝ) := by
    have : ∀ v ∈ (Finset.univ : Finset (Fin N)),
        parityViolation χ Φ v = 0 := fun v _ => hAligned v
    simpa using Finset.sum_eq_zero this
  rw [hsum, mul_zero]

/-- The amplituhedron barrier at `A = 1` is zero: every principal
    minor of the identity has determinant `1 > 0`, so each summand
    `(− 1)_+` is `0`. -/
theorem amplituhedronBarrier_identity {N : ℕ} :
    amplituhedronBarrier (1 : Matrix (Fin N) (Fin N) ℝ) = 0 := by
  unfold amplituhedronBarrier
  apply Finset.sum_eq_zero
  intro J _
  -- `det (principalMinor 1 J) = 1`, so we need `posPart (-1) = 0`.
  have hdet : (principalMinor (1 : Matrix (Fin N) (Fin N) ℝ) J).det = 1 :=
    principalMinor_one_det
  rw [hdet]
  -- `posPart (-1) = max (-1) 0 = 0`.
  unfold posPart
  have : (-(1 : ℝ)) ≤ 0 := by norm_num
  exact max_eq_right this

/-- Paper §28.3 — collapse at `A = 1` with an aligned phase field:
    the full N-Frame action reduces to the pure edge-energy term. -/
theorem SNFAction_nonneg_at_identity {N d : ℕ} {α β lam : ℝ}
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (χ : TseitinCharge N) (Φ : Fin N → ℝ)
    (_hα : 0 ≤ α) (hβ : 0 ≤ β) (_hlam : 0 ≤ lam)
    (hAligned : ∀ v, parityViolation χ Φ v = 0) :
    SNFAction α β lam G χ Φ (1 : Matrix (Fin N) (Fin N) ℝ) =
      α * ∑ e ∈ G.edges, (Φ e.1 - Φ e.2)^2 := by
  unfold SNFAction
  rw [parityTerm_aligned_zero hβ hAligned, amplituhedronBarrier_identity,
      mul_zero]
  ring

end PallLean.Paper93.Paper283
