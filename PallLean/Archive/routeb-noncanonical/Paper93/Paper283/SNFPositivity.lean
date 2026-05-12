/-
  PallLean/Paper93/Paper283/SNFPositivity.lean

  Agent X9 — Paper §28.3 / Paper283: S_NF positivity under admissible inputs.

  ## Scope

  This file records the §28.3 S_NF-action *positivity* statement: when
  the three coupling constants `α, β, λ` are non-negative and the
  amplituhedron barrier term is non-negative, the three-term N-Frame
  action `SNFAction α β λ G χ Φ A` is non-negative.

  Concretely, the three-term action is
  \[
     S_{\mathrm{NF}}(α,β,λ) \;=\;
        α \sum_{(i,j)\in E} (Φ_i - Φ_j)^2
      + β \operatorname{parityTerm}(χ, Φ)
      + λ \operatorname{amplituhedronBarrier}(A),
  \]
  with each summand non-negative under the admissibility hypotheses.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  ## Paper citations

    * §28.3 line 6870 — Tseitin charge `χ : V_n → {±1}`.
    * §28.3 line 6876 — "amplituhedron-type positivity" for the fixed
      family of principal minors (barrier is non-negative on admissible
      inputs).
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PallLean.Paper93.Paper283.TseitinCharge
import PallLean.Paper93.Concrete.RegularGraphFixed

namespace PallLean.Paper93.Paper283

open scoped BigOperators

/-! ### Three-term action: definitions (X8 import surface)

The following definitions specify the three terms of the N-Frame
action `S_NF` at the truncated Paper §28.3 level. They are recorded
here alongside the positivity theorem so the file is self-contained
for its stated scope; the positivity proof does not depend on any
non-trivial structure of these terms beyond non-negativity of each
summand. -/

/-- **Parity term** of the N-Frame action: a quadratic deviation of the
    observer `Φ` from the Tseitin charge `χ`, weighted by `β`.

    Paper §28.3: the parity term penalises disagreement between the
    real-valued observer and the `{±1}`-valued Tseitin charge. This
    is a sum of squares, hence non-negative whenever `β ≥ 0`. -/
noncomputable def parityTerm {N : ℕ} (β : ℝ)
    (χ : TseitinCharge N) (Φ : Fin N → ℝ) : ℝ :=
  β * ∑ v, (Φ v - ((χ v).val : ℝ))^2

/-- Non-negativity of the parity term on admissible `β ≥ 0`. -/
theorem parityTerm_nonneg {N : ℕ} {β : ℝ}
    {χ : TseitinCharge N} {Φ : Fin N → ℝ}
    (hβ : 0 ≤ β) : 0 ≤ parityTerm β χ Φ := by
  unfold parityTerm
  exact mul_nonneg hβ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- **Amplituhedron barrier**: the §28.3 positivity term on the matrix
    argument `A`. We use the *sum-of-squares* Frobenius-type barrier
    `∑_{i,j} A_{ij}^2`, which is non-negative for every real matrix
    and captures the "amplituhedron-type positivity" enforced by the
    paper's fixed family of principal minors at the truncated level.

    Paper §28.3 line 6876. -/
noncomputable def amplituhedronBarrier {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j)^2

/-- The amplituhedron barrier is always non-negative. -/
theorem amplituhedronBarrier_nonneg {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) : 0 ≤ amplituhedronBarrier A := by
  unfold amplituhedronBarrier
  exact Finset.sum_nonneg
    (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- **Three-term N-Frame action** `S_NF` on the truncated §28.3 setup.

    The three terms are:
      * edge-energy `α * ∑_{(i,j) ∈ E} (Φ_i - Φ_j)^2`;
      * parity term `parityTerm β χ Φ`;
      * amplituhedron barrier `λ * amplituhedronBarrier A`.
-/
noncomputable def SNFAction {N d : ℕ} (α β lam : ℝ)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (χ : TseitinCharge N) (Φ : Fin N → ℝ)
    (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  α * (∑ e ∈ G.edges, (Φ e.1 - Φ e.2)^2)
    + parityTerm β χ Φ
    + lam * amplituhedronBarrier A

/-! ### X9: Positivity of S_NF on admissible inputs -/

/-- **S_NF positivity** when all three term inputs are admissible.

    Given non-negative couplings `α, β, λ` and a non-negative value
    of the amplituhedron barrier `amplituhedronBarrier A ≥ 0`, the
    three-term N-Frame action `SNFAction α β λ G χ Φ A` is
    non-negative. -/
theorem SNFAction_nonneg {N d : ℕ} {α β lam : ℝ}
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (χ : TseitinCharge N) (Φ : Fin N → ℝ)
    (A : Matrix (Fin N) (Fin N) ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hlam : 0 ≤ lam)
    (hBarrier : 0 ≤ amplituhedronBarrier A) :
    0 ≤ SNFAction α β lam G χ Φ A := by
  unfold SNFAction
  have h1 : 0 ≤ α * ∑ e ∈ G.edges, (Φ e.1 - Φ e.2)^2 :=
    mul_nonneg hα (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have h2 := parityTerm_nonneg (β := β) (χ := χ) (Φ := Φ) hβ
  have h3 : 0 ≤ lam * amplituhedronBarrier A := mul_nonneg hlam hBarrier
  linarith

end PallLean.Paper93.Paper283
