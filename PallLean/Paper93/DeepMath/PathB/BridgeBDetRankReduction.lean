import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Diagonal

/-!
# Bridge B (§28.3) — det/rank inequality, conditional/reduction form.

Paper §28.3 contains the inequality, valid for positive-definite `A` and `θ > 0`,

```
log det (I + θ A) ≤ rk(A) · log (1 + θ ‖A‖).
```

This file lands the **reduction theorem** (kernel-only):
*given* an upper bound `λᵢ ≤ ‖A‖` on each eigenvalue and the eigenvalue product
expansion `det (I + θA) = ∏ (1 + θ λᵢ)`, the paper inequality reduces to a
purely arithmetic inequality on logs and sums, which we prove here.

## Why a reduction theorem (not a from-scratch spectral proof)?

Mathlib's spectral theory does provide
`Matrix.IsHermitian.det_eq_prod_eigenvalues`, but plumbing it through to a
clean statement at this point in the development requires nontrivial
instance-setup (choice of inner-product space, casting eigenvalues to `ℝ`,
operator-norm interface) which is out of scope for this file. We instead
formalise the **arithmetic core** of the inequality so that the eigenvalue
product expansion can be substituted in by any caller that has it available.

## Honest stop point

The arithmetic core (`det_rank_inequality_from_eigenvalues`) is fully closed.
We additionally land the at-diagonal version
(`det_rank_inequality_for_diagonal`) which uses Mathlib's
`Matrix.det_diagonal` to handle the `diagonal D` special case end-to-end.

We do **not** close the fully-spectral version
`Real.log (det (1 + θ • A)) ≤ rk(A) · Real.log (1 + θ * ‖A‖)` for arbitrary
positive-definite `A`; that requires invoking
`Matrix.IsHermitian.det_eq_prod_eigenvalues` and an operator-norm bound on
the eigenvalues, both of which are deferred to a future spectral-bridge file.
-/

namespace PallLean.Paper93.DeepMath.PathB.BridgeBDetRankReduction

open Finset

/-!
## Step 1 — Pointwise log-of-shifted-eigenvalue bound.

For `θ > 0`, `0 ≤ λ`, and `λ ≤ M`, we have
`log (1 + θ * λ) ≤ log (1 + θ * M)`.

This is the only place where `Real.log_le_log` is invoked.
-/

private lemma log_one_add_mul_le_of_le {θ : ℝ} (hθ : 0 < θ)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    Real.log (1 + θ * x) ≤ Real.log (1 + θ * y) := by
  have hθx : 0 ≤ θ * x := mul_nonneg hθ.le hx
  have h1pos : 0 < 1 + θ * x := by linarith
  have hxy' : θ * x ≤ θ * y := by
    have hθle : 0 ≤ θ := hθ.le
    exact mul_le_mul_of_nonneg_left hxy hθle
  have h1le : 1 + θ * x ≤ 1 + θ * y := by linarith
  exact Real.log_le_log h1pos h1le

/-!
## Step 2 — Sum of zero-eigenvalue terms vanishes.

For `θ > 0` and `λ = 0`, `log (1 + θ * 0) = log 1 = 0`. Hence the partial sum
over `{i : λ i = 0}` is zero (using `0 ≤ λ` and `¬ (0 < λ)` ⇒ `λ = 0`).
-/

private lemma sum_log_zero_part_eq_zero {n : ℕ} (θ : ℝ)
    (eigenvalues : Fin n → ℝ) (h_nonneg : ∀ i, 0 ≤ eigenvalues i) :
    ∑ i ∈ Finset.univ.filter (fun i => ¬ 0 < eigenvalues i),
      Real.log (1 + θ * eigenvalues i) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_filter] at hi
  obtain ⟨_, hi_not⟩ := hi
  have h_zero : eigenvalues i = 0 :=
    le_antisymm (not_lt.mp hi_not) (h_nonneg i)
  rw [h_zero]
  simp [Real.log_one]

/-!
## Step 3 — Main reduction theorem (kernel-only).

Given:
* `θ > 0`,
* eigenvalues `λᵢ ≥ 0` with `λᵢ ≤ ‖A‖`,
* `rk = #{i : λᵢ > 0}`,

we prove the arithmetic inequality

`∑ i, log (1 + θ λᵢ) ≤ rk · log (1 + θ ‖A‖).`

This is the kernel-only target requested by the spec; no spectral theorem
is invoked.
-/

theorem det_rank_inequality_from_eigenvalues
    (n : ℕ) (θ : ℝ) (hθ : 0 < θ)
    (eigenvalues : Fin n → ℝ)
    (h_nonneg : ∀ i, 0 ≤ eigenvalues i)
    (operator_norm : ℝ)
    (h_bound : ∀ i, eigenvalues i ≤ operator_norm)
    (rk : ℕ)
    (h_rk_count :
      rk = (Finset.filter (fun i => 0 < eigenvalues i) Finset.univ).card) :
    ∑ i, Real.log (1 + θ * eigenvalues i)
      ≤ (rk : ℝ) * Real.log (1 + θ * operator_norm) := by
  classical
  -- Split the sum into "eigenvalue > 0" and "eigenvalue ≤ 0" parts.
  -- The latter is zero (each summand is `log 1 = 0`), so we focus on the former.
  set p : Fin n → Prop := fun i => 0 < eigenvalues i with hp_def
  -- Step A: rewrite full sum as filtered sum over `p`.
  have h_split :
      ∑ i, Real.log (1 + θ * eigenvalues i) =
        ∑ i ∈ Finset.univ.filter p, Real.log (1 + θ * eigenvalues i) := by
    -- p i = (0 < eigenvalues i) so ¬ p = ¬ (0 < eigenvalues i)
    have h_zero :
        ∑ i ∈ Finset.univ.filter (fun i => ¬ p i),
          Real.log (1 + θ * eigenvalues i) = 0 :=
      sum_log_zero_part_eq_zero (n := n) θ eigenvalues h_nonneg
    have h_total :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ p
        (fun i => Real.log (1 + θ * eigenvalues i)))
    -- h_total : (∑ filter p) + (∑ filter ¬p) = ∑ univ
    -- h_zero  : ∑ filter ¬p = 0
    -- So ∑ univ = ∑ filter p
    linarith
  -- Step B: bound each term in the filtered sum by `log (1 + θ * operator_norm)`.
  set S : Finset (Fin n) := Finset.univ.filter p with hS_def
  have h_pointwise :
      ∀ i ∈ S, Real.log (1 + θ * eigenvalues i)
        ≤ Real.log (1 + θ * operator_norm) := by
    intro i _hi
    exact log_one_add_mul_le_of_le hθ (h_nonneg i) (h_bound i)
  -- Step C: ∑_{i ∈ S} f(i) ≤ ∑_{i ∈ S} log(1 + θ * operator_norm)
  have h_sum_le_sum :
      ∑ i ∈ S, Real.log (1 + θ * eigenvalues i)
        ≤ ∑ _ ∈ S, Real.log (1 + θ * operator_norm) :=
    Finset.sum_le_sum h_pointwise
  -- Step D: ∑_{i ∈ S} c = #S • c = #S * c.
  have h_const :
      (∑ _ ∈ S, Real.log (1 + θ * operator_norm))
        = (S.card : ℝ) * Real.log (1 + θ * operator_norm) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  -- Step E: combine.
  calc
    ∑ i, Real.log (1 + θ * eigenvalues i)
        = ∑ i ∈ S, Real.log (1 + θ * eigenvalues i) := h_split
    _ ≤ ∑ _ ∈ S, Real.log (1 + θ * operator_norm) := h_sum_le_sum
    _ = (S.card : ℝ) * Real.log (1 + θ * operator_norm) := h_const
    _ = (rk : ℝ) * Real.log (1 + θ * operator_norm) := by
        rw [show S.card = rk from h_rk_count.symm]

/-!
## Step 4 — Optional: at-the-diagonal-matrix version.

For a diagonal matrix `Matrix.diagonal D` with `0 ≤ D i`, the inequality
`log (det (1 + θ • Matrix.diagonal D)) ≤ rk · log (1 + θ * sup D)` follows
end-to-end: we use `Matrix.det_diagonal` to expand the determinant as a
product, `Real.log_prod` to convert to a sum, and then apply
`det_rank_inequality_from_eigenvalues` with the explicit eigenvalues
`fun i => D i`, operator-norm bound `Finset.univ.sup' _ D`, and rank count
`#{i : 0 < D i}`.

Requires `Fin n` to be nonempty (i.e. `n = m + 1`) so that `Finset.univ`
admits a `sup'` witness. -/

theorem det_rank_inequality_for_diagonal
    {m : ℕ} (θ : ℝ) (hθ : 0 < θ) (D : Fin (m + 1) → ℝ)
    (h_nonneg : ∀ i, 0 ≤ D i) :
    Real.log
        (Matrix.det
          ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) +
            θ • Matrix.diagonal D))
      ≤ ((Finset.filter (fun i => 0 < D i) Finset.univ).card : ℝ) *
          Real.log (1 + θ * Finset.univ.sup'
            ⟨(0 : Fin (m + 1)), Finset.mem_univ _⟩ D) := by
  classical
  -- Step A: rewrite `(1 : Matrix _ _ ℝ) + θ • diagonal D` as
  --         `diagonal (fun i => 1 + θ * D i)`.
  have h_eq :
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
        + θ • Matrix.diagonal D
        = Matrix.diagonal (fun i => 1 + θ * D i) := by
    -- 1 = diagonal (fun _ => 1); θ • diagonal D = diagonal (θ • D)
    -- diagonal d₁ + diagonal d₂ = diagonal (d₁ + d₂)
    rw [show (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
            = Matrix.diagonal (fun _ => (1 : ℝ)) from
      (Matrix.diagonal_one).symm]
    rw [show θ • Matrix.diagonal D
            = Matrix.diagonal (fun i => θ * D i) from by
      rw [← Matrix.diagonal_smul]
      rfl]
    rw [Matrix.diagonal_add]
  -- Step B: det of a diagonal matrix is the product of its diagonal entries.
  have h_det :
      Matrix.det
          ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) +
            θ • Matrix.diagonal D)
        = ∏ i, (1 + θ * D i) := by
    rw [h_eq, Matrix.det_diagonal]
  -- Step C: each factor `1 + θ * D i` is positive (since θ > 0 and D i ≥ 0),
  -- so we can apply `Real.log_prod`.
  have h_pos : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))),
      (1 + θ * D i) ≠ 0 := by
    intro i _
    have hθD : 0 ≤ θ * D i := mul_nonneg hθ.le (h_nonneg i)
    have : 0 < 1 + θ * D i := by linarith
    exact ne_of_gt this
  -- Step D: log of product = sum of logs.
  have h_log_prod :
      Real.log (∏ i, (1 + θ * D i))
        = ∑ i, Real.log (1 + θ * D i) :=
    Real.log_prod (s := (Finset.univ : Finset (Fin (m + 1))))
      (f := fun i => 1 + θ * D i) h_pos
  -- Step E: apply the kernel-only inequality with operator_norm = sup' D.
  set M : ℝ := Finset.univ.sup' ⟨(0 : Fin (m + 1)), Finset.mem_univ _⟩ D
  have h_bound : ∀ i, D i ≤ M := by
    intro i
    exact Finset.le_sup' D (Finset.mem_univ i)
  have h_sum_le :=
    det_rank_inequality_from_eigenvalues
      (n := m + 1) θ hθ D h_nonneg M h_bound
      ((Finset.filter (fun i => 0 < D i) Finset.univ).card) rfl
  calc
    Real.log
        (Matrix.det
          ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) +
            θ • Matrix.diagonal D))
        = Real.log (∏ i, (1 + θ * D i)) := by rw [h_det]
    _ = ∑ i, Real.log (1 + θ * D i) := h_log_prod
    _ ≤ ((Finset.filter (fun i => 0 < D i) Finset.univ).card : ℝ) *
          Real.log (1 + θ * M) := h_sum_le

end PallLean.Paper93.DeepMath.PathB.BridgeBDetRankReduction
