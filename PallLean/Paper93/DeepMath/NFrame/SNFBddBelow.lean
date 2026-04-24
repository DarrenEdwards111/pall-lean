import PallLean.Paper93.DeepMath.NFrame.SNF
import PallLean.Paper93.DeepMath.NFrame.BarrierPosDef
import PallLean.Paper93.DeepMath.LPS.KnLaplacianSumZeroQuad
import PallLean.Paper93.DeepMath.GadgetRank.IdentityQuad

/-!
# Bounded-below property of the N-Frame Lagrangian on `K_n`

This file establishes that, under favourable hypotheses (couplings
`α, β, λ ≥ 0`; vertex values `Φ` sum-zero on the complete graph
`K_n`; gadget matrix `A` positive-definite with `det A ≤ 1`), the
N-Frame Lagrangian `S_NF` of paper §28.3 is non-negative.

The three-term decomposition

  `S_NF = α·Φᵀ L Φ + β·ParityPenalty + λ·B(A)`

is controlled term-by-term:

* The **α-term** is non-negative because, on `K_n` with sum-zero
  `Φ`, the Laplacian quadratic form equals `n · ‖Φ‖²`
  (`completeAdj_laplacian_sumZero_quadForm`), which is non-negative.
* The **β-term** is non-negative because the parity penalty is a
  sum of `max 0 …` terms (`parityPenalty_nonneg`).
* The **λ-term** `λ · B(A) = −λ · log(det A)` is non-negative
  precisely when `log(det A) ≤ 0`, i.e.\ when `det A ≤ 1`
  (we inline `barrier_nonneg_of_det_le_one` locally since
  `BarrierPosDef.lean` only records the dual `det A ≥ 1` case).

Paper reference: §28.3 pp. 137–138.

## Kernel-only
  * No `sorry`, no `axiom`, no `True`.
  * `#print axioms S_NF_nonneg_on_Kn` returns only kernel primitives.
-/

namespace PallLean.Paper93.DeepMath.NFrame

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.LPS
open PallLean.Paper93.DeepMath.GraphSpectral
open Matrix

/-- **Barrier non-negativity under `det A ≤ 1`.**

For a PosDef matrix `A` with `det A ≤ 1`, we have `log(det A) ≤ 0`
and therefore `barrier A = -log(det A) ≥ 0`.

Inlined here because `BarrierPosDef.lean` only provides the dual
statement `barrier_nonpos_of_det_ge_one`. -/
theorem barrier_nonneg_of_det_le_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (h : A.det ≤ 1) :
    0 ≤ barrier A := by
  unfold barrier
  -- `log` at a positive argument `≤ 1` is non-positive.
  have hpos : 0 < A.det := hA.det_pos
  have hlog : Real.log A.det ≤ 0 := Real.log_nonpos (le_of_lt hpos) h
  linarith

/-- **α-term non-negativity on `K_n` for sum-zero `Φ`.**

Inlined here (rather than imported from `SNFAlphaNonneg.lean`) because
that sibling file re-declares `S_NF_alpha` in the same namespace and
would collide with the `S_NF_alpha` of `SNF.lean`.

On `K_n` with `∑_i Φ_i = 0`, the Laplacian quadratic form satisfies
`Φᵀ L Φ = n · ‖Φ‖² ≥ 0`, so `α · Φᵀ L Φ ≥ 0` whenever `α ≥ 0`. -/
theorem S_NF_alpha_Kn_nonneg_local (α : ℝ) (n : ℕ) (hα : 0 ≤ α)
    (phi : Fin n → ℝ) (hphi : ∑ i, phi i = 0) :
    0 ≤ S_NF_alpha α (completeAdj n) phi := by
  unfold S_NF_alpha
  -- Rewrite the Laplacian quadratic form on the sum-zero subspace.
  rw [completeAdj_laplacian_sumZero_quadForm n phi hphi]
  -- Remaining goal: 0 ≤ α * ((n : ℝ) * ∑ i, phi i * phi i).
  have h_sum_nn : 0 ≤ ∑ i, phi i * phi i := sum_sq_nonneg phi
  have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have h_prod_nn : 0 ≤ (n : ℝ) * ∑ i, phi i * phi i :=
    mul_nonneg h_n_nn h_sum_nn
  exact mul_nonneg hα h_prod_nn

/-- **λ-term non-negativity under PosDef `A` with `det A ≤ 1`.**

`S_NF_lambda λ A = λ · B(A) = -λ · log(det A)` is non-negative when
`λ ≥ 0` and `det A ≤ 1` (so that `B(A) ≥ 0`). -/
theorem S_NF_lambda_nonneg_of_det_le_one {n : ℕ} (lam : ℝ) (hlam : 0 ≤ lam)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hdet : A.det ≤ 1) :
    0 ≤ S_NF_lambda lam A := by
  unfold S_NF_lambda
  have h_barrier_nonneg : 0 ≤ barrier A :=
    barrier_nonneg_of_det_le_one A hA hdet
  exact mul_nonneg hlam h_barrier_nonneg

/-- **N-Frame Lagrangian non-negativity on `K_n`.**

Under favourable hypotheses:

* couplings `α, β, λ ≥ 0`;
* vertex values `Φ : Fin n → ℝ` sum-zero on `K_n`
  (`∑_i Φ_i = 0`);
* gadget matrix `A` positive-definite with `det A ≤ 1`,

the three-term N-Frame Lagrangian

  `S_NF α β λ (completeAdj n) Φ χ A`

is non-negative. This is the termwise summing of

* α-term ≥ 0 (Dirichlet energy on `K_n` with sum-zero `Φ`);
* β-term ≥ 0 (parity penalty = sum of `max 0 …`);
* λ-term ≥ 0 (`B(A) ≥ 0` when `det A ≤ 1`).

Paper §28.3 pp. 137–138.

**Note on the `det A ≤ 1` hypothesis.** The paper barrier
`B(A) = −log det A` is non-negative precisely when `det A ≤ 1`
(since `log` is non-positive on `(0, 1]`). With couplings all
`≥ 0`, the sign alignment needed for the termwise bound `≥ 0`
forces `det A ≤ 1`; the dual regime `det A ≥ 1` yields
`B(A) ≤ 0` and so `λ · B(A) ≤ 0`. -/
theorem S_NF_nonneg_on_Kn (α β lam : ℝ) (n : ℕ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hlam : 0 ≤ lam)
    (phi chi : Fin n → ℝ) (hphi : ∑ i, phi i = 0)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hdet : A.det ≤ 1) :
    0 ≤ S_NF α β lam (completeAdj n) phi chi A := by
  rw [S_NF_decompose]
  have h1 : 0 ≤ S_NF_alpha α (completeAdj n) phi :=
    S_NF_alpha_Kn_nonneg_local α n hα phi hphi
  have h2 : 0 ≤ S_NF_beta β chi phi :=
    S_NF_beta_nonneg β hβ chi phi
  have h3 : 0 ≤ S_NF_lambda lam A :=
    S_NF_lambda_nonneg_of_det_le_one lam hlam A hA hdet
  linarith

end PallLean.Paper93.DeepMath.NFrame
