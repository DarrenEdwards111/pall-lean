import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Normed

open scoped Matrix.Norms.Elementwise

/-!
# Differentiability of `Matrix.det` and `log ∘ det` (N-Frame)

This file wraps Mathlib's differentiability machinery to establish that
the determinant function on real `n × n` matrices is differentiable
everywhere, and that `log ∘ det` is differentiable on the open half
`{M | 0 < det M}`.

Mathlib does not expose a single `Differentiable.matrix_det` lemma
analogous to `Continuous.matrix_det`; instead we reduce to `Matrix.det`
via its permutation-sum expansion `Matrix.det_apply`, which expresses
`det M` as a finite sum (over `Equiv.Perm (Fin n)`) of signed finite
products of matrix entries. Since each entry `M i j` is a component of
the Pi-type `Matrix (Fin n) (Fin n) ℝ = Fin n → Fin n → ℝ`, it is a
differentiable linear functional of `M`, and the sum/product/scalar
operations preserve differentiability.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

open scoped BigOperators

namespace PallLean.Paper93.DeepMath.NFrame

/-- The determinant function `Matrix (Fin n) (Fin n) ℝ → ℝ` is differentiable
    everywhere. Built from the permutation-sum expansion `Matrix.det_apply`
    together with Mathlib's `Differentiable.sum`, `Differentiable.finset_prod`,
    `Differentiable.const_smul`, and `differentiable_apply`. -/
theorem det_differentiable {n : ℕ} :
    Differentiable ℝ (fun M : Matrix (Fin n) (Fin n) ℝ => M.det) := by
  -- Rewrite `det` as a sum over permutations of a signed product of entries.
  have h_eq : (fun M : Matrix (Fin n) (Fin n) ℝ => M.det) =
      (fun M : Matrix (Fin n) (Fin n) ℝ =>
        ∑ σ : Equiv.Perm (Fin n),
          Equiv.Perm.sign σ • ∏ i : Fin n, M (σ i) i) := by
    funext M
    exact Matrix.det_apply M
  rw [h_eq]
  -- Differentiability of a finite sum (pointwise in `M`).
  apply Differentiable.fun_sum
  intro σ _
  -- Each summand: `sign σ • ∏ i, M (σ i) i`.  Use `const_smul`.
  apply Differentiable.const_smul
  -- Finite product of differentiable real-valued functions on a normed space.
  -- We prove this by induction on the Finset using `Finset.induction_on`.
  have hentry : ∀ i : Fin n,
      Differentiable ℝ (fun M : Matrix (Fin n) (Fin n) ℝ => M (σ i) i) := by
    intro i
    have h1 : Differentiable ℝ (fun M : Matrix (Fin n) (Fin n) ℝ => M (σ i)) :=
      differentiable_apply (σ i)
    have h2 : Differentiable ℝ (fun f : Fin n → ℝ => f i) :=
      differentiable_apply i
    exact h2.comp h1
  -- Induction on the universal finset over `Fin n`.
  suffices h : ∀ (s : Finset (Fin n)),
      Differentiable ℝ (fun M : Matrix (Fin n) (Fin n) ℝ => ∏ i ∈ s, M (σ i) i) by
    have := h (Finset.univ : Finset (Fin n))
    convert this using 1
  intro s
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact differentiable_const (1 : ℝ)
  | insert i s hi ih =>
    have hprod : (fun M : Matrix (Fin n) (Fin n) ℝ =>
        ∏ j ∈ insert i s, M (σ j) j) =
      (fun M => M (σ i) i) * (fun M => ∏ j ∈ s, M (σ j) j) := by
      funext M
      rw [Finset.prod_insert hi]
      rfl
    rw [hprod]
    exact (hentry i).mul ih

/-- On the open set `{M : det M > 0}`, `log ∘ det` is differentiable. -/
theorem log_det_differentiable_on {n : ℕ} :
    DifferentiableOn ℝ (fun M : Matrix (Fin n) (Fin n) ℝ => Real.log M.det)
      {M | 0 < M.det} := by
  apply DifferentiableOn.log
  · exact det_differentiable.differentiableOn
  · intro M hM
    exact ne_of_gt hM

end PallLean.Paper93.DeepMath.NFrame
