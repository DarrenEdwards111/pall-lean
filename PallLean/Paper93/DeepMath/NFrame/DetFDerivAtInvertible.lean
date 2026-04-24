import PallLean.Paper93.DeepMath.NFrame.DetDifferentiable

/-!
# Fréchet derivative of `Matrix.det` at invertible matrices (N-Frame)

At an invertible matrix `A : Matrix (Fin n) (Fin n) ℝ`, the determinant
function has a Fréchet derivative. The standard matrix-calculus result
(the Jacobi formula) identifies this derivative with the continuous
linear map `ΔA ↦ (A.adjugate * ΔA).trace`. We prove here only the
existence form:

  `∃ L, HasFDerivAt Matrix.det L A`

using the everywhere-differentiability theorem
`PallLean.Paper93.DeepMath.NFrame.det_differentiable`. The invertibility
hypothesis is carried through unused — existence of the Fréchet
derivative in fact holds at every matrix, but the invertible case is
what is needed downstream for the Jacobi-formula identification.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- At an invertible matrix, `Matrix.det` has a Fréchet derivative.

    The Jacobi formula identifies the derivative with the continuous
    linear map `ΔA ↦ (A.adjugate * ΔA).trace`, but here we record only
    the weaker existence statement: the Fréchet derivative exists (as a
    continuous linear functional) at `A`.

    The proof uses `det_differentiable`, which establishes that `det`
    is differentiable everywhere on `Matrix (Fin n) (Fin n) ℝ`, so in
    particular at `A`. The existence of a Fréchet derivative follows
    immediately, with witness `fderiv ℝ Matrix.det A`. -/
theorem det_hasFDerivAt_invertible {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsUnit A.det) :
    ∃ (L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ),
      HasFDerivAt (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ) L A := by
  -- `hA` is unused at the existence level: `det` is differentiable
  -- everywhere, so the Fréchet derivative exists at every point.
  let _hA' := hA
  -- `det_differentiable` gives `Differentiable ℝ Matrix.det`; specialise
  -- at `A` and extract the Fréchet derivative witness.
  refine ⟨fderiv ℝ (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ) A, ?_⟩
  have hdiff : DifferentiableAt ℝ (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ) A :=
    (det_differentiable (n := n)).differentiableAt
  exact hdiff.hasFDerivAt

end PallLean.Paper93.DeepMath.NFrame
