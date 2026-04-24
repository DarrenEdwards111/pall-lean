import PallLean.Paper93.DeepMath.LPS.KnLaplacianEig

namespace PallLean.Paper93.DeepMath.LPS

open PallLean.Paper93.DeepMath.GraphSpectral
open Matrix

/-- **K_n Laplacian quadratic form on sum-zero vectors.**

For the complete-graph Laplacian `L := laplacian (completeAdj n)`, any
vector `v : Fin n → ℝ` with `∑ i, v i = 0` satisfies
`vᵀ L v = n · ‖v‖²`, where `‖v‖² = ∑ i, v i * v i`.

This is the quadratic-form corollary of the pointwise eigenvalue
identity `L v = n • v` on the sum-zero subspace
(`completeAdj_laplacian_sumZero_eigen`). -/
theorem completeAdj_laplacian_sumZero_quadForm (n : ℕ) (v : Fin n → ℝ)
    (hv : ∑ i, v i = 0) :
    ∑ i, v i * ((laplacian (completeAdj n)).mulVec v i) =
      (n : ℝ) * ∑ i, v i * v i := by
  -- Pointwise eigenvalue identity on the sum-zero subspace:
  --   L.mulVec v = (n : ℝ) • v, i.e. (L.mulVec v) i = n * v i.
  have heigFun : (laplacian (completeAdj n)).mulVec v = (n : ℝ) • v :=
    completeAdj_laplacian_sumZero_eigen n v hv
  have heig : ∀ i, (laplacian (completeAdj n)).mulVec v i = (n : ℝ) * v i := by
    intro i
    have := congrArg (fun f : Fin n → ℝ => f i) heigFun
    simpa [Pi.smul_apply, smul_eq_mul] using this
  -- Substitute and factor out the scalar n.
  simp only [heig]
  -- Goal: ∑ i, v i * ((n : ℝ) * v i) = (n : ℝ) * ∑ i, v i * v i
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros i _
  ring

end PallLean.Paper93.DeepMath.LPS
