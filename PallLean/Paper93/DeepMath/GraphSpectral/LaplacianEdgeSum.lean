import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef
import PallLean.Paper93.DeepMath.GraphSpectral.DirichletLaplacianId

namespace PallLean.Paper93.DeepMath.GraphSpectral

open Finset

/-- Classical graph Laplacian identity: for symmetric `A`,
    `2 · (φᵀ L φ) = ∑ i, ∑ j, A_ij · (φᵢ − φⱼ)²`. -/
theorem laplacian_quadForm_eq_edge_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hSym : A.IsSymm) (phi : Fin n → ℝ) :
    2 * (∑ i, phi i * ((laplacian A).mulVec phi i)) =
      ∑ i, ∑ j, A i j * (phi i - phi j)^2 := by
  -- Rewrite the LHS using the expansion of the Laplacian quadratic form.
  rw [laplacian_quadForm_expand]
  -- Expand the squared difference in the RHS.
  have h_RHS : ∀ i j, A i j * (phi i - phi j)^2 =
      A i j * phi i * phi i - 2 * (A i j * phi i * phi j) + A i j * phi j * phi j := by
    intros i j; ring
  -- Apply the expansion term-by-term to the double sum.
  have hExpand :
      (∑ i, ∑ j, A i j * (phi i - phi j)^2) =
      (∑ i, ∑ j, (A i j * phi i * phi i -
                  2 * (A i j * phi i * phi j) +
                  A i j * phi j * phi j)) := by
    refine Finset.sum_congr rfl ?_
    intros i _
    refine Finset.sum_congr rfl ?_
    intros j _
    exact h_RHS i j
  rw [hExpand]
  -- Split each inner sum into three pieces.
  have hSplitInner : ∀ i : Fin n,
      (∑ j, (A i j * phi i * phi i -
             2 * (A i j * phi i * phi j) +
             A i j * phi j * phi j)) =
      (∑ j, A i j * phi i * phi i) -
      (∑ j, 2 * (A i j * phi i * phi j)) +
      (∑ j, A i j * phi j * phi j) := by
    intro i
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [hSplitInner]
  -- Now split the outer sum similarly.
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- Simplify each outer summand.
  -- Term 1:  ∑ i, ∑ j, A i j * phi i * phi i = ∑ i, (∑ j, A i j) * phi i * phi i.
  have hT1 :
      (∑ i : Fin n, ∑ j, A i j * phi i * phi i) =
      (∑ i : Fin n, (∑ j, A i j) * phi i * phi i) := by
    refine Finset.sum_congr rfl ?_
    intros i _
    rw [← Finset.sum_mul, ← Finset.sum_mul]
  -- Term 3 (after symmetry):  ∑ i, ∑ j, A i j * phi j * phi j
  --                         = ∑ j, ∑ i, A i j * phi j * phi j   (sum_comm)
  --                         = ∑ j, (∑ i, A i j) * phi j * phi j
  --                         = ∑ j, (rowSum j) * phi j * phi j   (by hSym)
  --                         = ∑ i, (rowSum i) * phi i * phi i.
  have hT3 :
      (∑ i : Fin n, ∑ j, A i j * phi j * phi j) =
      (∑ i : Fin n, (∑ j, A i j) * phi i * phi i) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intros i _
    -- ∑ j, A j i * phi i * phi i  =  (∑ j, A j i) * phi i * phi i.
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    -- Use symmetry to replace  ∑ j, A j i  with  ∑ j, A i j.
    have hRow : (∑ j, A j i) = (∑ j, A i j) := by
      refine Finset.sum_congr rfl ?_
      intros j _
      exact hSym.apply i j
    rw [hRow]
  -- Term 2:  ∑ i, ∑ j, 2 * (A i j * phi i * phi j)
  --       = 2 * ∑ i, ∑ j, A i j * phi i * phi j.
  have hT2 :
      (∑ i : Fin n, ∑ j, 2 * (A i j * phi i * phi j)) =
      2 * (∑ i : Fin n, ∑ j, A i j * phi i * phi j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intros i _
    rw [Finset.mul_sum]
  rw [hT1, hT3, hT2]
  ring

end PallLean.Paper93.DeepMath.GraphSpectral
