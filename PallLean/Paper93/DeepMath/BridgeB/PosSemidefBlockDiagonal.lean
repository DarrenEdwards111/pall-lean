import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Block

namespace PallLean.Paper93.DeepMath.BridgeB

open scoped BigOperators Matrix

/-- Block-diagonal of PosSemidef blocks is PosSemidef.

Mathlib (v4.28.0) does not provide a direct wrapper
`Matrix.PosSemidef.blockDiagonal`, so we prove this from the characterisation
`posSemidef_iff_dotProduct_mulVec`: a Hermitian matrix `A` is PSD iff
`star x ⬝ᵥ (A *ᵥ x) ≥ 0` for every vector `x`. The Hermitian property follows
from `blockDiagonal_conjTranspose`, and the quadratic form on a product index
decomposes block-by-block. -/
theorem posSemidef_blockDiagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : ι → Matrix n n ℝ)
    (hM : ∀ i, (M i).PosSemidef) :
    (Matrix.blockDiagonal M).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · -- Hermitian: (blockDiagonal M)ᴴ = blockDiagonal (fun k => (M k)ᴴ) = blockDiagonal M.
    unfold Matrix.IsHermitian
    rw [Matrix.blockDiagonal_conjTranspose]
    congr 1
    funext k
    exact (hM k).isHermitian
  · -- Quadratic form: star x ⬝ᵥ blockDiagonal M *ᵥ x = ∑ k, star (xₖ) ⬝ᵥ (M k *ᵥ xₖ).
    intro x
    -- For each block index `k`, define the slice `xSlice k j = x (j, k)`.
    set xSlice : ι → n → ℝ := fun k j => x (j, k) with hxSlice
    -- Rewrite the dot product on the product index as a double sum and split
    -- into block slices. We then show each slice term is nonneg and sum.
    -- Key per-row identity: `blockDiagonal M *ᵥ x` at `(i, k)` equals `M k *ᵥ xSlice k` at `i`.
    have hmulVec_row : ∀ (i : n) (k : ι),
        (Matrix.blockDiagonal M *ᵥ x) (i, k) = (M k *ᵥ xSlice k) i := by
      intro i k
      -- Unfold mulVec and dotProduct, then split the Fintype product.
      show (fun jk => Matrix.blockDiagonal M (i, k) jk) ⬝ᵥ x
        = (fun j => M k i j) ⬝ᵥ xSlice k
      simp only [dotProduct]
      rw [Fintype.sum_prod_type]
      -- Swap order of summation so the outer index is k'.
      rw [Finset.sum_comm]
      -- The sum over k' collapses: only k' = k contributes.
      refine (Finset.sum_eq_single k ?_ ?_).trans ?_
      · -- Off-diagonal k' ≠ k: every term is zero.
        intro k' _ hk'
        refine Finset.sum_eq_zero (fun j _ => ?_)
        rw [Matrix.blockDiagonal_apply_ne M i j (Ne.symm hk'), zero_mul]
      · -- k not in univ: impossible.
        intro hk
        exact (hk (Finset.mem_univ k)).elim
      · -- Diagonal term equals the block row action.
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Matrix.blockDiagonal_apply_eq]
    have hexpand :
        star x ⬝ᵥ (Matrix.blockDiagonal M *ᵥ x)
          = ∑ k, star (xSlice k) ⬝ᵥ (M k *ᵥ xSlice k) := by
      -- Expand outer dot product on the product index and reassemble by block.
      simp only [dotProduct]
      rw [Fintype.sum_prod_type]
      -- Swap the order to sum first over `k`, then over `i`.
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hmulVec_row i k]
      -- `x (i, k) = xSlice k i` is definitional.
      rfl
    rw [hexpand]
    refine Finset.sum_nonneg (fun k _ => ?_)
    -- Each block term is nonneg because M k is PSD.
    exact (Matrix.posSemidef_iff_dotProduct_mulVec.mp (hM k)).2 (xSlice k)

end PallLean.Paper93.DeepMath.BridgeB
