import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Real.Basic

/-!
# Rank of a block-diagonal matrix

Mathlib (v4.28.0) does not provide a direct `Matrix.rank_blockDiagonal` lemma.
We prove here that the rank of any single block is bounded above by the rank
of the full block-diagonal matrix (Option C of the task, the "lower bound on
one block"):
```
theorem rank_blockDiagonal_ge_one (M : ι → Matrix n n ℝ) (j : ι) :
    (M j).rank ≤ (Matrix.blockDiagonal M).rank
```

The argument goes through the characterisation
`Matrix.rank = finrank ℝ (range M.mulVecLin)` and an explicit zero-padding
linear embedding `e_j : (n → ℝ) → ((n × ι) → ℝ)` at block index `j`.

Concretely we show that
`(Matrix.blockDiagonal M).mulVecLin ∘ e_j = e_j ∘ (M j).mulVecLin`,
so the range of `(M j).mulVecLin` (finite-dimensional) embeds, via the
injective linear map `e_j`, into the range of `(Matrix.blockDiagonal M).mulVecLin`.
Since `e_j` is injective, the finrank is preserved and the inequality on ranks
follows by `Submodule.finrank_mono`.
-/

namespace PallLean.Paper93.DeepMath.BridgeB

open scoped BigOperators Matrix
open Matrix Module

/-- Zero-padding embedding into a single block index.

Given a block index `j : ι`, this map sends a vector `v : n → ℝ` to the vector
on `n × ι` that equals `v` on block `j` and `0` on the other blocks. -/
noncomputable def blockEmbed {ι n : Type*} [DecidableEq ι]
    (j : ι) : (n → ℝ) →ₗ[ℝ] (n × ι → ℝ) where
  toFun v := fun p => if p.2 = j then v p.1 else 0
  map_add' v w := by
    funext p
    by_cases h : p.2 = j
    · simp [h]
    · simp [h]
  map_smul' c v := by
    funext p
    by_cases h : p.2 = j
    · simp [h]
    · simp [h]

@[simp] lemma blockEmbed_apply {ι n : Type*} [DecidableEq ι]
    (j : ι) (v : n → ℝ) (p : n × ι) :
    blockEmbed j v p = if p.2 = j then v p.1 else 0 := rfl

lemma blockEmbed_injective {ι n : Type*} [DecidableEq ι]
    (j : ι) : Function.Injective (blockEmbed (n := n) (ι := ι) j) := by
  intro v w h
  funext i
  have := congrArg (fun f => f (i, j)) h
  simpa [blockEmbed_apply] using this

/-- Key identity: applying `blockDiagonal M` to a vector concentrated in block
`j` (via `blockEmbed j`) is the same as first applying `M j` and then
zero-padding back into block `j`. -/
lemma blockDiagonal_mulVec_blockEmbed {ι n : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype n] [DecidableEq n]
    (M : ι → Matrix n n ℝ) (j : ι) (v : n → ℝ) :
    (Matrix.blockDiagonal M) *ᵥ (blockEmbed j v) = blockEmbed j ((M j) *ᵥ v) := by
  funext p
  obtain ⟨i, k⟩ := p
  -- Expand mulVec and split the sum on the product index.
  show (fun jk => Matrix.blockDiagonal M (i, k) jk) ⬝ᵥ (blockEmbed j v)
      = (if k = j then ((fun l => M j i l) ⬝ᵥ v) else 0)
  simp only [dotProduct, Fintype.sum_prod_type]
  -- Swap the order of summation to put the block index outermost.
  rw [Finset.sum_comm]
  by_cases hkj : k = j
  · -- Block `k = j`: the only surviving outer term is `k' = j` with the block `M j` contribution.
    subst hkj
    rw [if_pos rfl]
    refine (Finset.sum_eq_single k ?_ ?_).trans ?_
    · intro k' _ hk'
      refine Finset.sum_eq_zero (fun l _ => ?_)
      rw [Matrix.blockDiagonal_apply_ne M i l (Ne.symm hk'), zero_mul]
    · intro hk
      exact (hk (Finset.mem_univ k)).elim
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Matrix.blockDiagonal_apply_eq]
      -- RHS: blockEmbed k v (l, k) = v l because k = k.
      simp [blockEmbed_apply]
  · -- Block `k ≠ j`: every contribution vanishes.
    rw [if_neg hkj]
    refine Finset.sum_eq_zero (fun k' _ => ?_)
    refine Finset.sum_eq_zero (fun l _ => ?_)
    -- If k' ≠ k, the blockDiagonal entry is 0.
    by_cases hk' : k' = k
    · -- k' = k means k' ≠ j since k ≠ j; then the embedded coord at (l, k') is 0.
      have hk'j : k' ≠ j := by rw [hk']; exact hkj
      have : blockEmbed j v (l, k') = 0 := by
        simp [blockEmbed_apply, hk'j]
      rw [this, mul_zero]
    · rw [Matrix.blockDiagonal_apply_ne M i l (Ne.symm hk'), zero_mul]

/-- **Option C.** The rank of any single block is at most the rank of the
block-diagonal matrix. -/
theorem rank_blockDiagonal_ge_one {ι n : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype n] [DecidableEq n]
    (M : ι → Matrix n n ℝ) (j : ι) :
    (M j).rank ≤ (Matrix.blockDiagonal M).rank := by
  classical
  -- We translate to a `finrank` inequality and use an injective linear embedding.
  -- First, by the definition of rank:
  -- rank A = finrank ℝ (range A.mulVecLin).
  -- We will show:
  --   (M j).mulVecLin factors through the blockEmbed on both input and output,
  -- so range ((M j).mulVecLin) is linearly equivalent (via blockEmbed) to a
  -- subspace of range ((blockDiagonal M).mulVecLin).
  -- Step 1: build a linear map ψ from (n → ℝ) to range of (blockDiagonal M).mulVecLin
  -- whose range equals `(blockEmbed j) (range (M j).mulVecLin)`.
  -- We use Submodule.finrank_mono and LinearMap.finrank_range_of_inj.
  -- Show: (blockEmbed j) (range (M j).mulVecLin) ≤ range ((blockDiagonal M).mulVecLin).
  have hsub :
      (LinearMap.range (M j).mulVecLin).map (blockEmbed (n := n) j)
        ≤ LinearMap.range (Matrix.blockDiagonal M).mulVecLin := by
    intro y hy
    rcases hy with ⟨w, hw_range, hw_eq⟩
    rcases hw_range with ⟨v, hv⟩
    refine ⟨blockEmbed j v, ?_⟩
    -- (blockDiagonal M).mulVecLin (blockEmbed j v) = blockEmbed j ((M j).mulVecLin v)
    -- = blockEmbed j w = y.
    have hbase := blockDiagonal_mulVec_blockEmbed M j v
    show (Matrix.blockDiagonal M) *ᵥ (blockEmbed j v) = y
    rw [hbase]
    have : (M j) *ᵥ v = w := hv
    rw [this, hw_eq]
  -- Step 2: compute finrank of the pushforward submodule.
  -- Since `blockEmbed j` is injective, the pushforward has the same finrank
  -- as the source submodule.
  have hinj : Function.Injective (blockEmbed (n := n) (ι := ι) j) := by
    intro v w h
    funext i
    have := congrArg (fun f => f (i, j)) h
    simpa [blockEmbed_apply] using this
  have hfinrank_map :
      Module.finrank ℝ
          ((LinearMap.range (M j).mulVecLin).map (blockEmbed (n := n) j))
        = Module.finrank ℝ (LinearMap.range (M j).mulVecLin) := by
    -- Use that blockEmbed j restricted to any submodule is injective.
    classical
    have hinj' : Function.Injective
        ((blockEmbed (n := n) (ι := ι) j).domRestrict
          (LinearMap.range (M j).mulVecLin)) := by
      intro ⟨v, hv⟩ ⟨w, hw⟩ hEq
      apply Subtype.ext
      apply hinj
      simpa using hEq
    -- The range of domRestrict is exactly (p).map (blockEmbed j).
    have hrange :
        LinearMap.range ((blockEmbed (n := n) (ι := ι) j).domRestrict
            (LinearMap.range (M j).mulVecLin))
          = (LinearMap.range (M j).mulVecLin).map (blockEmbed (n := n) j) := by
      ext x
      constructor
      · rintro ⟨⟨v, hv⟩, rfl⟩
        exact ⟨v, hv, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨⟨v, hv⟩, rfl⟩
    rw [← hrange, LinearMap.finrank_range_of_inj hinj']
  -- Now combine: finrank of map ≤ finrank of ambient range, and equals finrank of source.
  calc (M j).rank
      = Module.finrank ℝ (LinearMap.range (M j).mulVecLin) := rfl
    _ = Module.finrank ℝ
          ((LinearMap.range (M j).mulVecLin).map (blockEmbed (n := n) j)) := hfinrank_map.symm
    _ ≤ Module.finrank ℝ
          (LinearMap.range (Matrix.blockDiagonal M).mulVecLin) := Submodule.finrank_mono hsub
    _ = (Matrix.blockDiagonal M).rank := rfl

end PallLean.Paper93.DeepMath.BridgeB
