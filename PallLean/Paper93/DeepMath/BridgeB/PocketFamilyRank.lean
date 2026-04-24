import PallLean.Paper93.DeepMath.BridgeB.PocketFamily
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace PallLean.Paper93.DeepMath.BridgeB

open PallLean.Paper93.DeepMath.GadgetRank
open scoped BigOperators Matrix

/-- Currying linear equivalence: `(n × ι → R)` is linearly equivalent to `ι → n → R`,
where both sides are indexed `R`-modules of matching shape.  This is the standard
currying isomorphism specialised for the product domain `n × ι`. -/
private def blockCurry (n ι : Type*) (R : Type*) [Semiring R] :
    ((n × ι) → R) ≃ₗ[R] (ι → n → R) where
  toFun x := fun k i => x (i, k)
  invFun y := fun p => y p.2 p.1
  left_inv _ := by funext ⟨_, _⟩; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Under the currying equivalence `blockCurry`, the `mulVec`-linear map of a
block-diagonal matrix corresponds to the pointwise product of the block
`mulVec`-linear maps. -/
private lemma blockCurry_mulVecLin_blockDiagonal
    {n ι : Type*} {R : Type*}
    [CommSemiring R] [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
    (M : ι → Matrix n n R) (x : (n × ι) → R) (k : ι) (i : n) :
    ((Matrix.blockDiagonal M).mulVec x) (i, k)
      = (M k).mulVec (fun j => x (j, k)) i := by
  -- Unfold mulVec and split the double sum over `j × k'`.
  show (fun jk => Matrix.blockDiagonal M (i, k) jk) ⬝ᵥ x
    = (fun j => M k i j) ⬝ᵥ (fun j => x (j, k))
  simp only [dotProduct]
  rw [Fintype.sum_prod_type]
  -- Swap to sum over `k'` outer.
  rw [Finset.sum_comm]
  -- Collapse the `k'` sum: only `k' = k` contributes.
  refine (Finset.sum_eq_single k ?_ ?_).trans ?_
  · intro k' _ hk'
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [Matrix.blockDiagonal_apply_ne M i j (Ne.symm hk'), zero_mul]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Matrix.blockDiagonal_apply_eq]

/-- Under the currying equivalence, the block-diagonal `mulVecLin` factors as
a `LinearMap.pi` of the block `mulVecLin`s composed with coordinate projections. -/
private lemma blockCurry_comp_blockDiagonal_mulVecLin
    {n ι : Type*} {R : Type*}
    [CommSemiring R] [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
    (M : ι → Matrix n n R) :
    (blockCurry n ι R : ((n × ι) → R) →ₗ[R] (ι → n → R))
        ∘ₗ (Matrix.blockDiagonal M).mulVecLin
      = (LinearMap.pi
            (fun k : ι => (M k).mulVecLin.comp
              (LinearMap.proj k : (ι → n → R) →ₗ[R] (n → R))))
          ∘ₗ (blockCurry n ι R : ((n × ι) → R) →ₗ[R] (ι → n → R)) := by
  refine LinearMap.ext (fun x => ?_)
  funext k i
  show ((Matrix.blockDiagonal M).mulVec x) (i, k)
    = ((M k).mulVec (fun j => x (j, k))) i
  exact blockCurry_mulVecLin_blockDiagonal M x k i

/-- Finrank of the range of the block-diagonal `mulVecLin` equals the sum of
finranks of the per-block ranges. -/
private lemma finrank_range_blockDiagonal_mulVecLin
    {n ι : Type*}
    [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
    (M : ι → Matrix n n ℝ) :
    Module.finrank ℝ (LinearMap.range (Matrix.blockDiagonal M).mulVecLin)
      = ∑ k, Module.finrank ℝ (LinearMap.range (M k).mulVecLin) := by
  -- Step 1: Conjugate by the `blockCurry` equivalence to reduce to the `LinearMap.pi`
  -- version.  `Submodule.map_equiv` preserves finrank.
  have hconj :
      (blockCurry n ι ℝ : ((n × ι) → ℝ) →ₗ[ℝ] (ι → n → ℝ))
          ∘ₗ (Matrix.blockDiagonal M).mulVecLin
        = (LinearMap.pi
              (fun k : ι => (M k).mulVecLin.comp
                (LinearMap.proj k : (ι → n → ℝ) →ₗ[ℝ] (n → ℝ))))
            ∘ₗ (blockCurry n ι ℝ : ((n × ι) → ℝ) →ₗ[ℝ] (ι → n → ℝ)) :=
    blockCurry_comp_blockDiagonal_mulVecLin M
  -- Finrank of range equals finrank of image under the equiv.
  have hfinrank_eq :
      Module.finrank ℝ (LinearMap.range (Matrix.blockDiagonal M).mulVecLin)
        = Module.finrank ℝ (LinearMap.range
            ((blockCurry n ι ℝ : ((n × ι) → ℝ) →ₗ[ℝ] (ι → n → ℝ))
              ∘ₗ (Matrix.blockDiagonal M).mulVecLin)) := by
    rw [LinearMap.range_comp]
    exact ((blockCurry n ι ℝ).finrank_map_eq
        (LinearMap.range (Matrix.blockDiagonal M).mulVecLin)).symm
  rw [hfinrank_eq, hconj]
  -- Now the LHS involves the range of `pi f_k ∘ₗ blockCurry`.
  rw [LinearMap.range_comp,
      LinearEquiv.range, Submodule.map_top]
  -- Goal: finrank of range of `LinearMap.pi ...` equals ∑ k, finrank (range (M k).mulVecLin).
  -- Step 2: Construct a LinearEquiv between this range and `Π k, range (M k).mulVecLin`.
  let rangeProduct :
      (LinearMap.range
        (LinearMap.pi (fun k : ι =>
          (M k).mulVecLin.comp (LinearMap.proj k : (ι → n → ℝ) →ₗ[ℝ] (n → ℝ)))))
        ≃ₗ[ℝ] ((k : ι) → (LinearMap.range (M k).mulVecLin)) :=
    { toFun := fun y k => ⟨y.1 k, by
        rcases y.2 with ⟨v, hv⟩
        refine ⟨v k, ?_⟩
        have := congrArg (fun f => f k) hv
        simpa using this⟩
      invFun := fun y => ⟨fun k => (y k).1, by
        choose v hv using fun k => (y k).2
        refine ⟨fun k => v k, ?_⟩
        funext k
        simpa using hv k⟩
      left_inv := fun y => by
        apply Subtype.ext
        funext k
        rfl
      right_inv := fun y => by
        funext k
        apply Subtype.ext
        rfl
      map_add' := fun _ _ => by funext k; apply Subtype.ext; rfl
      map_smul' := fun _ _ => by funext k; apply Subtype.ext; rfl }
  rw [rangeProduct.finrank_eq]
  exact Module.finrank_pi_fintype ℝ

/-- Rank of a block-diagonal matrix equals the sum of the ranks of its blocks. -/
theorem rank_blockDiagonal
    {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
    (M : ι → Matrix n n ℝ) :
    (Matrix.blockDiagonal M).rank = ∑ k, (M k).rank := by
  unfold Matrix.rank
  exact finrank_range_blockDiagonal_mulVecLin M

/-- Rank of the uniform κ-pocket gadget equals κ times the single-pocket rank. -/
theorem pocketFamily_rank (α : ℝ) (κ n : ℕ) :
    (pocketFamily α κ n).rank = κ * (compiledGadget α n).rank := by
  unfold pocketFamily
  rw [rank_blockDiagonal]
  -- ∑ i : Fin κ, (compiledGadget α n).rank = κ * (compiledGadget α n).rank
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end PallLean.Paper93.DeepMath.BridgeB
