import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBestPartitionReduction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBestPartitionExistence

/-!
# From the rank-rigid matrix to the entanglement bond

Connects `exists_best_partition_hard` (a matrix whose every balanced off-diagonal block has rank `≥ r`) to the
actual tensor **bond** via `chi_subset_finrank`.  The residuals of the bilinear form across a cut are the characters
`χ_{Bᵀa}`; of these, `|range(Bᵀ)| = 2^{rank_{𝔽₂}(B)}` are distinct, and distinct characters are independent
(`chi_subset_finrank`), so the bond (residual-span dimension) is exactly `2^{rank B}`.

* `charBlockSet B` — the `2^{rank B}` distinct residual characters of the block `B`;
* `block_bond_eq` — their span has dimension exactly `2^{rank B}` (the reduction's rank formula, `chi_subset_finrank`
  + `Module.card_eq_pow_finrank`);
* `exists_best_partition_bond` — **there is a matrix whose bond across every balanced partition is `≥ 2^r = 2^{Ω(n)}`**.

## Honest scope

Existential (a random matrix), not explicit (Valiant-open).  A genuine best-partition-hard entanglement bound,
end to end.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BestPartitionBond

open Matrix
open PallLean.Paper93.DeepMath.PathB.InnerProductCommRank
open PallLean.Paper93.DeepMath.PathB.BestPartitionReduction
open PallLean.Paper93.DeepMath.PathB.BestPartitionExistence

variable {K : Type*} [Field K] [CharZero K] {h r : ℕ}

/-- Coordinatewise `ZMod 2 → Bool`. -/
def toBoolVec (c : Fin h → ZMod 2) : Fin h → Bool := fun i => decide (c i = 1)

theorem toBoolVec_injective : Function.Injective (toBoolVec (h := h)) := by
  intro c c' hcc
  funext i
  have : decide (c i = 1) = decide (c' i = 1) := congrFun hcc i
  have hinj : Function.Injective (fun z : ZMod 2 => decide (z = 1)) := by decide
  exact hinj this

/-- The set of distinct residual characters of the block `B` (indexed by `Bᵀa`). -/
noncomputable def charBlockSet (B : Matrix (Fin h) (Fin h) (ZMod 2)) : Finset (Fin h → Bool) :=
  Finset.univ.image (fun a : Fin h → ZMod 2 => toBoolVec (B.transpose *ᵥ a))

/-- `|image(Bᵀ)| = 2^{rank B}`. -/
theorem img_card (B : Matrix (Fin h) (Fin h) (ZMod 2)) :
    (Finset.univ.image (fun a : Fin h → ZMod 2 => B.transpose *ᵥ a)).card = 2 ^ B.rank := by
  classical
  have h1 : (Finset.univ.image (fun a : Fin h → ZMod 2 => B.transpose *ᵥ a))
      = (LinearMap.range B.transpose.mulVecLin : Set (Fin h → ZMod 2)).toFinset := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_toFinset, SetLike.mem_coe,
      LinearMap.mem_range, Matrix.mulVecLin_apply]
  rw [h1, Set.toFinset_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card 2]
  congr 1
  rw [← Matrix.rank_transpose (A := B)]
  rfl

/-- The block has exactly `2^{rank B}` distinct residual characters. -/
theorem charBlockSet_card (B : Matrix (Fin h) (Fin h) (ZMod 2)) :
    (charBlockSet B).card = 2 ^ B.rank := by
  classical
  have heq : charBlockSet B
      = (Finset.univ.image (fun a : Fin h → ZMod 2 => B.transpose *ᵥ a)).image toBoolVec := by
    unfold charBlockSet
    rw [Finset.image_image]
    rfl
  rw [heq, Finset.card_image_of_injective _ toBoolVec_injective, img_card]

/-- **The bond of a block equals `2^{rank B}`.**  The distinct residual characters are linearly independent
(`chi_subset_finrank`), so their span — the tensor bond across the cut — has dimension exactly `2^{rank B}`. -/
theorem block_bond_eq (B : Matrix (Fin h) (Fin h) (ZMod 2)) :
    Module.finrank K
        (Submodule.span K (Set.range (fun t : (charBlockSet B) => chi (K := K) t.val)))
      = 2 ^ B.rank := by
  rw [chi_subset_finrank, charBlockSet_card]

/-- **A best-partition-hard entanglement bound exists.**  For `2r + 2 < h`, there is an `𝔽₂` matrix on `2h`
variables whose tensor bond across **every** balanced partition is `≥ 2^r = 2^{Ω(n)}`. -/
theorem exists_best_partition_bond (hh : 2 * r + 2 < h) :
    ∃ M : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2),
      ∀ S : Finset (Fin (2 * h)), S.card = h →
        2 ^ r ≤ Module.finrank K
          (Submodule.span K (Set.range (fun t : (charBlockSet (blk S M)) => chi (K := K) t.val))) := by
  obtain ⟨M, hM⟩ := exists_best_partition_hard hh
  refine ⟨M, fun S hS => ?_⟩
  rw [block_bond_eq]
  exact Nat.pow_le_pow_right (by norm_num) (hM S hS)

end PallLean.Paper93.DeepMath.PathB.BestPartitionBond

#print axioms PallLean.Paper93.DeepMath.PathB.BestPartitionBond.block_bond_eq
#print axioms PallLean.Paper93.DeepMath.PathB.BestPartitionBond.exists_best_partition_bond
