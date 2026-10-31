import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMPSCostLowerBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTensorEntanglementHardF

/-!
# Concrete MPS cost bound for `hardF`

Instantiates the fixed-ordering cost bound `mps_cost_ge_rank` for the parity-multiplexer `hardF`.  In `hardF`'s
natural variable layout, block `0`'s address bits are variables `0, …, b−1` (`addrBitVar 0 j = ⟨j, _⟩`), so they
are exactly the **first `b` sites** an MPS reads.  The prefix cut at `j = b` is therefore block `0`'s address
block, where the cross-cut rank is `≥ 2^b − 1` (`hardF_dimResiduals_ge`).

`hardF_mps_cost_ge` — **any MPS computing `hardF` in its natural variable order has cost `≥ 2^b − 1`** — exponential
in the block length.  No reordering hypothesis: the natural order already reads block `0` as a prefix.

## Honest scope

Fixed-ordering (the natural layout puts block `0` first).  The min over orderings collapses, so this is a
restricted tensor-network cost lower bound, not a separation.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MPSCostHardF

open PallLean.Paper93.DeepMath.PathB.NecHard
open PallLean.Paper93.DeepMath.PathB.MPSCost
open PallLean.Paper93.DeepMath.PathB.TensorEntanglementHardF

variable {K : Type*} [Field K] {b m χ : ℕ}

/-- `b ≤ nn b m`: the address block fits (since `b < 2^b ≤ Dsize b ≤ nn`). -/
theorem b_le_nn : b ≤ nn b m := by
  have hb2 : b ≤ Dsize b := by
    have hcard : Dsize b = 2 ^ b := by
      simp only [Dsize]
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [hcard]; exact (Nat.lt_two_pow_self).le
  calc b ≤ Dsize b := hb2
    _ ≤ nn b m := by show Dsize b ≤ m * b + Dsize b; omega

/-- `1 ≤ nn b m` (the variable count is positive). -/
theorem one_le_nn : 1 ≤ nn b m := by
  have : 0 < Dsize b := Fintype.card_pos
  show 1 ≤ m * b + Dsize b; omega

/-- The first `b` sites of the natural order are exactly block `0`'s address bits. -/
theorem cutBlock_b_eq_blockS_zero (hm : 0 < m) :
    cutBlock (nn b m) b = blockS (⟨0, hm⟩ : Fin m) := by
  have hbN : b ≤ nn b m := b_le_nn
  have hce : ∀ j : Fin b, Fin.castLE hbN j = addrBitVar (⟨0, hm⟩ : Fin m) j := by
    intro j; apply Fin.ext; simp [addrBitVar]
  have hlist : List.take b (List.finRange (nn b m))
      = (List.finRange b).map (Fin.castLE hbN) := by
    apply List.ext_getElem
    · rw [List.length_take, List.length_finRange, List.length_map, List.length_finRange,
        min_eq_left hbN]
    · intro k h1 h2
      rw [List.getElem_take, List.getElem_finRange, List.getElem_map, List.getElem_finRange]
      rfl
  unfold cutBlock
  rw [hlist]
  ext i
  simp only [List.mem_toFinset, List.mem_map, List.mem_finRange, blockS, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩; exact ⟨j, by rw [← hce j]; exact hj⟩
  · rintro ⟨j, hj⟩; exact ⟨j, by rw [hce j]; exact hj⟩

/-- **Concrete cost bound.**  Any MPS computing `hardF` in its natural variable order has cost `≥ 2^b − 1`. -/
theorem hardF_mps_cost_ge (hm : 0 < m) (M : MPS (nn b m) χ K)
    (heval : M.eval = hardFK K b m) :
    Dsize b - 1 ≤ M.cost := by
  have h1 := mps_cost_ge_rank M b (one_le_nn)
  rw [cutBlock_b_eq_blockS_zero hm, heval] at h1
  exact le_trans (hardF_dimResiduals_ge (K := K) (⟨0, hm⟩ : Fin m)) h1

end PallLean.Paper93.DeepMath.PathB.MPSCostHardF

#print axioms PallLean.Paper93.DeepMath.PathB.MPSCostHardF.hardF_mps_cost_ge
