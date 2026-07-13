import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGlobalResidualFactorization
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBestPartitionExistence

/-!
# The global best-partition bond exists

Combines the global residual factorization (`GlobalResidual.residual_finrank_ge`) with the index-count and a
probabilistic existence over the **symmetrized** block, to land the genuine statement the earlier work overclaimed:

> `∃ f : (Fin (2h) → Bool) → K, ∀ balanced S, 2^r ≤ finrank(span(range (residualOf S f)))`.

* Piece (1) `indexImage_card` — `#{distinct residual characters at S} = 2^{rank(symM A S)}`, where `symM A S` is the
  symmetrized off-diagonal block `(A+Aᵀ)` supported on `S × Sᶜ`;
* Piece (2) `exists_symM_rank_ge` — a random `A` has `rank(symM A S) ≥ r` at every balanced cut;
* `exists_global_best_partition_bond` — the two combined: one function `QF A` whose residual span has dimension
  `≥ 2^r = 2^{Ω(n)}` across **every** balanced partition.

Existential (a random matrix); explicit is Valiant-open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.GlobalBestPartitionBond

open Matrix
open PallLean.Paper93.DeepMath.PathB.GlobalResidual
open PallLean.Paper93.DeepMath.PathB.LowRankCount
open PallLean.Paper93.DeepMath.PathB.BestPartitionExistence

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- `ZMod 2 → Bool` coordinatewise. -/
def toBoolN (v : Fin n → ZMod 2) : Fin n → Bool := fun i => decide (v i = 1)

theorem toBoolN_injective : Function.Injective (toBoolN (n := n)) := by
  intro v v' hvv
  funext i
  have hinj : Function.Injective (fun z : ZMod 2 => decide (z = 1)) := by decide
  exact hinj (congrFun hvv i)

/-- The symmetrized off-diagonal block matrix, `(Aᵢⱼ+Aⱼᵢ)` on `S × Sᶜ` and `0` elsewhere. -/
noncomputable def symM (A : Matrix (Fin n) (Fin n) (ZMod 2)) (S : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of (fun i j => if i ∈ S ∧ j ∈ Sᶜ then A i j + A j i else 0)

theorem idx_eq_mulVec (A : Matrix (Fin n) (Fin n) (ZMod 2)) (S : Finset (Fin n)) (α : Fin n → Bool) :
    idx A S α = symM A S *ᵥ (fun j => bit (α j)) := by
  funext i
  unfold idx symM
  rw [Matrix.mulVec]
  simp only [Matrix.of_apply, dotProduct]
  by_cases hi : i ∈ S
  · rw [if_pos hi, ← Finset.sum_add_sum_compl S]
    have h1 : (∑ j ∈ S, (if i ∈ S ∧ j ∈ Sᶜ then A i j + A j i else 0) * bit (α j)) = 0 := by
      apply Finset.sum_eq_zero; intro j hj
      rw [if_neg (by simp [Finset.mem_compl, hj]), zero_mul]
    rw [h1, zero_add]
    apply Finset.sum_congr rfl; intro j hj
    rw [if_pos ⟨hi, hj⟩]
  · rw [if_neg hi]
    symm
    apply Finset.sum_eq_zero; intro j _
    rw [if_neg (fun h => hi h.1), zero_mul]

theorem img_card_n (M : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (Finset.univ.image (fun a : Fin n → ZMod 2 => M *ᵥ a)).card = 2 ^ M.rank := by
  classical
  have h1 : (Finset.univ.image (fun a : Fin n → ZMod 2 => M *ᵥ a))
      = (LinearMap.range M.mulVecLin : Set (Fin n → ZMod 2)).toFinset := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_toFinset, SetLike.mem_coe,
      LinearMap.mem_range, Matrix.mulVecLin_apply]
  rw [h1, Set.toFinset_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card 2]
  rfl

/-- **Piece (1).**  The number of distinct residual characters of `QF A` at `S` is `2^{rank(symM A S)}`. -/
theorem indexImage_card (A : Matrix (Fin n) (Fin n) (ZMod 2)) (S : Finset (Fin n)) :
    (indexImage A S).card = 2 ^ (symM A S).rank := by
  classical
  have hyb : ∀ α, yb A S α = toBoolN (symM A S *ᵥ (fun j => bit (α j))) := by
    intro α; rw [← idx_eq_mulVec]; rfl
  have hsurj : Function.Surjective (fun α : Fin n → Bool => (fun j => bit (α j))) := by
    intro v
    refine ⟨toBoolN v, ?_⟩
    funext j
    simp only [toBoolN, bit]
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (v j) with h | h <;> simp [h]
  calc (indexImage A S).card
      = (Finset.univ.image (fun α : Fin n → Bool => toBoolN (symM A S *ᵥ (fun j => bit (α j))))).card := by
        unfold indexImage; rw [Finset.image_congr (fun α _ => hyb α)]
    _ = (Finset.univ.image (fun α : Fin n → Bool => symM A S *ᵥ (fun j => bit (α j)))).card := by
        have h : (Finset.univ.image (fun α : Fin n → Bool => toBoolN (symM A S *ᵥ (fun j => bit (α j)))))
            = (Finset.univ.image (fun α : Fin n → Bool => symM A S *ᵥ (fun j => bit (α j)))).image toBoolN := by
          rw [Finset.image_image]; rfl
        rw [h, Finset.card_image_of_injective _ toBoolN_injective]
    _ = (Finset.univ.image (fun v : Fin n → ZMod 2 => symM A S *ᵥ v)).card := by
        have h : (Finset.univ.image (fun α : Fin n → Bool => symM A S *ᵥ (fun j => bit (α j))))
            = Finset.univ.image (fun v : Fin n → ZMod 2 => symM A S *ᵥ v) := by
          rw [show (fun α : Fin n → Bool => symM A S *ᵥ (fun j => bit (α j)))
                = (fun v : Fin n → ZMod 2 => symM A S *ᵥ v) ∘ (fun α : Fin n → Bool => fun j => bit (α j))
              from rfl, ← Finset.image_image, Finset.image_univ_of_surjective hsurj]
        rw [h]
    _ = 2 ^ (symM A S).rank := img_card_n (symM A S)

end PallLean.Paper93.DeepMath.PathB.GlobalBestPartitionBond
