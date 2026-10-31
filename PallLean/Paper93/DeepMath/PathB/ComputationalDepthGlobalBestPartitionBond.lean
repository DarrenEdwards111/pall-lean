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
open PallLean.Paper93.DeepMath.PathB.TensorEntanglement

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

/-! ## Piece (2): existence over the symmetrized block -/

variable {h r : ℕ}

/-- The entries of `A` outside the `S × Sᶜ` block. -/
def complP (S : Finset (Fin (2 * h))) : Type :=
  {p : Fin (2 * h) × Fin (2 * h) // ¬(p.1 ∈ S ∧ p.2 ∈ Sᶜ)}

noncomputable instance (S : Finset (Fin (2 * h))) : Fintype (complP S) := by
  unfold complP; infer_instance

/-- `A` restricted to the complement of the `S × Sᶜ` block. -/
noncomputable def restA (S : Finset (Fin (2 * h)))
    (A : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2)) : complP S → ZMod 2 := fun p => A p.1.1 p.1.2

/-- `A` is recovered from `symM A S` and its complement: `Aᵢⱼ = symMᵢⱼ + Aⱼᵢ` on the block. -/
theorem symM_restA_injective (S : Finset (Fin (2 * h))) :
    Function.Injective (fun A : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2) => (symM A S, restA S A)) := by
  intro A A' hAA
  rw [Prod.mk.injEq] at hAA
  obtain ⟨hs, hr⟩ := hAA
  ext i j
  by_cases hij : i ∈ S ∧ j ∈ Sᶜ
  · obtain ⟨hi, hj⟩ := hij
    have hsij : symM A S i j = symM A' S i j := congrFun (congrFun hs i) j
    simp only [symM, Matrix.of_apply] at hsij
    rw [if_pos ⟨hi, hj⟩, if_pos ⟨hi, hj⟩] at hsij
    have hji : ¬ (j ∈ S ∧ i ∈ Sᶜ) := fun hh => (Finset.mem_compl.mp hj) hh.1
    have hrji := congrFun hr (⟨(j, i), hji⟩ : complP S)
    simp only [restA] at hrji
    rw [hrji] at hsij
    exact add_right_cancel hsij
  · have hrij := congrFun hr (⟨(i, j), hij⟩ : complP S)
    simpa only [restA] using hrij

theorem card_complP (S : Finset (Fin (2 * h))) (hS : S.card = h) :
    Fintype.card (complP S) = (2 * h) * (2 * h) - h * h := by
  have hSc : Sᶜ.card = h := by rw [Finset.card_compl, Fintype.card_fin, hS]; omega
  have hP : Fintype.card {p : Fin (2 * h) × Fin (2 * h) // p.1 ∈ S ∧ p.2 ∈ Sᶜ} = h * h := by
    rw [Fintype.card_subtype]
    have hpe : (Finset.univ.filter (fun p : Fin (2 * h) × Fin (2 * h) => p.1 ∈ S ∧ p.2 ∈ Sᶜ))
        = S ×ˢ Sᶜ := by ext p; simp [Finset.mem_product]
    rw [hpe, Finset.card_product, hS, hSc]
  unfold complP
  rw [Fintype.card_subtype_compl, hP, Fintype.card_prod, Fintype.card_fin]

/-- Fiber bound for the symmetrized block. -/
theorem symM_fiber_bound (S : Finset (Fin (2 * h))) :
    (Finset.univ.filter
        (fun A : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2) => (symM A S).rank < r)).card
      ≤ 2 ^ (2 * (2 * h) * r) * 2 ^ Fintype.card (complP S) := by
  classical
  calc (Finset.univ.filter
          (fun A : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2) => (symM A S).rank < r)).card
      ≤ ((Finset.univ.filter (fun M : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2) => M.rank < r)) ×ˢ
          (Finset.univ : Finset (complP S → ZMod 2))).card := by
        apply Finset.card_le_card_of_injOn (fun A => (symM A S, restA S A))
        · intro A hA
          rw [Finset.mem_coe, Finset.mem_filter] at hA
          rw [Finset.mem_coe, Finset.mem_product]
          exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA.2⟩, Finset.mem_univ _⟩
        · exact (symM_restA_injective S).injOn
    _ = (Finset.univ.filter (fun M : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2) => M.rank < r)).card
          * Fintype.card (complP S → ZMod 2) := by rw [Finset.card_product, Finset.card_univ]
    _ ≤ 2 ^ (2 * (2 * h) * r) * 2 ^ Fintype.card (complP S) := by
        apply Nat.mul_le_mul
        · calc (Finset.univ.filter (fun M : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2) => M.rank < r)).card
              ≤ (Finset.univ.filter
                  (fun M : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2) => M.rank ≤ r)).card := by
                apply Finset.card_le_card
                intro M hM
                rw [Finset.mem_filter] at hM ⊢
                exact ⟨hM.1, le_of_lt hM.2⟩
            _ ≤ 2 ^ (2 * (2 * h) * r) := card_lowRank_le (2 * h) r
        · exact le_of_eq (by rw [Fintype.card_fun, ZMod.card 2])

/-- **Piece (2).**  For `4r + 2 < h`, a matrix `A` has `rank(symM A S) ≥ r` at every balanced cut. -/
theorem exists_symM_rank_ge (hh : 4 * r + 2 < h) :
    ∃ A : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2),
      ∀ S : Finset (Fin (2 * h)), S.card = h → r ≤ (symM A S).rank := by
  classical
  set T := Finset.univ.filter (fun S : Finset (Fin (2 * h)) => S.card = h) with hTdef
  set Bad := fun S => Finset.univ.filter
    (fun A : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2) => (symM A S).rank < r) with hBaddef
  have hΩ : Fintype.card (Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2)) = 2 ^ ((2 * h) * (2 * h)) := by
    rw [Fintype.card_congr (Matrix.of (m := Fin (2 * h)) (n := Fin (2 * h)) (α := ZMod 2)).symm,
      Fintype.card_fun, Fintype.card_fun, ZMod.card 2, Fintype.card_fin, ← pow_mul]
  have hlt : ∑ S ∈ T, (Bad S).card < Fintype.card (Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2)) := by
    calc ∑ S ∈ T, (Bad S).card
        ≤ ∑ _S ∈ T, 2 ^ (2 * (2 * h) * r) * 2 ^ ((2 * h) * (2 * h) - h * h) := by
          apply Finset.sum_le_sum
          intro S hST
          have hSc : S.card = h := (Finset.mem_filter.mp hST).2
          calc (Bad S).card ≤ 2 ^ (2 * (2 * h) * r) * 2 ^ Fintype.card (complP S) := symM_fiber_bound S
            _ = 2 ^ (2 * (2 * h) * r) * 2 ^ ((2 * h) * (2 * h) - h * h) := by rw [card_complP S hSc]
      _ = T.card * (2 ^ (2 * (2 * h) * r) * 2 ^ ((2 * h) * (2 * h) - h * h)) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 2 ^ (2 * h) * (2 ^ (2 * (2 * h) * r) * 2 ^ ((2 * h) * (2 * h) - h * h)) := by
          apply Nat.mul_le_mul_right
          calc T.card ≤ Fintype.card (Finset (Fin (2 * h))) := Finset.card_le_univ T
            _ = 2 ^ (2 * h) := by rw [Fintype.card_finset, Fintype.card_fin]
      _ < Fintype.card (Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2)) := by
          rw [hΩ, ← pow_add, ← pow_add]
          apply Nat.pow_lt_pow_right (by norm_num)
          have h0 : 0 < h := by omega
          have hN2 : (2 * h) * (2 * h) = 4 * (h * h) := by ring
          have hkey : 2 * (2 * h) * r + 2 * h < h * h := by nlinarith [hh, h0]
          omega
  obtain ⟨A, hA⟩ := exists_avoiding T Bad hlt
  refine ⟨A, fun S hS => ?_⟩
  have hST : S ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩
  have hnot := hA S hST
  simp only [hBaddef, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnot
  exact hnot

/-- **The global best-partition bond exists.**  For `4r + 2 < h`, there is a single function `f = QF A` on `2h`
variables whose residual-span dimension across **every** balanced partition is `≥ 2^r = 2^{Ω(n)}`. -/
theorem exists_global_best_partition_bond (hh : 4 * r + 2 < h) :
    ∃ A : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2),
      ∀ S : Finset (Fin (2 * h)), S.card = h →
        2 ^ r ≤ Module.finrank K
          (Submodule.span K (Set.range (residualOf S (QF (K := K) A)))) := by
  obtain ⟨A, hA⟩ := exists_symM_rank_ge hh
  refine ⟨A, fun S hS => ?_⟩
  calc 2 ^ r ≤ 2 ^ (symM A S).rank := Nat.pow_le_pow_right (by norm_num) (hA S hS)
    _ = (indexImage A S).card := (indexImage_card A S).symm
    _ ≤ Module.finrank K (Submodule.span K (Set.range (residualOf S (QF (K := K) A)))) :=
        residual_finrank_ge A S

/-! ## Step (1): the symmetric all-cut matrix, stated directly -/

/-- `B` masked to the cross block `S × Sᶜ`. -/
def crossBlock (B : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2)) (S : Finset (Fin (2 * h))) :
    Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2) :=
  Matrix.of (fun i j => if i ∈ S ∧ j ∈ Sᶜ then B i j else 0)

/-- **A symmetric, zero-diagonal `𝔽₂` matrix `B` whose every balanced cross block has rank `≥ r`.**  Stated
directly as the symmetric all-cut matrix (`B = A + Aᵀ` for the `A` of `exists_symM_rank_ge`). -/
theorem exists_symmetric_all_cut (hh : 4 * r + 2 < h) :
    ∃ B : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2),
      Bᵀ = B ∧ (∀ i, B i i = 0) ∧
        ∀ S : Finset (Fin (2 * h)), S.card = h → r ≤ (crossBlock B S).rank := by
  obtain ⟨A, hA⟩ := exists_symM_rank_ge hh
  refine ⟨A + Aᵀ, ?_, ?_, ?_⟩
  · rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  · intro i
    simp only [Matrix.add_apply, Matrix.transpose_apply]
    exact CharTwo.add_self_eq_zero _
  · intro S hS
    have hcb : crossBlock (A + Aᵀ) S = symM A S := by
      unfold crossBlock symM
      ext i j
      simp only [Matrix.of_apply, Matrix.add_apply, Matrix.transpose_apply]
    rw [hcb]
    exact hA S hS

end PallLean.Paper93.DeepMath.PathB.GlobalBestPartitionBond

#print axioms PallLean.Paper93.DeepMath.PathB.GlobalBestPartitionBond.exists_symM_rank_ge
#print axioms PallLean.Paper93.DeepMath.PathB.GlobalBestPartitionBond.exists_global_best_partition_bond
