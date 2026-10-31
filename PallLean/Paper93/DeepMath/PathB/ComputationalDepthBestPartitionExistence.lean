import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLowRankCount

/-!
# A best-partition-hard matrix exists (probabilistic method)

The existence theorem the engine (`LowRankCount`) was built for.  On `n = 2h` variables, there is an `𝔽₂` matrix
`M` whose off-diagonal block at **every** balanced partition `(S, Sᶜ)` has rank `≥ r` (for `2r + 2 < h`), i.e.
`r ≈ n/4`.  Via the reduction (`BestPartitionReduction.chi_subset_finrank`), the associated quadratic form is
best-partition-hard: bond `≥ 2^r = 2^{Ω(n)}` across every ordering.

Counting: for a fixed partition, the bad set `{M : rank(block_S M) < r}` injects (via `M ↦ (block_S M, M|_complement)`)
into `{low-rank blocks} × {complement entries}`, so has size `≤ 2^{2hr} · 2^{n²−h²}`; the union over `≤ 2^n`
partitions is `< 2^{n²}` once `2r + 2 < h`, and `exists_avoiding` produces the rigid `M`.

`exists_best_partition_hard` — the existence theorem.

## Honest scope

A genuine best-partition-hard object, existentially (a random matrix works).  Not explicit — explicit rank-rigid
matrices are Valiant's open problem (`SCOPE_BEST_PARTITION_HARD.md`).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BestPartitionExistence

open Matrix PallLean.Paper93.DeepMath.PathB.LowRankCount

variable {h r : ℕ}

/-- The off-diagonal block of `M` at partition `(S, Sᶜ)` (rows `S`, columns `Sᶜ`), as an `h×h` matrix; `0` if `S`
is not balanced. -/
noncomputable def blk (S : Finset (Fin (2 * h))) (M : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2)) :
    Matrix (Fin h) (Fin h) (ZMod 2) :=
  if hS : S.card = h then
    M.submatrix (S.orderEmbOfFin hS)
      (Sᶜ.orderEmbOfFin (show Sᶜ.card = h by rw [Finset.card_compl, Fintype.card_fin, hS]; omega))
  else 0

/-- The entries of `M` outside the block index set `S × Sᶜ`. -/
def complS (S : Finset (Fin (2 * h))) : Type :=
  {p : Fin (2 * h) × Fin (2 * h) // ¬(p.1 ∈ S ∧ p.2 ∈ Sᶜ)}

noncomputable instance (S : Finset (Fin (2 * h))) : Fintype (complS S) := by
  unfold complS; infer_instance

/-- `M` restricted to the complement of the block. -/
noncomputable def restOf (S : Finset (Fin (2 * h))) (M : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2)) :
    complS S → ZMod 2 := fun p => M p.1.1 p.1.2

/-- `M` is determined by its block and its complement entries. -/
theorem blk_restOf_injective (S : Finset (Fin (2 * h))) (hS : S.card = h) :
    Function.Injective
      (fun M : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2) => (blk S M, restOf S M)) := by
  have hSc : Sᶜ.card = h := by rw [Finset.card_compl, Fintype.card_fin, hS]; omega
  intro M M' hMM
  rw [Prod.mk.injEq] at hMM
  obtain ⟨hb, hr⟩ := hMM
  ext i j
  by_cases hp : i ∈ S ∧ j ∈ Sᶜ
  · obtain ⟨hi, hj⟩ := hp
    have hiR : i ∈ Set.range (S.orderEmbOfFin hS) := by
      rw [Finset.range_orderEmbOfFin]; exact Finset.mem_coe.mpr hi
    have hjR : j ∈ Set.range (Sᶜ.orderEmbOfFin hSc) := by
      rw [Finset.range_orderEmbOfFin]; exact Finset.mem_coe.mpr hj
    obtain ⟨i', hi'⟩ := hiR
    obtain ⟨j', hj'⟩ := hjR
    have e1 : M i j = blk S M i' j' := by
      simp only [blk, dif_pos hS, Matrix.submatrix_apply, hi', hj']
    have e2 : M' i j = blk S M' i' j' := by
      simp only [blk, dif_pos hS, Matrix.submatrix_apply, hi', hj']
    rw [e1, e2, hb]
  · have hc := congrFun hr ⟨(i, j), hp⟩
    simpa [restOf] using hc

/-- **Fiber bound.**  For a balanced partition, at most `2^{2hr} · 2^{|complement|}` matrices have a low-rank
block. -/
theorem fiber_bound (S : Finset (Fin (2 * h))) (hS : S.card = h) :
    (Finset.univ.filter
        (fun M : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2) => (blk S M).rank < r)).card
      ≤ 2 ^ (2 * h * r) * 2 ^ Fintype.card (complS S) := by
  classical
  calc (Finset.univ.filter
          (fun M : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2) => (blk S M).rank < r)).card
      ≤ ((Finset.univ.filter (fun b : Matrix (Fin h) (Fin h) (ZMod 2) => b.rank < r)) ×ˢ
          (Finset.univ : Finset (complS S → ZMod 2))).card := by
        apply Finset.card_le_card_of_injOn (fun M => (blk S M, restOf S M))
        · intro M hM
          rw [Finset.mem_coe, Finset.mem_filter] at hM
          rw [Finset.mem_coe, Finset.mem_product]
          exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hM.2⟩, Finset.mem_univ _⟩
        · exact (blk_restOf_injective S hS).injOn
    _ = (Finset.univ.filter (fun b : Matrix (Fin h) (Fin h) (ZMod 2) => b.rank < r)).card
          * Fintype.card (complS S → ZMod 2) := by rw [Finset.card_product, Finset.card_univ]
    _ ≤ 2 ^ (2 * h * r) * 2 ^ Fintype.card (complS S) := by
        apply Nat.mul_le_mul
        · calc (Finset.univ.filter (fun b : Matrix (Fin h) (Fin h) (ZMod 2) => b.rank < r)).card
              ≤ (Finset.univ.filter (fun b : Matrix (Fin h) (Fin h) (ZMod 2) => b.rank ≤ r)).card := by
                apply Finset.card_le_card
                intro b hb
                rw [Finset.mem_filter] at hb ⊢
                exact ⟨hb.1, le_of_lt hb.2⟩
            _ ≤ 2 ^ (2 * h * r) := card_lowRank_le h r
        · exact le_of_eq (by rw [Fintype.card_fun, ZMod.card 2])

/-- The complement has exactly `n² − h²` entries. -/
theorem card_complS (S : Finset (Fin (2 * h))) (hS : S.card = h) :
    Fintype.card (complS S) = (2 * h) * (2 * h) - h * h := by
  have hSc : Sᶜ.card = h := by rw [Finset.card_compl, Fintype.card_fin, hS]; omega
  have hP : Fintype.card {p : Fin (2 * h) × Fin (2 * h) // p.1 ∈ S ∧ p.2 ∈ Sᶜ} = h * h := by
    rw [Fintype.card_subtype]
    have hpe : (Finset.univ.filter (fun p : Fin (2 * h) × Fin (2 * h) => p.1 ∈ S ∧ p.2 ∈ Sᶜ))
        = S ×ˢ Sᶜ := by ext p; simp [Finset.mem_product]
    rw [hpe, Finset.card_product, hS, hSc]
  unfold complS
  rw [Fintype.card_subtype_compl, hP, Fintype.card_prod, Fintype.card_fin]

/-- **A best-partition-hard matrix exists.**  For `2r + 2 < h`, some `𝔽₂` matrix on `2h` variables has, at every
balanced partition, off-diagonal block of rank `≥ r`. -/
theorem exists_best_partition_hard (hh : 2 * r + 2 < h) :
    ∃ M : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2),
      ∀ S : Finset (Fin (2 * h)), S.card = h → r ≤ (blk S M).rank := by
  classical
  set T := Finset.univ.filter (fun S : Finset (Fin (2 * h)) => S.card = h) with hTdef
  set Bad := fun S => Finset.univ.filter
    (fun M : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2) => (blk S M).rank < r) with hBaddef
  have hΩ : Fintype.card (Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2)) = 2 ^ ((2 * h) * (2 * h)) := by
    rw [Fintype.card_congr (Matrix.of (m := Fin (2 * h)) (n := Fin (2 * h)) (α := ZMod 2)).symm,
      Fintype.card_fun, Fintype.card_fun, ZMod.card 2, Fintype.card_fin, ← pow_mul]
  have hh0 : 0 < h := by omega
  have hkey : 2 * h * r + 2 * h < h * h := by nlinarith [hh, hh0]
  have hlt : ∑ S ∈ T, (Bad S).card < Fintype.card (Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2)) := by
    calc ∑ S ∈ T, (Bad S).card
        ≤ ∑ _S ∈ T, 2 ^ (2 * h * r) * 2 ^ ((2 * h) * (2 * h) - h * h) := by
          apply Finset.sum_le_sum
          intro S hST
          have hSc : S.card = h := (Finset.mem_filter.mp hST).2
          calc (Bad S).card ≤ 2 ^ (2 * h * r) * 2 ^ Fintype.card (complS S) := fiber_bound S hSc
            _ = 2 ^ (2 * h * r) * 2 ^ ((2 * h) * (2 * h) - h * h) := by rw [card_complS S hSc]
      _ = T.card * (2 ^ (2 * h * r) * 2 ^ ((2 * h) * (2 * h) - h * h)) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 2 ^ (2 * h) * (2 ^ (2 * h * r) * 2 ^ ((2 * h) * (2 * h) - h * h)) := by
          apply Nat.mul_le_mul_right
          calc T.card ≤ Fintype.card (Finset (Fin (2 * h))) := Finset.card_le_univ T
            _ = 2 ^ (2 * h) := by rw [Fintype.card_finset, Fintype.card_fin]
      _ < Fintype.card (Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2)) := by
          rw [hΩ, ← pow_add, ← pow_add]
          apply Nat.pow_lt_pow_right (by norm_num)
          have h1 : h * h ≤ (2 * h) * (2 * h) := by nlinarith
          omega
  obtain ⟨M, hM⟩ := exists_avoiding T Bad hlt
  refine ⟨M, fun S hS => ?_⟩
  have hST : S ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩
  have hnot := hM S hST
  simp only [hBaddef, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnot
  exact hnot

end PallLean.Paper93.DeepMath.PathB.BestPartitionExistence

#print axioms PallLean.Paper93.DeepMath.PathB.BestPartitionExistence.exists_best_partition_hard
