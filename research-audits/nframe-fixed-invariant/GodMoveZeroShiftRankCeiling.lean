import GodMoveUnitCharacteristic

/-!
# The easy product saturates the universal zero-shift rank ceiling

At strict derivative order `k` and zero shift, every projected SPDP row is a
scalar multiple of a derivative indexed by a `k`-subset. Admissibility forbids
repeated variables, and commutativity removes ordering. Thus every polynomial,
with every block partition, has rank at most `choose n k` at these parameters.
No multilinearity hypothesis on the polynomial is required.

The existing full-product identity minor attains this universal ceiling for
discrete blocks. In particular the easy unit-CNF characteristic already has
the largest possible rank. Dividing this rank by that easy-product baseline
leaves a value at most one for every target. Such a baseline normalization
therefore removes the proposed superpolynomial lower bound as well as the
easy-family counterexample. This concerns the stated strict zero-shift rank,
not every invariant or other choices of derivative/shift parameters.
-/

namespace GodMoveZeroShiftRankCeiling

open MvPolynomial SPDP MultilinearSPDP
open GodMoveMonomialMinor (Poly KSubset kSubset_card fullMonomial discreteBlocks)
open GodMoveUnitCharacteristic GodMoveFaithfulHandshake

noncomputable def subsetRows {n : ℕ} (k : ℕ) (p : Poly n) :
    KSubset n k → Poly n :=
  fun S => mlProj (iterDerivList S.val.toList p)

noncomputable def subsetSpan {n : ℕ} (k : ℕ) (p : Poly n) : Submodule ℚ (Poly n) :=
  Submodule.span ℚ (Set.range (subsetRows k p))

/-- A degree-zero shift is a scalar, and each admissible derivative list can
be replaced by the canonical ordering of its subset. -/
theorem zeroShift_subspace_le_subsetSpan {n : ℕ}
    (B : BlockPartition n) (k : ℕ) (p : Poly n) :
    mlBlockedSpdpSubspace B k 0 p ≤ subsetSpan k p := by
  classical
  apply Submodule.span_le.mpr
  rintro q ⟨S, m, hlen, hdeg, _, hadm, rfl⟩
  have hcard : S.toFinset.card = k := by
    rw [List.toFinset_card_of_nodup hadm.1, hlen]
  let I : KSubset n k := ⟨S.toFinset, Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ _, hcard⟩⟩
  have hderiv : iterDerivList S p = iterDerivList I.val.toList p :=
    IterDerivHelpers.iterDerivList_perm (List.toFinset_toList hadm.1).symm p
  have hm : m = C (m.coeff 0) :=
    totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hdeg)
  rw [hm, ← smul_eq_C_mul, mlProj_smul, hderiv]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨I, rfl⟩)

/-- There is at most one generator per `k`-subset. -/
theorem subsetSpan_finrank_le_choose {n : ℕ} (k : ℕ) (p : Poly n) :
    Module.finrank ℚ (subsetSpan k p) ≤ Nat.choose n k := by
  classical
  simpa only [subsetSpan, kSubset_card] using
    (finrank_range_le_card (R := ℚ) (subsetRows k p))

/-- The universal ceiling for this concrete strict zero-shift rank. -/
theorem zeroShift_rank_le_choose {n : ℕ}
    (B : BlockPartition n) (k : ℕ) (p : Poly n) :
    mlBlockedSpdpRank B k 0 p ≤ Nat.choose n k := by
  classical
  letI : Module.Finite ℚ (subsetSpan k p) :=
    Module.Finite.span_of_finite ℚ (Set.finite_range (subsetRows k p))
  exact (Submodule.finrank_mono (zeroShift_subspace_le_subsetSpan B k p)).trans
    (subsetSpan_finrank_le_choose k p)

/-- The easy product reaches the universal ceiling exactly. -/
theorem fullMonomial_zeroShift_rank (n k : ℕ) :
    mlBlockedSpdpRank (discreteBlocks n) k 0 (fullMonomial n) = Nat.choose n k :=
  Nat.le_antisymm (zeroShift_rank_le_choose _ _ _)
    (GodMoveMonomialMinor.choose_le_strict_rank n k 0)

theorem unitFormula_zeroShift_rank (n k : ℕ) :
    mlBlockedSpdpRank (discreteBlocks n) k 0
      (verifierCharacteristic n (unitFormula n)) = Nat.choose n k := by
  rw [unitFormula_characteristic]
  exact fullMonomial_zeroShift_rank n k

/-- Every polynomial is bounded by the rank of this easy family at the same
variable count and derivative order (the easy family uses discrete blocks). -/
theorem zeroShift_rank_le_unitFormula {n : ℕ}
    (B : BlockPartition n) (k : ℕ) (p : Poly n) :
    mlBlockedSpdpRank B k 0 p ≤
      mlBlockedSpdpRank (discreteBlocks n) k 0
        (verifierCharacteristic n (unitFormula n)) := by
  rw [unitFormula_zeroShift_rank]
  exact zeroShift_rank_le_choose B k p

/-- Dividing by the easy-product baseline bounds every target by one.
When `k > n`, both ranks are zero; rational division uses `0 / 0 = 0`. -/
theorem baseline_ratio_le_one {n : ℕ}
    (B : BlockPartition n) (k : ℕ) (p : Poly n) :
    (mlBlockedSpdpRank B k 0 p : ℚ) / (Nat.choose n k : ℚ) ≤ 1 := by
  by_cases hz : Nat.choose n k = 0
  · simp [hz]
  · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hz)).mpr
    exact_mod_cast zeroShift_rank_le_choose B k p

end GodMoveZeroShiftRankCeiling

#print axioms GodMoveZeroShiftRankCeiling.zeroShift_subspace_le_subsetSpan
#print axioms GodMoveZeroShiftRankCeiling.subsetSpan_finrank_le_choose
#print axioms GodMoveZeroShiftRankCeiling.zeroShift_rank_le_choose
#print axioms GodMoveZeroShiftRankCeiling.fullMonomial_zeroShift_rank
#print axioms GodMoveZeroShiftRankCeiling.unitFormula_zeroShift_rank
#print axioms GodMoveZeroShiftRankCeiling.zeroShift_rank_le_unitFormula
#print axioms GodMoveZeroShiftRankCeiling.baseline_ratio_le_one
