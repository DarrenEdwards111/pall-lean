import GodMoveCircuitNormalization

/-!
# Boolean normalization of the actual designated strict God-Move sheet

The production `Step252.cookLevinStrictFOBTarget` is the object wrapped by
`routeBPaperFaithfulTPhiTarget` in `RouteBPaperFaithfulTPhiExtraction.lean`.
It restricts the actual compiled product to variables `3*i`, killing all
adjacency and transition-skeleton constraints. The remaining booleanity
factors evaluate to one on every Boolean assignment.

We prove this directly for that production target, then prove that Boolean
normalization yields the constant polynomial one. Consequently the positive
strict-derivative rank of the designated sheet cannot be retained by merely
identifying it with its Boolean characteristic. This concerns this specific
normalization step, not all possible God-Move constructions.
-/

namespace GodMoveDesignatedSheetNormalization

set_option exponentiation.threshold 1000

open MvPolynomial MultilinearSPDP PaperFaithfulSeparation
open GodMoveBooleanInterpolation GodMoveCircuitNormalization
open Step4Compiler.Step252
open scoped BigOperators

/-- Evaluate the flat first-of-block restriction of an ambient polynomial. -/
noncomputable def sparseEvaluation (n : ℕ) (a : Assignment (n / 3)) :
    Poly n →+* ℚ :=
  (eval (booleanPoint a)).comp
    (restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n)).toRingHom

theorem sparseEvaluation_X (n : ℕ) (a : Assignment (n / 3)) (i : Fin n) :
    sparseEvaluation n a (X i) =
      if h : ∃ j, cookLevinStrictFOBFlatMap n j = i then bit (a h.choose) else 0 := by
  classical
  simp only [sparseEvaluation, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, restrictPoly_X]
  split_ifs <;> simp [booleanPoint]

theorem sparseEvaluation_X_boolean (n : ℕ) (a : Assignment (n / 3)) (i : Fin n) :
    sparseEvaluation n a (X i) = 0 ∨ sparseEvaluation n a (X i) = 1 := by
  classical
  rw [sparseEvaluation_X]
  split_ifs with h
  · cases a h.choose <;> simp [bit]
  · exact Or.inl rfl

/-- Two adjacent coordinates cannot both survive the strict first-of-block map. -/
theorem sparseEvaluation_adjacent_zero (n : ℕ) (a : Assignment (n / 3))
    (i : Fin n) (hi : i.val + 1 < n) :
    sparseEvaluation n a (X i * X ⟨i.val + 1, hi⟩) = 0 := by
  classical
  rw [map_mul, sparseEvaluation_X, sparseEvaluation_X]
  by_cases h : ∃ j, cookLevinStrictFOBFlatMap n j = i
  · have hnext : ¬ ∃ j, cookLevinStrictFOBFlatMap n j = ⟨i.val + 1, hi⟩ := by
      rintro ⟨j, hj⟩
      obtain ⟨k, hk⟩ := h
      have hjval := congrArg Fin.val hj
      have hkval := congrArg Fin.val hk
      simp only [cookLevinStrictFOBFlatMap] at hjval hkval
      omega
    simp [hnext]
  · simp [h]

theorem sparseEvaluation_bool_constraint_zero (n : ℕ) (a : Assignment (n / 3))
    (lc : LocalConstraint n) (hlc : lc ∈ boolConstraintList n) :
    sparseEvaluation n a lc.poly = 0 := by
  classical
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hlc
  change sparseEvaluation n a (X i * (1 - X i)) = 0
  rw [map_mul, map_sub, map_one]
  rcases sparseEvaluation_X_boolean n a i with h | h <;> simp [h]

theorem sparseEvaluation_rest_constraint_zero
    (M : TuringMachine.DTM) (n : ℕ) (a : Assignment (n / 3))
    (lc : LocalConstraint n)
    (hlc : lc ∈ adjConstraintList n ++ transSkelConstraintList M n) :
    sparseEvaluation n a lc.poly = 0 := by
  obtain ⟨c, i, hi, hpoly⟩ := rest_constraint_cadj_form M n lc hlc
  rw [hpoly, map_mul, sparseEvaluation_adjacent_zero n a i hi, mul_zero]

/-- Every actual local constraint of this compiler vanishes on the sparse
Boolean face, for every transition table. -/
theorem sparseEvaluation_compiled_constraint_zero
    (M : TuringMachine.DTM) (n : ℕ) (hn2 : 2 ≤ n)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (a : Assignment (n / 3)) (lc : LocalConstraint n)
    (hlc : lc ∈ (cook_levin_compilation M n hn2 htb hns).constraints) :
    sparseEvaluation n a lc.poly = 0 := by
  change lc ∈ (boolConstraintList n ++ adjConstraintList n) ++
    transSkelConstraintList M n at hlc
  rw [List.append_assoc, List.mem_append] at hlc
  rcases hlc with h | h
  · exact sparseEvaluation_bool_constraint_zero n a lc h
  · exact sparseEvaluation_rest_constraint_zero M n a lc h

theorem flat_restriction_boolean_eval_one
    (M : TuringMachine.DTM) (n : ℕ) (hn2 : 2 ≤ n)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (a : Assignment (n / 3)) :
    eval (booleanPoint a)
      (restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns))) = 1 := by
  change sparseEvaluation n a
    (compiledPoly (cook_levin_compilation M n hn2 htb hns)) = 1
  change sparseEvaluation n a
    (((boolConstraintList n ++ adjConstraintList n) ++ transSkelConstraintList M n).map
      (fun lc : LocalConstraint n => (1 : GodMoveBooleanInterpolation.Poly n) - lc.poly)).prod = 1
  rw [map_list_prod, List.map_map]
  apply List.prod_eq_one
  intro x hx
  obtain ⟨lc, hlc, rfl⟩ := List.mem_map.mp hx
  change sparseEvaluation n a (1 - lc.poly) = 1
  rw [map_sub, map_one,
    sparseEvaluation_compiled_constraint_zero M n hn2 htb hns a lc hlc, sub_zero]

/-- Exact Boolean semantics of the production designated coupled sheet. -/
theorem designated_sheet_boolean_eval_one
    (M : TuringMachine.DTM) (n : ℕ) (hn2 : 2 ≤ n)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B : SPDP.BlockPartition (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (a : Assignment (n / 3)) :
    eval (booleanPoint a) (cookLevinStrictFOBTarget M n hn2 htb hns B).coupledPoly = 1 := by
  change eval (booleanPoint a)
    (restrictPoly ℚ (cookLevinStrictFOBMap M n) (cookLevinStrictFOBMap_injective M n)
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).embedded_Q) = 1
  rw [cookLevinStrictFOB_restrict_embedded_Q_eq_restrict_compiledPoly]
  exact flat_restriction_boolean_eval_one M n hn2 htb hns a

/-- The Boolean normalizer used for actual-machine characteristic semantics
collapses this designated sheet to one. -/
theorem designated_sheet_normalize_eq_one
    (M : TuringMachine.DTM) (n : ℕ) (hn2 : 2 ≤ n)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B : SPDP.BlockPartition (PaperFaithfulCompilation.cookLevinUVSplit M n).total) :
    normalize (cookLevinStrictFOBTarget M n hn2 htb hns B).coupledPoly = 1 := by
  apply multilinear_eq_of_boolean_eval _ _ (normalize_isMultilinear _) ?_ ?_
  · intro a ha i
    have hzero : a = 0 := by simpa [coeff_one, eq_comm] using ha
    simp [hzero]
  · intro a
    rw [eval_normalize]
    simpa only [map_one] using designated_sheet_boolean_eval_one M n hn2 htb hns B a

/-- At every positive derivative order, the normalized designated sheet has
strict SPDP rank zero, for any partition and shift allowance. -/
theorem designated_sheet_normalized_rank_zero
    (M : TuringMachine.DTM) (n : ℕ) (hn2 : 2 ≤ n)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B : SPDP.BlockPartition (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (D : SPDP.BlockPartition (n / 3)) (kappa ell : ℕ) (hk : 0 < kappa) :
    mlBlockedSpdpRank D kappa ell
      (normalize (cookLevinStrictFOBTarget M n hn2 htb hns B).coupledPoly) = 0 := by
  rw [designated_sheet_normalize_eq_one]
  have h := mlBlockedSpdpRank_add_lowDeg ℚ D kappa ell
    (0 : GodMoveBooleanInterpolation.Poly (n / 3)) 1
    (by simpa using hk)
  simpa [mlBlockedSpdpRank_zero] using h

/-- The same designated sheet, before Boolean normalization, has the
production identity-minor lower bound strictly above the paper's `n^200`
budget. This theorem has no SAT-decider assumption. -/
theorem designated_sheet_rank_gt_npow200
    (M : TuringMachine.DTM) (n : ℕ) (hn : 2 ^ 804 ≤ n) (hn2 : 2 ≤ n)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B : SPDP.BlockPartition (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB : B = PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) :
    n ^ 200 < mlBlockedSpdpRank
      (cookLevinStrictFOBTarget M n hn2 htb hns B).coupledPartition
      (Nat.log 2 n) (Nat.log 2 n)
      (cookLevinStrictFOBTarget M n hn2 htb hns B).coupledPoly := by
  have hminor := cookLevinStrictFOBTarget_same_target_lower M n hn hn2 htb hns B hB
  have hn20 : 2 ^ 20 ≤ n :=
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 20 ≤ 804)).trans hn
  have hlog : 804 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by decide : 1 < 2) hn
  calc
    n ^ 200 < n ^ (Nat.log 2 n / 4) :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    _ ≤ Nat.choose (n / 30) (Nat.log 2 n) :=
      BinomialBound.binomial_lower_bound_concrete n hn20
    _ ≤ Nat.choose (n / 3) (Nat.log 2 n) := Nat.choose_mono _ (by omega)
    _ ≤ _ := hminor

/-- At the very window carrying the designated identity minor, Boolean
normalization changes its superpolynomial rank to zero. -/
theorem designated_sheet_normalization_loses_rank
    (M : TuringMachine.DTM) (n : ℕ) (hn : 2 ^ 804 ≤ n) (hn2 : 2 ≤ n)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B : SPDP.BlockPartition (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB : B = PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) :
    mlBlockedSpdpRank
        (cookLevinStrictFOBTarget M n hn2 htb hns B).coupledPartition
        (Nat.log 2 n) (Nat.log 2 n)
        (normalize (cookLevinStrictFOBTarget M n hn2 htb hns B).coupledPoly) = 0 ∧
      n ^ 200 < mlBlockedSpdpRank
        (cookLevinStrictFOBTarget M n hn2 htb hns B).coupledPartition
        (Nat.log 2 n) (Nat.log 2 n)
        (cookLevinStrictFOBTarget M n hn2 htb hns B).coupledPoly := by
  have hlog : 804 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by decide : 1 < 2) hn
  exact ⟨designated_sheet_normalized_rank_zero M n hn2 htb hns B _ _ _ (by omega),
    designated_sheet_rank_gt_npow200 M n hn hn2 htb hns B hB⟩

/-- No multilinear characteristic polynomial can equal this unnormalized
designated hard sheet at paper scale. -/
theorem multilinear_polynomial_ne_designated_sheet
    (M : TuringMachine.DTM) (n : ℕ) (hn : 2 ^ 804 ≤ n) (hn2 : 2 ≤ n)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B : SPDP.BlockPartition (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB : B = PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)
    (p : GodMoveBooleanInterpolation.Poly (n / 3)) (hp : IsMultilinear p) :
    p ≠ (cookLevinStrictFOBTarget M n hn2 htb hns B).coupledPoly := by
  intro heq
  have hpone : p = 1 := by
    apply multilinear_eq_of_boolean_eval _ _ hp ?_ ?_
    · intro a ha i
      have hzero : a = 0 := by simpa [coeff_one, eq_comm] using ha
      simp [hzero]
    · intro a
      rw [heq]
      simpa only [map_one] using designated_sheet_boolean_eval_one M n hn2 htb hns B a
  have htarget : (cookLevinStrictFOBTarget M n hn2 htb hns B).coupledPoly = 1 :=
    heq.symm.trans hpone
  have hnorm := designated_sheet_normalization_loses_rank M n hn hn2 htb hns B hB
  have hequal : normalize (cookLevinStrictFOBTarget M n hn2 htb hns B).coupledPoly =
      (cookLevinStrictFOBTarget M n hn2 htb hns B).coupledPoly := by
    rw [designated_sheet_normalize_eq_one, htarget]
  rw [hequal] at hnorm
  omega

end GodMoveDesignatedSheetNormalization

#print axioms GodMoveDesignatedSheetNormalization.sparseEvaluation_adjacent_zero
#print axioms GodMoveDesignatedSheetNormalization.sparseEvaluation_compiled_constraint_zero
#print axioms GodMoveDesignatedSheetNormalization.designated_sheet_boolean_eval_one
#print axioms GodMoveDesignatedSheetNormalization.designated_sheet_normalize_eq_one
#print axioms GodMoveDesignatedSheetNormalization.designated_sheet_normalized_rank_zero
#print axioms GodMoveDesignatedSheetNormalization.designated_sheet_rank_gt_npow200
#print axioms GodMoveDesignatedSheetNormalization.designated_sheet_normalization_loses_rank
#print axioms GodMoveDesignatedSheetNormalization.multilinear_polynomial_ne_designated_sheet
