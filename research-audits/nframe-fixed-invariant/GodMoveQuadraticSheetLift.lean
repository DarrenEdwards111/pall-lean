import GodMoveDesignatedSheetNormalization
import GodMoveMonomialMinor
import GodMoveBooleanFace
import GodMoveFullShiftProductSpace

/-!
# A source-specific quadratic lift into the actual designated sheet

The concrete strict first-of-block target is exactly the product of the
production booleanity factors. Substituting those factors for the variables
in a full monomial recovers that target. The rank comparison established
below is specific to these source and target polynomials; the quadratic
substitution is not asserted to preserve SPDP rank on arbitrary inputs.

For `k ≤ n` and `k ≤ ell`, the actual target rows lie in the affine
complement of the full monomial's strict shifted-derivative space. This
proves rank transport with no loss in parameters, and for any target
partition. The full monomial itself has large rank at logarithmic derivative
order, so the extraction does not supply the missing polynomial P-side
upper bound or a SAT separation.
-/

namespace GodMoveQuadraticSheetLift

open MvPolynomial MultilinearSPDP PaperFaithfulSeparation
open GodMoveBooleanInterpolation GodMoveCircuitNormalization
open Step4Compiler.Step252 SymmetricPower
open scoped BigOperators

abbrev Poly (n : ℕ) := MvPolynomial (Fin n) ℚ

/-- Restriction along any injective coordinate map keeps exactly one
booleanity factor for each target coordinate. -/
theorem restrict_boolFactorFullProd {m n : ℕ}
    (f : Fin m → Fin n) (hf : Function.Injective f) :
    restrictPoly ℚ f hf (boolFactorFullProd n) = boolFactorFullProd m := by
  classical
  let R := restrictPoly ℚ f hf
  have hkept (j : Fin m) : R (X (f j)) = X j := by
    change restrictPoly ℚ f hf (X (f j)) = X j
    have hj : ∃ k, f k = f j := ⟨j, rfl⟩
    rw [restrictPoly_X, dif_pos hj]
    rw [hf hj.choose_spec]
  have hdropped (i : Fin n) (hi : i ∉ Finset.univ.image f) : R (boolFactor n i) = 1 := by
    have hnot : ¬ ∃ j, f j = i := by simpa using hi
    change restrictPoly ℚ f hf (1 - X i * (1 - X i)) = 1
    simp [restrictPoly_X, hnot]
  unfold boolFactorFullProd
  rw [map_prod]
  change (∏ i : Fin n, R (boolFactor n i)) = ∏ j : Fin m, boolFactor m j
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image f))
    (fun i _ hi => hdropped i hi)]
  rw [Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro j _
    simp only [boolFactor, map_sub, map_one, map_mul, hkept]
  · exact fun i _ j _ h => hf h

/-- Every adjacent monomial is killed by the actual first-of-block restriction. -/
theorem strictFOB_adjacent_zero (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    restrictPoly ℚ (cookLevinStrictFOBFlatMap n) (cookLevinStrictFOBFlatMap_injective n)
      (X i * X ⟨i.val + 1, hi⟩) = 0 := by
  classical
  rw [map_mul, restrictPoly_X, restrictPoly_X]
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

theorem strictFOB_restFactorProd_eq_one (M : TuringMachine.DTM) (n : ℕ) :
    restrictPoly ℚ (cookLevinStrictFOBFlatMap n) (cookLevinStrictFOBFlatMap_injective n)
      (restFactorProd' M n) = 1 := by
  classical
  unfold restFactorProd'
  rw [map_list_prod, List.map_map]
  apply List.prod_eq_one
  intro x hx
  obtain ⟨lc, hlc, rfl⟩ := List.mem_map.mp hx
  obtain ⟨c, i, hi, hpoly⟩ := rest_constraint_cadj_form M n lc hlc
  simp only [Function.comp_apply, hpoly, map_sub, map_one, map_mul]
  have hzero := strictFOB_adjacent_zero n i hi
  rw [map_mul] at hzero
  rw [hzero]
  simp

/-- The exact production strict first-of-block target, not a substitute
example, is the full booleanity-factor product on its retained variables. -/
theorem designated_sheet_eq_boolFactorFullProd
    (M : TuringMachine.DTM) (n : ℕ) (hn2 : 2 ≤ n)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B : SPDP.BlockPartition (PaperFaithfulCompilation.cookLevinUVSplit M n).total) :
    (cookLevinStrictFOBTarget M n hn2 htb hns B).coupledPoly =
      boolFactorFullProd (n / 3) := by
  change restrictPoly ℚ (cookLevinStrictFOBMap M n) (cookLevinStrictFOBMap_injective M n)
    (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).embedded_Q = _
  rw [cookLevinStrictFOB_restrict_embedded_Q_eq_restrict_compiledPoly,
    CompiledBoolFactorBridge.compiledPoly_eq_boolFactorFullProd_mul_rest,
    map_mul, strictFOB_restFactorProd_eq_one, mul_one, restrict_boolFactorFullProd]

/-- The concrete quadratic coordinate lift. -/
noncomputable def quadraticLift (n : ℕ) : Poly n →ₐ[ℚ] Poly n :=
  aeval (boolFactor n)

theorem quadraticLift_X (n : ℕ) (i : Fin n) :
    quadraticLift n (X i) = 1 - X i + X i ^ 2 := by
  simp only [quadraticLift, aeval_X, boolFactor]
  ring

theorem quadraticLift_fullMonomial (n : ℕ) :
    quadraticLift n (GodMoveMonomialMinor.fullMonomial n) = boolFactorFullProd n := by
  simp [quadraticLift, GodMoveMonomialMinor.fullMonomial, boolFactorFullProd]

/-- The designated sheet is recovered exactly by this explicit lift. -/
theorem quadraticLift_recovers_designated_sheet
    (M : TuringMachine.DTM) (n : ℕ) (hn2 : 2 ≤ n)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B : SPDP.BlockPartition (PaperFaithfulCompilation.cookLevinUVSplit M n).total) :
    quadraticLift (n / 3) (GodMoveMonomialMinor.fullMonomial (n / 3)) =
      (cookLevinStrictFOBTarget M n hn2 htb hns B).coupledPoly := by
  rw [quadraticLift_fullMonomial, designated_sheet_eq_boolFactorFullProd]

/-- An invertible affine change used to transport the two derivative spaces.
This is separate from the quadratic lift defining the extracted polynomial. -/
noncomputable def affineComplement (n : ℕ) : Poly n →ₐ[ℚ] Poly n :=
  aeval (fun i => 1 - X i)

theorem affineComplement_X (n : ℕ) (i : Fin n) :
    affineComplement n (X i) = 1 - X i := by simp [affineComplement]

theorem affineComplement_involutive (n : ℕ) (p : Poly n) :
    affineComplement n (affineComplement n p) = p := by
  have h : (affineComplement n).comp (affineComplement n) = AlgHom.id ℚ (Poly n) := by
    ext i
    simp [affineComplement, map_sub]
  exact congrArg (fun F : Poly n →ₐ[ℚ] Poly n => F p) h

theorem affineFactor_vars_subset {n : ℕ} (i : Fin n) :
    (1 - X i : Poly n).vars ⊆ {i} := by
  exact (MvPolynomial.vars_sub_subset (p := (1 : Poly n)) (q := X i)).trans (by simp)

theorem affineFactor_isMultilinear {n : ℕ} (i : Fin n) :
    IsMultilinear (1 - X i : Poly n) := by
  rw [← mlProj_boolFactor i]
  exact fun a ha => WithinProfileBound.mlProj_support_isMultilinear _ a ha

theorem affineProduct_isMultilinear {n : ℕ} (s : Finset (Fin n)) :
    IsMultilinear (∏ i ∈ s, (1 - X i : Poly n)) := by
  classical
  apply (GodMoveBooleanFace.mlProj_eq_self_iff _).mp
  rw [WithinProfileBound.mlProj_finset_prod_of_pairwise_disjoint_vars]
  · apply Finset.prod_congr rfl
    intro i _
    exact mlProj_of_isMultilinear _ (affineFactor_isMultilinear i)
  · intro i _ j _ hij
    exact Finset.disjoint_of_subset_left (affineFactor_vars_subset i)
      (Finset.disjoint_of_subset_right (affineFactor_vars_subset j) (by simp [hij]))

theorem affineComplement_monomial_multilinear {n : ℕ}
    (a : Fin n →₀ ℕ) (c : ℚ) (ha : Finsupp.IsMultilinear a) :
    affineComplement n (monomial a c) = c • ∏ i ∈ a.support, (1 - X i : Poly n) := by
  classical
  simp only [affineComplement, aeval_monomial]
  change C c * (∏ i ∈ a.support, (1 - X i : Poly n) ^ a i) = _
  have hprod : (∏ i ∈ a.support, (1 - X i : Poly n) ^ a i) =
      ∏ i ∈ a.support, (1 - X i : Poly n) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hai : a i = 1 := by
      have hne := Finsupp.mem_support_iff.mp hi
      have hle := ha i
      omega
    rw [hai, pow_one]
  rw [hprod, C_mul']

/-- Coordinate complementation preserves multilinearity. -/
theorem affineComplement_isMultilinear {n : ℕ} (p : Poly n) (hp : IsMultilinear p) :
    IsMultilinear (affineComplement n p) := by
  classical
  rw [← support_sum_monomial_coeff p, map_sum]
  intro b hb i
  obtain ⟨a, ha, hba⟩ := Finsupp.mem_support_finset_sum b hb
  rw [affineComplement_monomial_multilinear a (coeff a p) (hp a ha)] at hba
  exact affineProduct_isMultilinear a.support b (support_smul hba) i

theorem vars_product_subset {n : ℕ} (s : Finset (Fin n)) (f : Fin n → Poly n)
    (hf : ∀ i, (f i).vars ⊆ {i}) : (∏ i ∈ s, f i).vars ⊆ s := by
  classical
  intro i hi
  obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp (vars_prod f hi)
  have heq : i = j := Finset.mem_singleton.mp (hf j hij)
  simpa [heq] using hj

theorem derivativeFactor_vars_subset {n : ℕ} (i : Fin n) :
    (pderiv i (boolFactor n i)).vars ⊆ {i} := by
  rw [pderiv_boolFactor_self]
  refine (vars_add_subset _ _).trans ?_
  rw [vars_neg, vars_one, Finset.empty_union]
  rw [show (2 : Poly n) = C 2 by simp [map_ofNat]]
  simpa only [vars_C, vars_X, Finset.empty_union] using vars_mul (C (2 : ℚ) : Poly n) (X i)

/-- Projected rows factor into an active polynomial and one affine factor
for every undifferentiated coordinate. -/
theorem projected_row_factorization {n : ℕ} (S : Finset (Fin n))
    (shift : Poly n) (hshift : shift.vars ⊆ S) :
    mlProj (shift * boolFactorDerivProd S) =
      mlProj (shift * ∏ i ∈ S, pderiv i (boolFactor n i)) *
        ∏ i ∈ Finset.univ \ S, (1 - X i : Poly n) := by
  classical
  have hactive : (shift * ∏ i ∈ S, pderiv i (boolFactor n i)).vars ⊆ S :=
    (vars_mul _ _).trans
      (Finset.union_subset hshift (vars_product_subset S _ derivativeFactor_vars_subset))
  have houtside : (∏ i ∈ Finset.univ \ S, boolFactor n i).vars ⊆ Finset.univ \ S :=
    vars_product_subset _ _ (boolFactor_vars_subset n)
  unfold boolFactorDerivProd
  rw [← mul_assoc, WithinProfileBound.mlProj_mul_of_vars_disjoint]
  · rw [WithinProfileBound.mlProj_finset_prod_of_pairwise_disjoint_vars]
    · simp only [mlProj_boolFactor]
    · intro i _ j _ hij
      exact Finset.disjoint_of_subset_left (boolFactor_vars_subset n i)
        (Finset.disjoint_of_subset_right (boolFactor_vars_subset n j) (by simp [hij]))
  · exact Finset.disjoint_of_subset_left hactive
      (Finset.disjoint_of_subset_right houtside Finset.disjoint_sdiff)

theorem complemented_projected_row_factorization {n : ℕ} (S : Finset (Fin n))
    (shift : Poly n) (hshift : shift.vars ⊆ S) :
    affineComplement n (mlProj (shift * boolFactorDerivProd S)) =
      affineComplement n (mlProj (shift * ∏ i ∈ S, pderiv i (boolFactor n i))) *
        GodMoveMonomialMinor.derivativeRow S := by
  rw [projected_row_factorization S shift hshift, map_mul, map_prod,
    GodMoveMonomialMinor.derivativeRow_eq_complement_product]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp [map_sub, affineComplement_X]

/-- Every target derivative row has a preimage in the full monomial's
shifted-derivative space, under a fixed linear map independent of the row. -/
theorem boolFactor_subspace_le_complemented_fullMonomial {n : ℕ}
    (B : SPDP.BlockPartition n) (k ell : ℕ) (hk : k ≤ n) (hell : k ≤ ell) :
    mlBlockedSpdpSubspace B k ell (boolFactorFullProd n) ≤
      Submodule.map (affineComplement n).toLinearMap
        (mlBlockedSpdpSubspace (GodMoveMonomialMinor.discreteBlocks n) k ell
          (GodMoveMonomialMinor.fullMonomial n)) := by
  classical
  apply Submodule.span_le.mpr
  rintro q ⟨S, shift, hlen, _hdeg, hvars, hadm, rfl⟩
  have hcard : S.toFinset.card = k := by
    rw [List.toFinset_card_of_nodup hadm.1, hlen]
  have hderiv : SPDP.iterDerivList S (boolFactorFullProd n) =
      boolFactorDerivProd S.toFinset := by
    rw [boolFactorDerivProd_eq_iterDerivList]
    exact IterDerivHelpers.iterDerivList_perm (List.toFinset_toList hadm.1).symm _
  rw [hderiv]
  apply Submodule.mem_map.mpr
  refine ⟨affineComplement n (mlProj (shift * boolFactorDerivProd S.toFinset)), ?_, ?_⟩
  · rw [GodMoveFullShiftProductSpace.strict_spdp_eq_highDegreeSpace n k ell hk hell]
    have hmem := GodMoveFullShiftProductSpace.mlProj_mul_complement_mem k S.toFinset
      hcard.le (affineComplement n
        (mlProj (shift * ∏ i ∈ S.toFinset, pderiv i (boolFactor n i))))
    rw [← complemented_projected_row_factorization S.toFinset shift hvars] at hmem
    rwa [mlProj_of_isMultilinear _ (affineComplement_isMultilinear _
      (fun a ha => WithinProfileBound.mlProj_support_isMultilinear _ a ha))] at hmem
  · exact affineComplement_involutive n _

/-- Source-specific rank transport into the quadratic product, at unchanged
derivative and shift parameters. It holds for any target partition. -/
theorem boolFactorFullProd_rank_le_fullMonomial_any_partition {n : ℕ}
    (B : SPDP.BlockPartition n) (k ell : ℕ) (hk : k ≤ n) (hell : k ≤ ell) :
    mlBlockedSpdpRank B k ell (boolFactorFullProd n) ≤
      mlBlockedSpdpRank (GodMoveMonomialMinor.discreteBlocks n) k ell
        (GodMoveMonomialMinor.fullMonomial n) := by
  exact (Submodule.finrank_mono
    (boolFactor_subspace_le_complemented_fullMonomial B k ell hk hell)).trans
    (Submodule.finrank_map_le _ _)

theorem boolFactorFullProd_rank_le_fullMonomial (n k ell : ℕ)
    (hk : k ≤ n) (hell : k ≤ ell) :
    mlBlockedSpdpRank (GodMoveMonomialMinor.discreteBlocks n) k ell (boolFactorFullProd n) ≤
      mlBlockedSpdpRank (GodMoveMonomialMinor.discreteBlocks n) k ell
        (GodMoveMonomialMinor.fullMonomial n) :=
  boolFactorFullProd_rank_le_fullMonomial_any_partition _ k ell hk hell

/-- The actual designated sheet inherits this unchanged-parameter rank
comparison, with its actual coupled partition. -/
theorem designated_sheet_rank_le_fullMonomial
    (M : TuringMachine.DTM) (n : ℕ) (hn2 : 2 ≤ n)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B : SPDP.BlockPartition (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (k ell : ℕ) (hk : k ≤ n / 3) (hell : k ≤ ell) :
    mlBlockedSpdpRank (cookLevinStrictFOBTarget M n hn2 htb hns B).coupledPartition
        k ell (cookLevinStrictFOBTarget M n hn2 htb hns B).coupledPoly ≤
      mlBlockedSpdpRank (GodMoveMonomialMinor.discreteBlocks (n / 3)) k ell
        (GodMoveMonomialMinor.fullMonomial (n / 3)) := by
  rw [designated_sheet_eq_boolFactorFullProd]
  exact boolFactorFullProd_rank_le_fullMonomial_any_partition _ k ell hk hell

end GodMoveQuadraticSheetLift

#print axioms GodMoveQuadraticSheetLift.restrict_boolFactorFullProd
#print axioms GodMoveQuadraticSheetLift.designated_sheet_eq_boolFactorFullProd
#print axioms GodMoveQuadraticSheetLift.quadraticLift_recovers_designated_sheet
#print axioms GodMoveQuadraticSheetLift.affineComplement_isMultilinear
#print axioms GodMoveQuadraticSheetLift.projected_row_factorization
#print axioms GodMoveQuadraticSheetLift.boolFactor_subspace_le_complemented_fullMonomial
#print axioms GodMoveQuadraticSheetLift.boolFactorFullProd_rank_le_fullMonomial_any_partition
#print axioms GodMoveQuadraticSheetLift.designated_sheet_rank_le_fullMonomial
