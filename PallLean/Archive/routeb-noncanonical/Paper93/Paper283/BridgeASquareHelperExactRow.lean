import PallLean.Paper93.Paper283.BridgeASquareHelperUpper

/-!
# Exact-row upper containment for the Bridge A square-helper candidate

This file handles the complementary strict-row case to
`BridgeASquareHelperUpper`: the derivative list has length `kappa`, is
admissible for the discrete partition, and contains all helpers of one row.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open SPDP

namespace BridgeAGeneralizedNonzeroWitness

attribute [local instance] Classical.dec

/-- Differentiating `X_i^2` by `i` gives `2 X_i`. -/
theorem pderiv_X_mul_X_self {n : Nat} (i : Fin n) :
    pderiv i ((X i * X i : MvPolynomial (Fin n) Rat)) =
      (2 : Rat) • X i := by
  rw [pderiv_mul, MvPolynomial.pderiv_X_self]
  simp [two_smul]

/-- Differentiating a product of squared variables in all variables of the
indexing finset leaves the linear product, with coefficient `2^|T|`. -/
theorem iterDerivList_toList_prod_X_sq {n : Nat}
    (T : Finset (Fin n)) :
    iterDerivList T.toList
        (T.prod (fun i => (X i * X i : MvPolynomial (Fin n) Rat))) =
      (2 : Rat) ^ T.card • T.prod (fun i => (X i : MvPolynomial (Fin n) Rat)) := by
  classical
  refine Finset.induction_on T ?_ ?_
  · simp [IterDerivHelpers.iterDerivList_nil]
  · intro a T ha ih
    have hperm : (insert a T).toList.Perm (a :: T.toList) :=
      Finset.toList_insert ha
    rw [IterDerivHelpers.iterDerivList_perm hperm]
    rw [IterDerivHelpers.iterDerivList_cons]
    rw [ProductDeriv.pderiv_prod_single (s := insert a T)
      (f := fun i => (X i * X i : MvPolynomial (Fin n) Rat))
      (i := a) (k := a) (Finset.mem_insert_self a T)]
    · rw [pderiv_X_mul_X_self]
      simp only [Finset.erase_insert ha]
      have hconst :
          ∀ i ∈ T.toList,
            pderiv i ((2 : Rat) • (X a : MvPolynomial (Fin n) Rat)) = 0 := by
        intro i hi
        have hia : i ≠ a := by
          intro h
          exact ha (by simpa [h] using hi)
        rw [(pderiv i).map_smul, MvPolynomial.pderiv_X_of_ne hia.symm]
        simp
      rw [IterDerivHelpers.iterDerivList_mul_left_const T.toList
        ((2 : Rat) • X a)
        (T.prod (fun i => (X i * X i : MvPolynomial (Fin n) Rat))) hconst]
      rw [ih]
      rw [Finset.prod_insert ha]
      simp only [Finset.card_insert_of_notMem ha]
      rw [pow_succ]
      rw [smul_mul_assoc, mul_smul_comm, smul_smul]
      rw [mul_comm (2 : Rat) ((2 : Rat) ^ T.card)]
    · intro j hj hja
      exact pderiv_helperSq_of_ne hja.symm

/-- Row terms can be written as payload times the product over the helper set. -/
theorem squareHelperRowTerm_eq_payload_mul_helperSet_prod_sq
    (kappa gadgetN : Nat) (r : Fin (rowCount kappa gadgetN)) :
    squareHelperRowTerm kappa gadgetN r =
      X (squarePayloadIndex kappa gadgetN r) *
        (squareRowHelperSet kappa gadgetN r).prod
          (fun i => (X i * X i :
            MvPolynomial (Fin (squareHelperVarCount kappa gadgetN)) Rat)) := by
  classical
  unfold squareHelperRowTerm squareRowHelperSet
  congr 1
  symm
  rw [Finset.prod_image]
  intro a _ b _ h
  exact squareHelperIndex_injective_right (kappa := kappa)
    (gadgetN := gadgetN) r h

/-- Row monomials can be written as payload times the product over the helper
set. -/
theorem squareRowLinearMonomial_eq_payload_mul_helperSet_prod_X
    (kappa gadgetN : Nat) (r : Fin (rowCount kappa gadgetN)) :
    squareRowLinearMonomial kappa gadgetN r =
      X (squarePayloadIndex kappa gadgetN r) *
        (squareRowHelperSet kappa gadgetN r).prod
          (fun i => (X i :
            MvPolynomial (Fin (squareHelperVarCount kappa gadgetN)) Rat)) := by
  classical
  unfold squareRowLinearMonomial squareRowHelperSet
  congr 1
  symm
  rw [Finset.prod_image]
  intro a _ b _ h
  exact squareHelperIndex_injective_right (kappa := kappa)
    (gadgetN := gadgetN) r h

/-- The upper-file row monomial is definitionally the same monomial as the
original row-space generator. -/
theorem squareHelperRowMonomial_eq_squareRowLinearMonomial
    (kappa gadgetN : Nat) (r : Fin (rowCount kappa gadgetN)) :
    squareHelperRowMonomial kappa gadgetN r =
      squareRowLinearMonomial kappa gadgetN r := by
  rfl

/-- The two row-space definitions in the square-helper files coincide. -/
theorem squareHelperRowSpace_eq_squareHelperRowSpan
    (kappa gadgetN : Nat) :
    squareHelperRowSpace kappa gadgetN = squareHelperRowSpan kappa gadgetN := by
  rfl

/-- Exact differentiation of one square-helper row by precisely its helper set. -/
theorem iterDerivList_squareRowHelperSet_toList_squareHelperRowTerm
    (kappa gadgetN : Nat) (r : Fin (rowCount kappa gadgetN)) :
    iterDerivList (squareRowHelperSet kappa gadgetN r).toList
        (squareHelperRowTerm kappa gadgetN r) =
      (2 : Rat) ^ kappa • squareRowLinearMonomial kappa gadgetN r := by
  classical
  rw [squareHelperRowTerm_eq_payload_mul_helperSet_prod_sq]
  rw [IterDerivHelpers.iterDerivList_mul_left_const]
  · rw [iterDerivList_toList_prod_X_sq]
    rw [squareRowLinearMonomial_eq_payload_mul_helperSet_prod_X]
    rw [squareRowHelperSet_card]
    simp
  · intro i hi
    simp only [Finset.mem_toList, squareRowHelperSet, Finset.mem_image,
      Finset.mem_univ, true_and] at hi
    rcases hi with ⟨j, rfl⟩
    rw [MvPolynomial.pderiv_X_of_ne]
    intro h
    have hsnd := congrArg Prod.snd (finProdFinEquiv.injective h.symm)
    exact Fin.succ_ne_zero j hsnd

/-- If a discrete-admissible strict-`kappa` list contains every helper of row
`r`, then its support is exactly that row's helper set. -/
theorem squareHelper_exactRow_toFinset_eq_squareRowHelperSet
    (kappa gadgetN : Nat)
    (S : List (Fin (squareHelperVarCount kappa gadgetN)))
    (r : Fin (rowCount kappa gadgetN))
    (hLen : S.length = kappa)
    (hAdm :
      isBlockAdmissible
        (discretePartition (squareHelperVarCount kappa gadgetN)) S)
    (hrow : ∀ j : Fin kappa, squareHelperIndex kappa gadgetN r j ∈ S) :
    S.toFinset = squareRowHelperSet kappa gadgetN r := by
  classical
  symm
  apply BlockedBoolRank.Finset.eq_of_subset_of_card_eq
  · intro x hx
    simp only [squareRowHelperSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hx
    rcases hx with ⟨j, rfl⟩
    simpa using hrow j
  · rw [List.toFinset_card_of_nodup hAdm.1, hLen,
      squareRowHelperSet_card]

/-- A helper of another row cannot belong to the exact row helper set. -/
theorem squareHelperIndex_not_mem_squareRowHelperSet_of_ne
    {kappa gadgetN : Nat}
    {r r' : Fin (rowCount kappa gadgetN)}
    (hne : r' ≠ r) (j : Fin kappa) :
    squareHelperIndex kappa gadgetN r' j ∉ squareRowHelperSet kappa gadgetN r := by
  classical
  intro hmem
  simp only [squareRowHelperSet, Finset.mem_image, Finset.mem_univ,
    true_and] at hmem
  rcases hmem with ⟨j', hj'⟩
  have hr : r = r' :=
    congrArg Prod.fst (finProdFinEquiv.injective hj')
  exact hne hr.symm

/-- Once `S` is exactly row `r`'s helper set, every other row misses a helper
from `S`. -/
theorem squareHelper_otherRow_missing_helper_of_exactRow
    {kappa gadgetN : Nat}
    (S : List (Fin (squareHelperVarCount kappa gadgetN)))
    {r r' : Fin (rowCount kappa gadgetN)}
    (hSset : S.toFinset = squareRowHelperSet kappa gadgetN r)
    (hne : r' ≠ r) :
    ∃ j : Fin kappa, squareHelperIndex kappa gadgetN r' j ∉ S := by
  classical
  have hkappa_pos : 0 < kappa := by
    by_contra hkappa
    have hkappa0 : kappa = 0 := Nat.eq_zero_of_not_pos hkappa
    subst kappa
    exact Fin.elim0 (by simpa [rowCount] using r)
  let j0 : Fin kappa := ⟨0, hkappa_pos⟩
  refine ⟨j0, ?_⟩
  intro hjS
  have hjFin : squareHelperIndex kappa gadgetN r' j0 ∈ S.toFinset := by
    simpa using hjS
  have hjRow : squareHelperIndex kappa gadgetN r' j0 ∈
      squareRowHelperSet kappa gadgetN r := by
    simpa [hSset] using hjFin
  exact squareHelperIndex_not_mem_squareRowHelperSet_of_ne
    (kappa := kappa) (gadgetN := gadgetN) hne j0 hjRow

/-- The payload variable is not one of its row's helper variables. -/
theorem squarePayloadIndex_not_mem_squareRowHelperSet
    (kappa gadgetN : Nat) (r : Fin (rowCount kappa gadgetN)) :
    squarePayloadIndex kappa gadgetN r ∉ squareRowHelperSet kappa gadgetN r := by
  classical
  intro hmem
  simp only [squareRowHelperSet, Finset.mem_image, Finset.mem_univ,
    true_and] at hmem
  rcases hmem with ⟨j, hj⟩
  have hsnd := congrArg Prod.snd (finProdFinEquiv.injective hj.symm)
  exact Fin.succ_ne_zero j hsnd.symm

/-- The product of coordinate variables over a finset is the corresponding
multilinear tag monomial. -/
theorem prod_X_eq_monomial_tag {n : Nat} (T : Finset (Fin n)) :
    T.prod (fun i => (X i : MvPolynomial (Fin n) Rat)) =
      monomial (SymmetricPower.tagMonomial T) (1 : Rat) := by
  rw [SymmetricPower.tagMonomial, MvPolynomial.monomial_sum_one]
  simp [MvPolynomial.X]

/-- The linear row monomial is the product over payload plus row helpers. -/
theorem squareRowLinearMonomial_eq_support_prod_X
    (kappa gadgetN : Nat) (r : Fin (rowCount kappa gadgetN)) :
    squareRowLinearMonomial kappa gadgetN r =
      (insert (squarePayloadIndex kappa gadgetN r)
        (squareRowHelperSet kappa gadgetN r)).prod
          (fun i => (X i :
            MvPolynomial (Fin (squareHelperVarCount kappa gadgetN)) Rat)) := by
  classical
  rw [Finset.prod_insert (squarePayloadIndex_not_mem_squareRowHelperSet
    kappa gadgetN r)]
  exact squareRowLinearMonomial_eq_payload_mul_helperSet_prod_X
    kappa gadgetN r

/-- `mlProj` fixes the exact multilinear row monomial. -/
theorem mlProj_squareRowLinearMonomial
    (kappa gadgetN : Nat) (r : Fin (rowCount kappa gadgetN)) :
    mlProj (squareRowLinearMonomial kappa gadgetN r) =
      squareRowLinearMonomial kappa gadgetN r := by
  rw [squareRowLinearMonomial_eq_support_prod_X, prod_X_eq_monomial_tag]
  rw [mlProj_monomial,
    if_pos (SymmetricPower.tagMonomial_isMultilinear _)]

/-- Exact-row contribution after an admissible strict row derivative lies in the
row span, for any shift supported on the derivative variables. -/
theorem mlProj_shift_iterDerivList_squareHelperRowTerm_mem_rowSpan_of_exactRow
    (kappa gadgetN : Nat)
    (S : List (Fin (squareHelperVarCount kappa gadgetN)))
    (m : MvPolynomial (Fin (squareHelperVarCount kappa gadgetN)) Rat)
    (r : Fin (rowCount kappa gadgetN))
    (hSnd : S.Nodup)
    (hSset : S.toFinset = squareRowHelperSet kappa gadgetN r)
    (hvars : m.vars ⊆ S.toFinset) :
    mlProj (m * iterDerivList S (squareHelperRowTerm kappa gadgetN r)) ∈
      squareHelperRowSpan kappa gadgetN := by
  classical
  have hperm : S.Perm (squareRowHelperSet kappa gadgetN r).toList := by
    apply (List.perm_ext_iff_of_nodup hSnd
      (squareRowHelperSet kappa gadgetN r).nodup_toList).mpr
    intro x
    simp [← hSset]
  rw [IterDerivHelpers.iterDerivList_perm hperm]
  rw [iterDerivList_squareRowHelperSet_toList_squareHelperRowTerm]
  rw [mul_smul_comm, mlProj_smul]
  apply Submodule.smul_mem
  rw [show m = ∑ s ∈ m.support, MvPolynomial.monomial s (MvPolynomial.coeff s m) from
    m.as_sum]
  rw [Finset.sum_mul]
  rw [mlProj_finset_sum]
  apply Submodule.sum_mem
  intro s hs
  have hcoeff_ne : MvPolynomial.coeff s m ≠ 0 := by
    simpa [MvPolynomial.mem_support_iff] using hs
  by_cases hs0 : s = 0
  · subst hs0
    rw [MvPolynomial.monomial_zero']
    rw [MvPolynomial.C_mul']
    rw [mlProj_smul]
    rw [mlProj_squareRowLinearMonomial]
    rw [← squareHelperRowMonomial_eq_squareRowLinearMonomial]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨r, rfl⟩
  · by_cases hzeroCoeff : MvPolynomial.coeff s m = 0
    · rw [hzeroCoeff, MvPolynomial.monomial_zero, zero_mul, mlProj_zero]
      exact Submodule.zero_mem _
    · have hs_support_nonempty : s.support.Nonempty := by
        simpa [Finsupp.support_eq_empty] using hs0
      rcases hs_support_nonempty with ⟨v, hv⟩
      have hv_vars : v ∈ m.vars :=
        (MvPolynomial.mem_vars v).mpr ⟨s, hs, hv⟩
      have hvS : v ∈ S.toFinset := hvars hv_vars
      have hvRow : v ∈ squareRowHelperSet kappa gadgetN r := by
        simpa [hSset] using hvS
      let R : Finset (Fin (squareHelperVarCount kappa gadgetN)) :=
        insert (squarePayloadIndex kappa gadgetN r)
          (squareRowHelperSet kappa gadgetN r)
      have hvR : v ∈ R := Finset.mem_insert_of_mem hvRow
      rw [squareRowLinearMonomial_eq_support_prod_X]
      change mlProj
          (MvPolynomial.monomial s (MvPolynomial.coeff s m) *
            R.prod (fun i => (X i :
              MvPolynomial (Fin (squareHelperVarCount kappa gadgetN)) Rat))) ∈
        squareHelperRowSpan kappa gadgetN
      rw [prod_X_eq_monomial_tag]
      rw [MvPolynomial.monomial_mul]
      simp only [mul_one]
      rw [mlProj_monomial]
      have hnot :
          ¬ Finsupp.IsMultilinear
            (s + SymmetricPower.tagMonomial R) := by
        intro hml
        have hvle := hml v
        have hspos : 0 < s v :=
          Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv)
        rw [Finsupp.add_apply, SymmetricPower.tagMonomial_apply,
          if_pos hvR] at hvle
        omega
      rw [if_neg hnot]
      exact Submodule.zero_mem _

/-- Exact-row upper containment into the row span. -/
theorem mlProj_shift_iterDerivList_squareHelperQ_mem_rowSpan_of_exactRow
    (kappa gadgetN : Nat)
    (S : List (Fin (squareHelperVarCount kappa gadgetN)))
    (m : MvPolynomial (Fin (squareHelperVarCount kappa gadgetN)) Rat)
    (r : Fin (rowCount kappa gadgetN))
    (hLen : S.length = kappa)
    (hAdm :
      isBlockAdmissible
        (discretePartition (squareHelperVarCount kappa gadgetN)) S)
    (hrow : ∀ j : Fin kappa, squareHelperIndex kappa gadgetN r j ∈ S)
    (hvars : m.vars ⊆ S.toFinset)
    (_hdeg : m.totalDegree ≤ kappa) :
    mlProj (m * iterDerivList S (squareHelperQ kappa gadgetN)) ∈
      squareHelperRowSpan kappa gadgetN := by
  classical
  have hSset :=
    squareHelper_exactRow_toFinset_eq_squareRowHelperSet
      kappa gadgetN S r hLen hAdm hrow
  unfold squareHelperQ
  rw [iterDerivList_finset_sum]
  rw [Finset.mul_sum]
  rw [mlProj_finset_sum]
  apply Submodule.sum_mem
  intro r' _hr'
  by_cases hrr : r' = r
  · subst r'
    exact mlProj_shift_iterDerivList_squareHelperRowTerm_mem_rowSpan_of_exactRow
      kappa gadgetN S m r hAdm.1 hSset hvars
  · rcases squareHelper_otherRow_missing_helper_of_exactRow
      (kappa := kappa) (gadgetN := gadgetN) S hSset hrr with ⟨j, hj⟩
    rw [mlProj_shift_iterDerivList_squareHelperRowTerm_eq_zero_of_helper_not_mem
      kappa gadgetN S m r' j hj]
    exact Submodule.zero_mem _

/-- Exact-row upper containment into the original row-space definition. -/
theorem mlProj_shift_iterDerivList_squareHelperQ_mem_rowSpace_of_exactRow
    (kappa gadgetN : Nat)
    (S : List (Fin (squareHelperVarCount kappa gadgetN)))
    (m : MvPolynomial (Fin (squareHelperVarCount kappa gadgetN)) Rat)
    (r : Fin (rowCount kappa gadgetN))
    (hLen : S.length = kappa)
    (hAdm :
      isBlockAdmissible
        (discretePartition (squareHelperVarCount kappa gadgetN)) S)
    (hrow : ∀ j : Fin kappa, squareHelperIndex kappa gadgetN r j ∈ S)
    (hvars : m.vars ⊆ S.toFinset)
    (hdeg : m.totalDegree ≤ kappa) :
    mlProj (m * iterDerivList S (squareHelperQ kappa gadgetN)) ∈
      squareHelperRowSpace kappa gadgetN := by
  rw [squareHelperRowSpace_eq_squareHelperRowSpan]
  exact mlProj_shift_iterDerivList_squareHelperQ_mem_rowSpan_of_exactRow
    kappa gadgetN S m r hLen hAdm hrow hvars hdeg

end BridgeAGeneralizedNonzeroWitness

end PallLean.Paper93.Paper283
