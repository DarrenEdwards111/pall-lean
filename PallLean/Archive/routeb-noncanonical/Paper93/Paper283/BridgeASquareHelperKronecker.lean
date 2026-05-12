import PallLean.Paper93.Paper283.BridgeASquareHelperUpper

/-!
# Kronecker coefficients for the Bridge A square-helper rows

This file is intentionally disjoint from the existing Bridge A files.  It
records coefficient-level progress for the derivative rows of `squareHelperQ`.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open SPDP

namespace BridgeAGeneralizedNonzeroWitness

attribute [local instance] Classical.dec

variable {kappa gadgetN : Nat}

theorem squarePayloadIndex_injective (kappa gadgetN : Nat) :
    Function.Injective (squarePayloadIndex kappa gadgetN) := by
  intro a b h
  apply Fin.ext
  exact congrArg Fin.val
    (congrArg Prod.fst (finProdFinEquiv.injective h))

theorem squareHelperIndex_injective (kappa gadgetN : Nat) :
    Function.Injective
      (fun rj : Fin (rowCount kappa gadgetN) × Fin kappa =>
        squareHelperIndex kappa gadgetN rj.1 rj.2) := by
  intro a b h
  have hp := finProdFinEquiv.injective h
  cases a with
  | mk ar aj =>
  cases b with
  | mk br bj =>
    have hr : ar = br := by
      apply Fin.ext
      exact congrArg Fin.val (congrArg Prod.fst hp)
    have hj : aj = bj := by
      apply Fin.ext
      exact Nat.succ.inj
        (congrArg Fin.val (congrArg Prod.snd hp))
    simp [hr, hj]

theorem squarePayloadIndex_ne_squareHelperIndex
    (kappa gadgetN : Nat)
    (r s : Fin (rowCount kappa gadgetN)) (j : Fin kappa) :
    squarePayloadIndex kappa gadgetN r ≠
      squareHelperIndex kappa gadgetN s j := by
  intro h
  have hsnd := congrArg Prod.snd (finProdFinEquiv.injective h)
  have hval := congrArg Fin.val hsnd
  simp at hval

theorem squareHelperIndex_eq_iff
    {r s : Fin (rowCount kappa gadgetN)} {i j : Fin kappa} :
    squareHelperIndex kappa gadgetN r i =
      squareHelperIndex kappa gadgetN s j ↔ r = s ∧ i = j := by
  constructor
  · intro h
    have hp : (r, i) = (s, j) :=
      (squareHelperIndex_injective kappa gadgetN h)
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem squareHelperRowMonomial_eq_monomial_linearExponent
    (kappa gadgetN : Nat) (r : Fin (rowCount kappa gadgetN)) :
    squareHelperRowMonomial kappa gadgetN r =
      monomial (squareRowLinearExponent kappa gadgetN r) (1 : Rat) := by
  unfold squareHelperRowMonomial squareRowLinearExponent
  rw [show
      (∏ j : Fin kappa, X (squareHelperIndex kappa gadgetN r j) :
          MvPolynomial (Fin (squareHelperVarCount kappa gadgetN)) Rat) =
        monomial
          ((Finset.univ : Finset (Fin kappa)).sum
            (fun j => Finsupp.single (squareHelperIndex kappa gadgetN r j) 1))
          (1 : Rat) by
    rw [MvPolynomial.monomial_sum_one]
    simp [MvPolynomial.X]]
  rw [MvPolynomial.X]
  rw [MvPolynomial.monomial_mul]
  simp

theorem squareRowLinearMonomial_eq_squareHelperRowMonomial
    (kappa gadgetN : Nat) (r : Fin (rowCount kappa gadgetN)) :
    squareRowLinearMonomial kappa gadgetN r =
      squareHelperRowMonomial kappa gadgetN r := by
  rfl

theorem squareRowLinearExponent_injective (kappa gadgetN : Nat) :
    Function.Injective (squareRowLinearExponent kappa gadgetN) := by
  intro r s h
  apply squarePayloadIndex_injective kappa gadgetN
  have hcoord := congrArg
    (fun e : Fin (squareHelperVarCount kappa gadgetN) →₀ Nat =>
      e (squarePayloadIndex kappa gadgetN r)) h
  have hone :
      1 =
        (Finsupp.single (squarePayloadIndex kappa gadgetN s) 1)
          (squarePayloadIndex kappa gadgetN r) := by
    simpa [squareRowLinearExponent, squarePayloadIndex_ne_squareHelperIndex] using hcoord
  by_contra hne
  have hne' :
      squarePayloadIndex kappa gadgetN s ≠
        squarePayloadIndex kappa gadgetN r := fun hsr => hne hsr.symm
  have hz :
      (Finsupp.single (squarePayloadIndex kappa gadgetN s) 1)
          (squarePayloadIndex kappa gadgetN r) = 0 := by
    simp [hne']
  omega

noncomputable def squareHelperSquareProd (kappa gadgetN : Nat)
    (r : Fin (rowCount kappa gadgetN)) (S : Finset (Fin kappa)) :
    MvPolynomial (Fin (squareHelperVarCount kappa gadgetN)) Rat :=
  S.prod (fun j =>
    X (squareHelperIndex kappa gadgetN r j) *
      X (squareHelperIndex kappa gadgetN r j))

noncomputable def squareHelperLinearProd (kappa gadgetN : Nat)
    (r : Fin (rowCount kappa gadgetN)) (S : Finset (Fin kappa)) :
    MvPolynomial (Fin (squareHelperVarCount kappa gadgetN)) Rat :=
  S.prod (fun j => X (squareHelperIndex kappa gadgetN r j))

theorem pderiv_squareHelperSquare_of_ne
    (kappa gadgetN : Nat) (r : Fin (rowCount kappa gadgetN))
    {i j : Fin kappa} (hij : i ≠ j) :
    pderiv (squareHelperIndex kappa gadgetN r i)
      (X (squareHelperIndex kappa gadgetN r j) *
        X (squareHelperIndex kappa gadgetN r j) :
        MvPolynomial (Fin (squareHelperVarCount kappa gadgetN)) Rat) = 0 := by
  exact pderiv_helperSq_of_ne
    (n := squareHelperVarCount kappa gadgetN)
    (v := squareHelperIndex kappa gadgetN r j)
    (i := squareHelperIndex kappa gadgetN r i)
    (by
      intro h
      exact hij
        ((squareHelperIndex_eq_iff (kappa := kappa) (gadgetN := gadgetN)).mp h).2)

theorem pderiv_squareHelperSquareProd_eq_zero_of_not_mem
    (kappa gadgetN : Nat) (r : Fin (rowCount kappa gadgetN))
    (a : Fin kappa) (S : Finset (Fin kappa)) (haS : a ∉ S) :
    pderiv (squareHelperIndex kappa gadgetN r a)
      (squareHelperSquareProd kappa gadgetN r S) = 0 := by
  classical
  unfold squareHelperSquareProd
  induction S using Finset.induction_on with
  | empty =>
      simp
  | insert b S hbS ih =>
      have hab : a ≠ b := by
        intro h
        exact haS (by simp [h])
      have haS' : a ∉ S := by
        intro h
        exact haS (Finset.mem_insert_of_mem h)
      rw [Finset.prod_insert hbS, pderiv_mul,
        pderiv_squareHelperSquare_of_ne kappa gadgetN r hab, ih haS']
      simp

theorem pderiv_squareHelperSquare_self
    (kappa gadgetN : Nat) (r : Fin (rowCount kappa gadgetN)) (a : Fin kappa) :
    pderiv (squareHelperIndex kappa gadgetN r a)
      (X (squareHelperIndex kappa gadgetN r a) *
        X (squareHelperIndex kappa gadgetN r a) :
        MvPolynomial (Fin (squareHelperVarCount kappa gadgetN)) Rat) =
      (2 : Rat) • X (squareHelperIndex kappa gadgetN r a) := by
  rw [pderiv_mul, MvPolynomial.pderiv_X_self]
  simp only [one_mul, mul_one]
  rw [two_smul]

theorem pderiv_payload_mul_squareHelperSquareProd_insert
    (kappa gadgetN : Nat) (r : Fin (rowCount kappa gadgetN))
    (a : Fin kappa) (S : Finset (Fin kappa)) (haS : a ∉ S) :
    pderiv (squareHelperIndex kappa gadgetN r a)
      (X (squarePayloadIndex kappa gadgetN r) *
        squareHelperSquareProd kappa gadgetN r (insert a S)) =
      (2 : Rat) •
        (X (squarePayloadIndex kappa gadgetN r) *
          X (squareHelperIndex kappa gadgetN r a) *
          squareHelperSquareProd kappa gadgetN r S) := by
  classical
  have hpayload :
      pderiv (squareHelperIndex kappa gadgetN r a)
        (X (squarePayloadIndex kappa gadgetN r) :
          MvPolynomial (Fin (squareHelperVarCount kappa gadgetN)) Rat) = 0 := by
    rw [MvPolynomial.pderiv_X_of_ne]
    exact squarePayloadIndex_ne_squareHelperIndex kappa gadgetN r r a
  have hrest :
      pderiv (squareHelperIndex kappa gadgetN r a)
        (squareHelperSquareProd kappa gadgetN r S) = 0 :=
    pderiv_squareHelperSquareProd_eq_zero_of_not_mem kappa gadgetN r a S haS
  rw [show
      squareHelperSquareProd kappa gadgetN r (insert a S) =
        (X (squareHelperIndex kappa gadgetN r a) *
          X (squareHelperIndex kappa gadgetN r a)) *
          squareHelperSquareProd kappa gadgetN r S by
    unfold squareHelperSquareProd
    rw [Finset.prod_insert haS]]
  nth_rewrite 1 [pderiv_mul]
  rw [hpayload, zero_mul, zero_add]
  nth_rewrite 1 [pderiv_mul]
  rw [pderiv_squareHelperSquare_self, hrest]
  simp only [mul_zero, add_zero]
  simp [MvPolynomial.smul_eq_C_mul]
  ring

theorem iterDerivList_smul_rat {n : Nat}
    (S : List (Fin n)) (c : Rat) (p : MvPolynomial (Fin n) Rat) :
    iterDerivList S (c • p) = c • iterDerivList S p := by
  induction S generalizing p with
  | nil =>
      rfl
  | cons i rest ih =>
      rw [IterDerivHelpers.iterDerivList_cons,
        (IterDerivHelpers.iterDerivList_cons i rest p)]
      rw [Derivation.map_smul, ih]

theorem iterDerivList_helperSquareProd_list
    (kappa gadgetN : Nat) (r : Fin (rowCount kappa gadgetN))
    (L : List (Fin kappa)) (hL : L.Nodup) :
    iterDerivList (L.map (squareHelperIndex kappa gadgetN r))
      (X (squarePayloadIndex kappa gadgetN r) *
        squareHelperSquareProd kappa gadgetN r L.toFinset) =
      ((2 : Rat) ^ L.length) •
        (X (squarePayloadIndex kappa gadgetN r) *
          squareHelperLinearProd kappa gadgetN r L.toFinset) := by
  classical
  induction L with
  | nil =>
      simp [squareHelperSquareProd, squareHelperLinearProd]
  | cons a rest ih =>
      have haRest : a ∉ rest.toFinset := by
        simpa [List.mem_toFinset] using (List.nodup_cons.mp hL).1
      have hrestNodup : rest.Nodup := hL.tail
      simp only [List.map_cons, IterDerivHelpers.iterDerivList_cons,
        List.length_cons]
      rw [List.toFinset_cons]
      rw [pderiv_payload_mul_squareHelperSquareProd_insert
        kappa gadgetN r a rest.toFinset haRest]
      rw [iterDerivList_smul_rat]
      rw [show
          X (squarePayloadIndex kappa gadgetN r) *
              X (squareHelperIndex kappa gadgetN r a) *
              squareHelperSquareProd kappa gadgetN r rest.toFinset =
            X (squareHelperIndex kappa gadgetN r a) *
              (X (squarePayloadIndex kappa gadgetN r) *
                squareHelperSquareProd kappa gadgetN r rest.toFinset) by
        ring]
      rw [IterDerivHelpers.iterDerivList_mul_left_const]
      · rw [ih hrestNodup]
        unfold squareHelperLinearProd
        rw [Finset.prod_insert haRest]
        simp [pow_succ, MvPolynomial.smul_eq_C_mul]
        ring
      · intro i hi
        rw [MvPolynomial.pderiv_X_of_ne]
        intro h
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hi
        have hab : a = b :=
          ((squareHelperIndex_eq_iff (kappa := kappa) (gadgetN := gadgetN)).mp h).2
        exact haRest (by
          rw [List.mem_toFinset]
          rwa [hab])

theorem squareRowHelperSet_toList_perm_univ_map
    (kappa gadgetN : Nat) (r : Fin (rowCount kappa gadgetN)) :
    (squareRowHelperSet kappa gadgetN r).toList.Perm
      ((Finset.univ : Finset (Fin kappa)).toList.map
        (squareHelperIndex kappa gadgetN r)) := by
  classical
  unfold squareRowHelperSet
  let L := (Finset.univ : Finset (Fin kappa)).toList.map
    (squareHelperIndex kappa gadgetN r)
  have hnodup : L.Nodup := by
    unfold L
    exact (Finset.univ : Finset (Fin kappa)).nodup_toList.map
      (squareHelperIndex_injective_right (kappa := kappa)
        (gadgetN := gadgetN) r)
  have hto :
      L.toFinset =
        (Finset.univ : Finset (Fin kappa)).image
          (squareHelperIndex kappa gadgetN r) := by
    ext x
    simp [L]
  simpa [L, hto] using (List.toFinset_toList hnodup)

theorem iterDerivList_squareHelperRowTerm_own_eq
    (kappa gadgetN : Nat) (r : Fin (rowCount kappa gadgetN)) :
    iterDerivList (squareRowHelperSet kappa gadgetN r).toList
      (squareHelperRowTerm kappa gadgetN r) =
      ((2 : Rat) ^ kappa) • squareHelperRowMonomial kappa gadgetN r := by
  classical
  let L := (Finset.univ : Finset (Fin kappa)).toList
  have hperm := squareRowHelperSet_toList_perm_univ_map kappa gadgetN r
  rw [IterDerivHelpers.iterDerivList_perm hperm]
  have hcalc := iterDerivList_helperSquareProd_list kappa gadgetN r L
    (Finset.univ : Finset (Fin kappa)).nodup_toList
  simpa [L, squareHelperRowTerm, squareHelperRowMonomial,
    squareHelperSquareProd, squareHelperLinearProd] using hcalc

theorem squareRowLinearExponent_isMultilinear
    (kappa gadgetN : Nat) (r : Fin (rowCount kappa gadgetN)) :
    Finsupp.IsMultilinear (squareRowLinearExponent kappa gadgetN r) := by
  intro x
  by_cases hp : x = squarePayloadIndex kappa gadgetN r
  · subst x
    simp [squareRowLinearExponent, squarePayloadIndex_ne_squareHelperIndex]
  · by_cases hx :
        ∃ j : Fin kappa, squareHelperIndex kappa gadgetN r j = x
    · rcases hx with ⟨j, rfl⟩
      have hsum :
          ((Finset.univ : Finset (Fin kappa)).sum
            (fun c => Finsupp.single (squareHelperIndex kappa gadgetN r c) 1))
              (squareHelperIndex kappa gadgetN r j) = 1 := by
        rw [Finsupp.finset_sum_apply]
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _hb hbj
          have hne :
              squareHelperIndex kappa gadgetN r b ≠
                squareHelperIndex kappa gadgetN r j := by
            intro h
            exact hbj
              ((squareHelperIndex_eq_iff (kappa := kappa)
                (gadgetN := gadgetN)).mp h).2
          simp [hne]
        · intro hnot
          exact (hnot (Finset.mem_univ j)).elim
      have hpay :
          squarePayloadIndex kappa gadgetN r ≠
            squareHelperIndex kappa gadgetN r j :=
        squarePayloadIndex_ne_squareHelperIndex kappa gadgetN r r j
      change
        (Finsupp.single (squarePayloadIndex kappa gadgetN r) 1
            (squareHelperIndex kappa gadgetN r j) +
          ((Finset.univ : Finset (Fin kappa)).sum
            (fun c => Finsupp.single (squareHelperIndex kappa gadgetN r c) 1))
              (squareHelperIndex kappa gadgetN r j)) ≤ 1
      rw [hsum]
      simp [hpay]
    · have hzero :
        ((Finset.univ : Finset (Fin kappa)).sum
          (fun j => Finsupp.single (squareHelperIndex kappa gadgetN r j) 1)) x = 0 := by
        rw [Finsupp.finset_sum_apply]
        apply Finset.sum_eq_zero
        intro j _hj
        have hne : squareHelperIndex kappa gadgetN r j ≠ x := fun h => hx ⟨j, h⟩
        simp [hne]
      have hp' : squarePayloadIndex kappa gadgetN r ≠ x := fun h => hp h.symm
      change
        (Finsupp.single (squarePayloadIndex kappa gadgetN r) 1 x +
          ((Finset.univ : Finset (Fin kappa)).sum
            (fun j => Finsupp.single (squareHelperIndex kappa gadgetN r j) 1)) x) ≤ 1
      rw [hzero]
      simp [hp']

theorem mlProj_squareHelperRowMonomial
    (kappa gadgetN : Nat) (r : Fin (rowCount kappa gadgetN)) :
    mlProj (squareHelperRowMonomial kappa gadgetN r) =
      squareHelperRowMonomial kappa gadgetN r := by
  rw [squareHelperRowMonomial_eq_monomial_linearExponent]
  rw [mlProj_monomial,
    if_pos (squareRowLinearExponent_isMultilinear kappa gadgetN r)]

theorem mlProj_iterDerivList_squareHelperRowTerm_own_eq
    (kappa gadgetN : Nat) (r : Fin (rowCount kappa gadgetN)) :
    mlProj (iterDerivList (squareRowHelperSet kappa gadgetN r).toList
      (squareHelperRowTerm kappa gadgetN r)) =
      ((2 : Rat) ^ kappa) • squareHelperRowMonomial kappa gadgetN r := by
  rw [iterDerivList_squareHelperRowTerm_own_eq]
  rw [mlProj_smul, mlProj_squareHelperRowMonomial]

theorem squareHelperIndex_not_mem_other_rowHelperSet_toList
    (kappa gadgetN : Nat) {r t : Fin (rowCount kappa gadgetN)}
    (hrt : r ≠ t) :
    ∃ j : Fin kappa,
      squareHelperIndex kappa gadgetN r j ∉
        (squareRowHelperSet kappa gadgetN t).toList := by
  have hkpos : 0 < kappa := by
    by_contra hk
    have hk0 : kappa = 0 := Nat.eq_zero_of_not_pos hk
    have ht : t.val < 0 := by
      simpa [rowCount, hk0] using t.isLt
    omega
  refine ⟨⟨0, hkpos⟩, ?_⟩
  intro hmem
  have hfin :
      squareHelperIndex kappa gadgetN r ⟨0, hkpos⟩ ∈
        squareRowHelperSet kappa gadgetN t := by
    simpa using hmem
  unfold squareRowHelperSet at hfin
  rcases Finset.mem_image.mp hfin with ⟨j, _hj, hidx⟩
  have htr : t = r :=
    ((squareHelperIndex_eq_iff (kappa := kappa) (gadgetN := gadgetN)).mp hidx).1
  exact hrt htr.symm

theorem mlProj_iterDerivList_squareHelperRowTerm_other_eq_zero
    (kappa gadgetN : Nat) {r t : Fin (rowCount kappa gadgetN)}
    (hrt : r ≠ t) :
    mlProj (iterDerivList (squareRowHelperSet kappa gadgetN t).toList
      (squareHelperRowTerm kappa gadgetN r)) = 0 := by
  rcases squareHelperIndex_not_mem_other_rowHelperSet_toList
    kappa gadgetN (r := r) (t := t) hrt with ⟨j, hj⟩
  simpa using
    (mlProj_shift_iterDerivList_squareHelperRowTerm_eq_zero_of_helper_not_mem
      kappa gadgetN (squareRowHelperSet kappa gadgetN t).toList
      (1 : MvPolynomial (Fin (squareHelperVarCount kappa gadgetN)) Rat)
      r j hj)

theorem mlProj_iterDerivList_squareHelperQ_row_eq
    (kappa gadgetN : Nat) (t : Fin (rowCount kappa gadgetN)) :
    mlProj (iterDerivList (squareRowHelperSet kappa gadgetN t).toList
      (squareHelperQ kappa gadgetN)) =
      ((2 : Rat) ^ kappa) • squareHelperRowMonomial kappa gadgetN t := by
  classical
  unfold squareHelperQ
  rw [iterDerivList_finset_sum]
  rw [mlProj_finset_sum]
  rw [Finset.sum_eq_single t]
  · exact mlProj_iterDerivList_squareHelperRowTerm_own_eq kappa gadgetN t
  · intro r _hr hrt
    exact mlProj_iterDerivList_squareHelperRowTerm_other_eq_zero
      kappa gadgetN (r := r) (t := t) hrt
  · intro ht
    exact (ht (Finset.mem_univ t)).elim

theorem coeff_mlProj_iterDerivList_squareHelperQ_row
    (kappa gadgetN : Nat) (s t : Fin (rowCount kappa gadgetN)) :
    coeff (squareRowLinearExponent kappa gadgetN s)
      (mlProj (iterDerivList (squareRowHelperSet kappa gadgetN t).toList
        (squareHelperQ kappa gadgetN))) =
      if s = t then (2 : Rat) ^ kappa else 0 := by
  rw [mlProj_iterDerivList_squareHelperQ_row_eq]
  rw [coeff_smul]
  rw [squareHelperRowMonomial_eq_monomial_linearExponent]
  rw [MvPolynomial.coeff_monomial]
  by_cases hst : s = t
  · subst hst
    simp
  · have hmono :
        squareRowLinearExponent kappa gadgetN t ≠
          squareRowLinearExponent kappa gadgetN s := by
      intro h
      exact hst ((squareRowLinearExponent_injective kappa gadgetN) h.symm)
    simp [hst, hmono]

theorem squareHelperDerivativeRowKronecker_squareHelperQ
    (kappa gadgetN : Nat) :
    squareHelperDerivativeRowKronecker kappa gadgetN := by
  intro s t
  exact coeff_mlProj_iterDerivList_squareHelperQ_row kappa gadgetN s t

end BridgeAGeneralizedNonzeroWitness

end PallLean.Paper93.Paper283
