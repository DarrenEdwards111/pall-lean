import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityTwo
import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityThreeResidualActive

/-!
# Residual active claim for identity (2) per-pair sum

This file mirrors the closed identity-(3) residual computation for the
left/right off-diagonal identity (2):

```
coeff probeRight
  (pderivListProdSumTwice (3k-1) (3k) touchedFactors)
  = crossBlockKValue (transCoeffSum M).
```

The row indices `{3k-1, 3k}` are disjoint from the probe indices
`{3k+1, 3k+2}`.  As in identity (3), this makes the quantitative
computation self-term-only after an inert/active partition.  The
surviving self terms are the factors at `(3k-1, 3k)`, and the residual
bilinear coefficient of the inert product is `-transCoeffSum M`.

No `sorry`.  No new axioms.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP
open BridgeABlockProductRule
open BridgeAKappaTwoTwoFoldLeibnizExpansion
open BridgeAKappaTwoFactorPairLemmas
open BridgeAKappaTwoIdentityOne
open BridgeAKappaTwoIdentityTwo
open BridgeAKappaTwoIdentityFour
open BridgeAKappaTwoIdentityThreeAux
open BridgeAKappaTwoIdentityThreeStructural
open BridgeAKappaTwoIdentityThreeResidualActive
open BridgeAKappaTwoListInductionHelpers
open MultilinearCoefficientInfrastructure

attribute [local instance] Classical.dec

namespace BridgeAKappaTwoIdentityTwoResidualActive

/-! ## Section A: identity-(2) indices -/

/-- First row index for identity (2): `3k-1`. -/
noncomputable def uIdx
    (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) : Fin n :=
  ⟨3 * k - 1, by omega⟩

/-- Second row index for identity (2): `3k`. -/
noncomputable def vIdx (n k : Nat) (hk2 : 3 * k + 3 < n) : Fin n :=
  ⟨3 * k, by omega⟩

/-- First probe-right index: `3k+1`. -/
noncomputable def aIdx (n k : Nat) (hk2 : 3 * k + 3 < n) : Fin n :=
  ⟨3 * k + 1, by omega⟩

/-- Second probe-right index: `3k+2`. -/
noncomputable def bIdx (n k : Nat) (hk2 : 3 * k + 3 < n) : Fin n :=
  ⟨3 * k + 2, by omega⟩

/-- Right stray index: `3k+3`. -/
noncomputable def rIdx (n k : Nat) (hk2 : 3 * k + 3 < n) : Fin n :=
  ⟨3 * k + 3, hk2⟩

theorem rowLeft_first_eq_uIdx
    (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    (⟨3 * (k - 1) + 2, by
      have heq : 3 * (k - 1) + 3 = 3 * k := by
        rw [show (3 : Nat) = 3 * 1 from rfl, ← Nat.mul_add]
        congr 1; omega
      omega⟩ : Fin n) = uIdx n k hk1 hk2 := by
  apply Fin.ext
  unfold uIdx
  simp
  omega

theorem rowLeft_second_eq_vIdx
    (n k : Nat) (hk2 : 3 * k + 3 < n) :
    (⟨3 * k + 0, by omega⟩ : Fin n) = vIdx n k hk2 := by
  apply Fin.ext
  unfold vIdx
  simp

theorem aIdx_ne_bIdx (n k : Nat) (hk2 : 3 * k + 3 < n) :
    aIdx n k hk2 ≠ bIdx n k hk2 := by
  unfold aIdx bIdx
  intro h
  have := congr_arg Fin.val h
  simp at this

theorem uIdx_ne_vIdx (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    uIdx n k hk1 hk2 ≠ vIdx n k hk2 := by
  unfold uIdx vIdx
  intro h
  have := congr_arg Fin.val h
  simp at this
  omega

theorem uIdx_ne_aIdx (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    uIdx n k hk1 hk2 ≠ aIdx n k hk2 := by
  unfold uIdx aIdx
  intro h
  have := congr_arg Fin.val h
  simp at this

theorem uIdx_ne_bIdx (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    uIdx n k hk1 hk2 ≠ bIdx n k hk2 := by
  unfold uIdx bIdx
  intro h
  have := congr_arg Fin.val h
  simp at this
  omega

theorem vIdx_ne_aIdx (n k : Nat) (hk2 : 3 * k + 3 < n) :
    vIdx n k hk2 ≠ aIdx n k hk2 := by
  unfold vIdx aIdx
  intro h
  have := congr_arg Fin.val h
  simp at this

theorem vIdx_ne_bIdx (n k : Nat) (hk2 : 3 * k + 3 < n) :
    vIdx n k hk2 ≠ bIdx n k hk2 := by
  unfold vIdx bIdx
  intro h
  have := congr_arg Fin.val h
  simp at this

theorem aIdx_ne_rIdx (n k : Nat) (hk2 : 3 * k + 3 < n) :
    aIdx n k hk2 ≠ rIdx n k hk2 := by
  unfold aIdx rIdx
  intro h
  have := congr_arg Fin.val h
  simp at this

theorem bIdx_ne_rIdx (n k : Nat) (hk2 : 3 * k + 3 < n) :
    bIdx n k hk2 ≠ rIdx n k hk2 := by
  unfold bIdx rIdx
  intro h
  have := congr_arg Fin.val h
  simp at this

theorem probeRight_eq (n k : Nat) (hk2 : 3 * k + 3 < n) :
    probeRight n k hk2 =
      Finsupp.single (aIdx n k hk2) 1 + Finsupp.single (bIdx n k hk2) 1 := by
  unfold probeRight aIdx bIdx
  rfl

theorem prevSucc_eq_vIdx
    (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    (⟨3 * k - 1 + 1, by omega⟩ : Fin n) = vIdx n k hk2 := by
  apply Fin.ext
  unfold vIdx
  simp
  omega

/-! ## Section B: factor partition -/

/-- The active factors carrying the full left row `(3k-1, 3k)`. -/
noncomputable def activeUVFactorsList
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    List (MvPolynomial (Fin n) ℚ) :=
  [cadjFactorPoly 1 (uIdx n k hk1 hk2) (vIdx n k hk2)] ++
  (List.finRange M.numStates).flatMap (fun q =>
    [cadjFactorPoly (transCoeff M q) (uIdx n k hk1 hk2) (vIdx n k hk2)])

/-- The active factors carrying `3k` but not `3k-1`. -/
noncomputable def activeVAFactorsList
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (_hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    List (MvPolynomial (Fin n) ℚ) :=
  [boolFactorPoly n (vIdx n k hk2),
   cadjFactorPoly 1 (vIdx n k hk2) (aIdx n k hk2)] ++
  (List.finRange M.numStates).flatMap (fun q =>
    [cadjFactorPoly (transCoeff M q) (vIdx n k hk2) (aIdx n k hk2)])

/-- The active list, split in the order used by the product rule. -/
noncomputable def activeFactorsList
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    List (MvPolynomial (Fin n) ℚ) :=
  activeUVFactorsList M n k hk1 hk2 ++
    activeVAFactorsList M n k hk1 hk2

/-- The inert factors for identity (2): probe bools, direct probe
adj/trans factors, and the right-stray `(3k+2,3k+3)` family. -/
noncomputable def inertFactorsList
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (_hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    List (MvPolynomial (Fin n) ℚ) :=
  [boolFactorPoly n (aIdx n k hk2),
   boolFactorPoly n (bIdx n k hk2),
   cadjFactorPoly 1 (aIdx n k hk2) (bIdx n k hk2),
   cadjFactorPoly 1 (bIdx n k hk2) (rIdx n k hk2)] ++
  (List.finRange M.numStates).flatMap (fun q =>
    [cadjFactorPoly (transCoeff M q) (aIdx n k hk2) (bIdx n k hk2),
     cadjFactorPoly (transCoeff M q) (bIdx n k hk2) (rIdx n k hk2)])

/-- Structural partition claim for the mapped touched list. -/
def touchedListPoly_perm_partition_claim
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) : Prop :=
  (BridgeAKappaTwoIdentityThreeStructural.touchedListPoly M n k hk1 hk2).Perm
    (inertFactorsList M n k hk1 hk2 ++ activeFactorsList M n k hk1 hk2)

/-- Quantitative residual after the inert/active partition. -/
def identityTwo_residualActiveClaim
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) : Prop :=
  MvPolynomial.coeff (probeRight n k hk2)
      ((inertFactorsList M n k hk1 hk2).prod *
        pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
          (activeFactorsList M n k hk1 hk2)) =
    crossBlockKValue (transCoeffSum M)

/-! ## Section C: inertness and the structural partition theorem -/

theorem bool_a_inert
    (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.pderiv (uIdx n k hk1 hk2)
        (boolFactorPoly n (aIdx n k hk2)) = 0 ∧
    MvPolynomial.pderiv (vIdx n k hk2)
        (boolFactorPoly n (aIdx n k hk2)) = 0 := by
  refine ⟨?_, ?_⟩
  · exact pderiv_one_sub_boolLC_factor_of_ne (aIdx n k hk2)
      (uIdx n k hk1 hk2) (uIdx_ne_aIdx n k hk1 hk2)
  · exact pderiv_one_sub_boolLC_factor_of_ne (aIdx n k hk2)
      (vIdx n k hk2) (vIdx_ne_aIdx n k hk2)

theorem bool_b_inert
    (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.pderiv (uIdx n k hk1 hk2)
        (boolFactorPoly n (bIdx n k hk2)) = 0 ∧
    MvPolynomial.pderiv (vIdx n k hk2)
        (boolFactorPoly n (bIdx n k hk2)) = 0 := by
  refine ⟨?_, ?_⟩
  · exact pderiv_one_sub_boolLC_factor_of_ne (bIdx n k hk2)
      (uIdx n k hk1 hk2) (uIdx_ne_bIdx n k hk1 hk2)
  · exact pderiv_one_sub_boolLC_factor_of_ne (bIdx n k hk2)
      (vIdx n k hk2) (vIdx_ne_bIdx n k hk2)

theorem cadj_a_b_inert
    (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) (c : ℚ) :
    MvPolynomial.pderiv (uIdx n k hk1 hk2)
        (cadjFactorPoly c (aIdx n k hk2) (bIdx n k hk2)) = 0 ∧
    MvPolynomial.pderiv (vIdx n k hk2)
        (cadjFactorPoly c (aIdx n k hk2) (bIdx n k hk2)) = 0 := by
  refine ⟨?_, ?_⟩
  · exact pderiv_one_sub_C_X_mul_X_at_other c
      (aIdx n k hk2) (bIdx n k hk2) (uIdx n k hk1 hk2)
      (uIdx_ne_aIdx n k hk1 hk2) (uIdx_ne_bIdx n k hk1 hk2)
  · exact pderiv_one_sub_C_X_mul_X_at_other c
      (aIdx n k hk2) (bIdx n k hk2) (vIdx n k hk2)
      (vIdx_ne_aIdx n k hk2) (vIdx_ne_bIdx n k hk2)

theorem cadj_b_r_inert
    (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) (c : ℚ) :
    MvPolynomial.pderiv (uIdx n k hk1 hk2)
        (cadjFactorPoly c (bIdx n k hk2) (rIdx n k hk2)) = 0 ∧
    MvPolynomial.pderiv (vIdx n k hk2)
        (cadjFactorPoly c (bIdx n k hk2) (rIdx n k hk2)) = 0 := by
  refine ⟨?_, ?_⟩
  · exact pderiv_one_sub_C_X_mul_X_at_other c
      (bIdx n k hk2) (rIdx n k hk2) (uIdx n k hk1 hk2)
      (uIdx_ne_bIdx n k hk1 hk2)
      (by
        intro h
        have := congr_arg Fin.val h
        unfold uIdx rIdx at this
        simp at this
        omega)
  · exact pderiv_one_sub_C_X_mul_X_at_other c
      (bIdx n k hk2) (rIdx n k hk2) (vIdx n k hk2)
      (vIdx_ne_bIdx n k hk2)
      (by
        intro h
        have := congr_arg Fin.val h
        unfold vIdx rIdx at this
        simp at this)

theorem inertFactorsList_inert_at_u
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ inertFactorsList M n k hk1 hk2) :
    MvPolynomial.pderiv (uIdx n k hk1 hk2) f = 0 := by
  unfold inertFactorsList at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange] at hf
  rcases hf with ((rfl | rfl | rfl | rfl) | ⟨q, _hq, rfl | rfl⟩)
  · exact (bool_a_inert n k hk1 hk2).1
  · exact (bool_b_inert n k hk1 hk2).1
  · exact (cadj_a_b_inert n k hk1 hk2 1).1
  · exact (cadj_b_r_inert n k hk1 hk2 1).1
  · exact (cadj_a_b_inert n k hk1 hk2 (transCoeff M q)).1
  · exact (cadj_b_r_inert n k hk1 hk2 (transCoeff M q)).1

theorem inertFactorsList_inert_at_v
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ inertFactorsList M n k hk1 hk2) :
    MvPolynomial.pderiv (vIdx n k hk2) f = 0 := by
  unfold inertFactorsList at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange] at hf
  rcases hf with ((rfl | rfl | rfl | rfl) | ⟨q, _hq, rfl | rfl⟩)
  · exact (bool_a_inert n k hk1 hk2).2
  · exact (bool_b_inert n k hk1 hk2).2
  · exact (cadj_a_b_inert n k hk1 hk2 1).2
  · exact (cadj_b_r_inert n k hk1 hk2 1).2
  · exact (cadj_a_b_inert n k hk1 hk2 (transCoeff M q)).2
  · exact (cadj_b_r_inert n k hk1 hk2 (transCoeff M q)).2

private theorem transSkel_flatMap_perm_split_identityTwo
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    ((List.finRange M.numStates).flatMap (fun q =>
        [cadjFactorPoly (transCoeff M q) (uIdx n k hk1 hk2) (vIdx n k hk2),
         cadjFactorPoly (transCoeff M q) (vIdx n k hk2) (aIdx n k hk2),
         cadjFactorPoly (transCoeff M q) (aIdx n k hk2) (bIdx n k hk2),
         cadjFactorPoly (transCoeff M q) (bIdx n k hk2) (rIdx n k hk2)])).Perm
      (((List.finRange M.numStates).flatMap (fun q =>
          [cadjFactorPoly (transCoeff M q) (aIdx n k hk2) (bIdx n k hk2),
           cadjFactorPoly (transCoeff M q) (bIdx n k hk2) (rIdx n k hk2)])) ++
       ((List.finRange M.numStates).flatMap (fun q =>
          [cadjFactorPoly (transCoeff M q) (uIdx n k hk1 hk2) (vIdx n k hk2)])) ++
       ((List.finRange M.numStates).flatMap (fun q =>
          [cadjFactorPoly (transCoeff M q) (vIdx n k hk2) (aIdx n k hk2)]))) := by
  set Fuv : List (MvPolynomial (Fin n) ℚ) :=
    (List.finRange M.numStates).flatMap (fun q =>
      [cadjFactorPoly (transCoeff M q) (uIdx n k hk1 hk2) (vIdx n k hk2)])
  set Fva : List (MvPolynomial (Fin n) ℚ) :=
    (List.finRange M.numStates).flatMap (fun q =>
      [cadjFactorPoly (transCoeff M q) (vIdx n k hk2) (aIdx n k hk2)])
  set Finert : List (MvPolynomial (Fin n) ℚ) :=
    (List.finRange M.numStates).flatMap (fun q =>
      [cadjFactorPoly (transCoeff M q) (aIdx n k hk2) (bIdx n k hk2),
       cadjFactorPoly (transCoeff M q) (bIdx n k hk2) (rIdx n k hk2)])
  have hsplit1 :
      ((List.finRange M.numStates).flatMap (fun q =>
        ([cadjFactorPoly (transCoeff M q) (uIdx n k hk1 hk2) (vIdx n k hk2),
          cadjFactorPoly (transCoeff M q) (vIdx n k hk2) (aIdx n k hk2)] ++
         [cadjFactorPoly (transCoeff M q) (aIdx n k hk2) (bIdx n k hk2),
          cadjFactorPoly (transCoeff M q) (bIdx n k hk2) (rIdx n k hk2)]))).Perm
        (((List.finRange M.numStates).flatMap (fun q =>
          [cadjFactorPoly (transCoeff M q) (uIdx n k hk1 hk2) (vIdx n k hk2),
           cadjFactorPoly (transCoeff M q) (vIdx n k hk2) (aIdx n k hk2)])) ++
         Finert) := by
    simpa [Finert] using
      (List.flatMap_append_perm (List.finRange M.numStates)
        (fun q : Fin M.numStates =>
          [cadjFactorPoly (transCoeff M q) (uIdx n k hk1 hk2) (vIdx n k hk2),
           cadjFactorPoly (transCoeff M q) (vIdx n k hk2) (aIdx n k hk2)])
        (fun q : Fin M.numStates =>
          [cadjFactorPoly (transCoeff M q) (aIdx n k hk2) (bIdx n k hk2),
           cadjFactorPoly (transCoeff M q) (bIdx n k hk2) (rIdx n k hk2)])).symm
  have hsplit2 :
      ((List.finRange M.numStates).flatMap (fun q =>
          [cadjFactorPoly (transCoeff M q) (uIdx n k hk1 hk2) (vIdx n k hk2),
           cadjFactorPoly (transCoeff M q) (vIdx n k hk2) (aIdx n k hk2)])).Perm
        (Fuv ++ Fva) := by
    simpa [Fuv, Fva] using
      (List.flatMap_append_perm (List.finRange M.numStates)
        (fun q : Fin M.numStates =>
          [cadjFactorPoly (transCoeff M q) (uIdx n k hk1 hk2) (vIdx n k hk2)])
        (fun q : Fin M.numStates =>
          [cadjFactorPoly (transCoeff M q) (vIdx n k hk2) (aIdx n k hk2)])).symm
  have h0 :
      ((List.finRange M.numStates).flatMap (fun q =>
        [cadjFactorPoly (transCoeff M q) (uIdx n k hk1 hk2) (vIdx n k hk2),
         cadjFactorPoly (transCoeff M q) (vIdx n k hk2) (aIdx n k hk2),
         cadjFactorPoly (transCoeff M q) (aIdx n k hk2) (bIdx n k hk2),
         cadjFactorPoly (transCoeff M q) (bIdx n k hk2) (rIdx n k hk2)])).Perm
        ((Fuv ++ Fva) ++ Finert) := by
    refine hsplit1.trans ?_
    exact hsplit2.append_right Finert
  have hswap : ((Fuv ++ Fva) ++ Finert).Perm (Finert ++ Fuv ++ Fva) := by
    simpa [List.append_assoc] using
      (List.perm_append_comm (l₁ := Fuv ++ Fva) (l₂ := Finert))
  simpa [Fuv, Fva, Finert, List.append_assoc] using h0.trans hswap

theorem inert_active_explicit_form
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    inertFactorsList M n k hk1 hk2 ++ activeFactorsList M n k hk1 hk2 =
      ([boolFactorPoly n (aIdx n k hk2),
        boolFactorPoly n (bIdx n k hk2),
        cadjFactorPoly 1 (aIdx n k hk2) (bIdx n k hk2),
        cadjFactorPoly 1 (bIdx n k hk2) (rIdx n k hk2)] ++
       (List.finRange M.numStates).flatMap (fun q =>
         [cadjFactorPoly (transCoeff M q) (aIdx n k hk2) (bIdx n k hk2),
          cadjFactorPoly (transCoeff M q) (bIdx n k hk2) (rIdx n k hk2)])) ++
      (([cadjFactorPoly 1 (uIdx n k hk1 hk2) (vIdx n k hk2)] ++
        (List.finRange M.numStates).flatMap (fun q =>
          [cadjFactorPoly (transCoeff M q) (uIdx n k hk1 hk2) (vIdx n k hk2)])) ++
       ([boolFactorPoly n (vIdx n k hk2),
         cadjFactorPoly 1 (vIdx n k hk2) (aIdx n k hk2)] ++
        (List.finRange M.numStates).flatMap (fun q =>
          [cadjFactorPoly (transCoeff M q) (vIdx n k hk2) (aIdx n k hk2)]))) := by
  unfold inertFactorsList activeFactorsList activeUVFactorsList activeVAFactorsList
  rfl

theorem touchedListPoly_perm_partition
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    touchedListPoly_perm_partition_claim M n k hk1 hk2 := by
  unfold touchedListPoly_perm_partition_claim
  rw [BridgeAKappaTwoIdentityThreeStructural.touchedListPoly_explicit_form,
    inert_active_explicit_form]
  rw [prevSucc_eq_vIdx n k hk1 hk2]
  set Bv : MvPolynomial (Fin n) ℚ := boolFactorPoly n (vIdx n k hk2)
  set Ba : MvPolynomial (Fin n) ℚ := boolFactorPoly n (aIdx n k hk2)
  set Bb : MvPolynomial (Fin n) ℚ := boolFactorPoly n (bIdx n k hk2)
  set U0 : MvPolynomial (Fin n) ℚ :=
    cadjFactorPoly 1 (uIdx n k hk1 hk2) (vIdx n k hk2)
  set V0 : MvPolynomial (Fin n) ℚ :=
    cadjFactorPoly 1 (vIdx n k hk2) (aIdx n k hk2)
  set D0 : MvPolynomial (Fin n) ℚ :=
    cadjFactorPoly 1 (aIdx n k hk2) (bIdx n k hk2)
  set R0 : MvPolynomial (Fin n) ℚ :=
    cadjFactorPoly 1 (bIdx n k hk2) (rIdx n k hk2)
  set Fuv : List (MvPolynomial (Fin n) ℚ) :=
    (List.finRange M.numStates).flatMap (fun q =>
      [cadjFactorPoly (transCoeff M q) (uIdx n k hk1 hk2) (vIdx n k hk2)])
  set Fva : List (MvPolynomial (Fin n) ℚ) :=
    (List.finRange M.numStates).flatMap (fun q =>
      [cadjFactorPoly (transCoeff M q) (vIdx n k hk2) (aIdx n k hk2)])
  set Finert : List (MvPolynomial (Fin n) ℚ) :=
    (List.finRange M.numStates).flatMap (fun q =>
      [cadjFactorPoly (transCoeff M q) (aIdx n k hk2) (bIdx n k hk2),
       cadjFactorPoly (transCoeff M q) (bIdx n k hk2) (rIdx n k hk2)])
  have hflat :
      ((List.finRange M.numStates).flatMap (fun q =>
        [cadjFactorPoly (transCoeff M q) (uIdx n k hk1 hk2) (vIdx n k hk2),
         cadjFactorPoly (transCoeff M q) (vIdx n k hk2) (aIdx n k hk2),
         cadjFactorPoly (transCoeff M q) (aIdx n k hk2) (bIdx n k hk2),
         cadjFactorPoly (transCoeff M q) (bIdx n k hk2) (rIdx n k hk2)])).Perm
        (Finert ++ Fuv ++ Fva) := by
    simpa [Fuv, Fva, Finert] using
      transSkel_flatMap_perm_split_identityTwo M n k hk1 hk2
  have hhead :
      (([Bv, Ba, Bb] ++ [U0, V0, D0, R0]) ++ (Finert ++ Fuv ++ Fva)).Perm
        (([Ba, Bb, D0, R0] ++ Finert) ++
          (([U0] ++ Fuv) ++ ([Bv, V0] ++ Fva))) := by
    have step1 :
        ([Bv, Ba, Bb, U0, V0, D0, R0] : List (MvPolynomial (Fin n) ℚ)).Perm
          [Ba, Bb, D0, R0, U0, Bv, V0] := by
      -- A finite shuffle of the seven non-state factors.
      have s1 :
          ([Bv, Ba, Bb, U0, V0, D0, R0] : List (MvPolynomial (Fin n) ℚ)).Perm
            [Ba, Bb, U0, V0, D0, R0, Bv] := by
        simpa using (List.perm_append_comm
          (l₁ := [Bv]) (l₂ := [Ba, Bb, U0, V0, D0, R0]))
      have stail :
          ([U0, V0, D0, R0, Bv] : List (MvPolynomial (Fin n) ℚ)).Perm
            [D0, R0, U0, V0, Bv] := by
        have h :
            ((([U0, V0] : List (MvPolynomial (Fin n) ℚ)) ++ [D0, R0]) ++ [Bv]).Perm
              ((([D0, R0] : List (MvPolynomial (Fin n) ℚ)) ++ [U0, V0]) ++ [Bv]) :=
          (List.perm_append_comm
            (l₁ := ([U0, V0] : List (MvPolynomial (Fin n) ℚ)))
            (l₂ := [D0, R0])).append_right [Bv]
        simpa [List.append_assoc] using h
      have s2 :
          ([Ba, Bb, U0, V0, D0, R0, Bv] : List (MvPolynomial (Fin n) ℚ)).Perm
            [Ba, Bb, D0, R0, U0, V0, Bv] := by
        exact List.Perm.cons Ba (List.Perm.cons Bb stail)
      have s3 :
          ([Ba, Bb, D0, R0, U0, V0, Bv] : List (MvPolynomial (Fin n) ℚ)).Perm
            [Ba, Bb, D0, R0, U0, Bv, V0] := by
        apply List.Perm.cons
        apply List.Perm.cons
        apply List.Perm.cons
        apply List.Perm.cons
        apply List.Perm.cons
        exact List.Perm.swap _ _ _
      exact s1.trans (s2.trans s3)
    have step2 :
        (([Bv, Ba, Bb] ++ [U0, V0, D0, R0]) ++
            (Finert ++ Fuv ++ Fva)).Perm
          ([Ba, Bb, D0, R0, U0, Bv, V0] ++ (Finert ++ Fuv ++ Fva)) := by
      simpa using (step1.append_right (Finert ++ Fuv ++ Fva))
    refine step2.trans ?_
    have hmove :
        ([Ba, Bb, D0, R0, U0, Bv, V0] ++ (Finert ++ Fuv ++ Fva)).Perm
          (([Ba, Bb, D0, R0] ++ Finert) ++
            (([U0] ++ Fuv) ++ ([Bv, V0] ++ Fva))) := by
      have hswapU :
          (([U0, Bv, V0] : List (MvPolynomial (Fin n) ℚ)) ++ Finert).Perm
            (Finert ++ [U0, Bv, V0]) :=
        List.perm_append_comm
      have h1 :
          ([Ba, Bb, D0, R0] ++ ([U0, Bv, V0] ++ Finert) ++ (Fuv ++ Fva)).Perm
            ([Ba, Bb, D0, R0] ++ (Finert ++ [U0, Bv, V0]) ++ (Fuv ++ Fva)) :=
        (List.Perm.append_left [Ba, Bb, D0, R0] hswapU).append_right _
      have hsplit :
          ([U0, Bv, V0] ++ Fuv).Perm ([U0] ++ Fuv ++ [Bv, V0]) := by
        have hswap :
            (([Bv, V0] : List (MvPolynomial (Fin n) ℚ)) ++ Fuv).Perm
              (Fuv ++ [Bv, V0]) :=
          List.perm_append_comm
        simpa [List.append_assoc] using List.Perm.append_left [U0] hswap
      have h2 :
          ([Ba, Bb, D0, R0] ++ (Finert ++ [U0, Bv, V0]) ++ (Fuv ++ Fva)).Perm
            (([Ba, Bb, D0, R0] ++ Finert) ++
              (([U0] ++ Fuv) ++ ([Bv, V0] ++ Fva))) := by
        have hlift :
            (([Ba, Bb, D0, R0] ++ Finert) ++
              (([U0, Bv, V0] ++ Fuv) ++ Fva)).Perm
              (([Ba, Bb, D0, R0] ++ Finert) ++
                ((([U0] ++ Fuv) ++ [Bv, V0]) ++ Fva)) :=
          List.Perm.append_left ([Ba, Bb, D0, R0] ++ Finert)
            (hsplit.append_right Fva)
        simpa [List.append_assoc] using hlift
      simpa [List.append_assoc] using h1.trans h2
    exact hmove
  have hprefix :
      (([Bv, Ba, Bb] ++ [U0, V0, D0, R0]) ++
          ((List.finRange M.numStates).flatMap (fun q =>
            [cadjFactorPoly (transCoeff M q) (uIdx n k hk1 hk2) (vIdx n k hk2),
             cadjFactorPoly (transCoeff M q) (vIdx n k hk2) (aIdx n k hk2),
             cadjFactorPoly (transCoeff M q) (aIdx n k hk2) (bIdx n k hk2),
             cadjFactorPoly (transCoeff M q) (bIdx n k hk2) (rIdx n k hk2)]))).Perm
        (([Bv, Ba, Bb] ++ [U0, V0, D0, R0]) ++ (Finert ++ Fuv ++ Fva)) := by
    exact List.Perm.append_left _ hflat
  simpa [Bv, Ba, Bb, U0, V0, D0, R0, Fuv, Fva, Finert, List.append_assoc] using
    hprefix.trans hhead

theorem identityTwo_perPairSum_of_decomposition
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (hperm : touchedListPoly_perm_partition_claim M n k hk1 hk2)
    (hres : identityTwo_residualActiveClaim M n k hk1 hk2) :
    BridgeAKappaTwoIdentityTwo.identityTwo_perPairSum M n hn htb hns k hk1 hk2 := by
  unfold BridgeAKappaTwoIdentityTwo.identityTwo_perPairSum
  have hu := rowLeft_first_eq_uIdx n k hk1 hk2
  have hv := rowLeft_second_eq_vIdx n k hk2
  rw [hu, hv]
  have hpermSum :
      pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
        (BridgeAKappaTwoIdentityThreeStructural.touchedListPoly M n k hk1 hk2) =
      pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
        (inertFactorsList M n k hk1 hk2 ++ activeFactorsList M n k hk1 hk2) := by
    apply pderivListProdSumTwice_perm
    exact hperm
  have hinert :
      pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
        (inertFactorsList M n k hk1 hk2 ++ activeFactorsList M n k hk1 hk2) =
      (inertFactorsList M n k hk1 hk2).prod *
        pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
          (activeFactorsList M n k hk1 hk2) := by
    apply pderivListProdSumTwice_append_inert_prefix
    · intro f hf
      exact inertFactorsList_inert_at_u M n k hk1 hk2 f hf
    · intro f hf
      exact inertFactorsList_inert_at_v M n k hk1 hk2 f hf
  rw [← (show
      BridgeAKappaTwoIdentityThreeStructural.touchedListPoly M n k hk1 hk2 =
        (kappaTwoTouchedList_explicit M n k hk1 hk2).map
          (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly) from rfl)]
  rw [hpermSum, hinert]
  exact hres

/-! ## Section D: coefficient preservation and active split -/

theorem coeff_probeRight_bool_v_mul
    (n k : Nat) (hk2 : 3 * k + 3 < n)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeRight n k hk2)
        (boolFactorPoly n (vIdx n k hk2) * p) =
      MvPolynomial.coeff (probeRight n k hk2) p := by
  rw [probeRight_eq]
  exact coeff_X_a_X_b_boolFactorPoly_mul
    (aIdx n k hk2) (bIdx n k hk2) (vIdx n k hk2) p
    (fun h => vIdx_ne_aIdx n k hk2 h)
    (fun h => vIdx_ne_bIdx n k hk2 h)

theorem coeff_probeRight_cadj_u_v_mul
    (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (c : ℚ) (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeRight n k hk2)
        (cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2) * p) =
      MvPolynomial.coeff (probeRight n k hk2) p := by
  rw [probeRight_eq]
  exact coeff_X_a_X_b_cadjFactorPoly_mul_stray_fst
    (aIdx n k hk2) (bIdx n k hk2)
    (uIdx n k hk1 hk2) (vIdx n k hk2) c p
    (fun h => uIdx_ne_aIdx n k hk1 hk2 h)
    (fun h => uIdx_ne_bIdx n k hk1 hk2 h)

theorem coeff_probeRight_cadj_v_a_mul
    (n k : Nat) (hk2 : 3 * k + 3 < n)
    (c : ℚ) (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeRight n k hk2)
        (cadjFactorPoly c (vIdx n k hk2) (aIdx n k hk2) * p) =
      MvPolynomial.coeff (probeRight n k hk2) p := by
  rw [probeRight_eq]
  exact coeff_X_a_X_b_cadjFactorPoly_mul_stray_fst
    (aIdx n k hk2) (bIdx n k hk2)
    (vIdx n k hk2) (aIdx n k hk2) c p
    (fun h => vIdx_ne_aIdx n k hk2 h)
    (fun h => vIdx_ne_bIdx n k hk2 h)

theorem coeff_probeRight_cadj_b_r_mul
    (n k : Nat) (hk2 : 3 * k + 3 < n)
    (c : ℚ) (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeRight n k hk2)
        (cadjFactorPoly c (bIdx n k hk2) (rIdx n k hk2) * p) =
      MvPolynomial.coeff (probeRight n k hk2) p := by
  rw [probeRight_eq]
  exact coeff_X_a_X_b_cadjFactorPoly_mul_stray_snd
    (aIdx n k hk2) (bIdx n k hk2)
    (bIdx n k hk2) (rIdx n k hk2) c p
    (fun h => aIdx_ne_rIdx n k hk2 h.symm)
    (fun h => bIdx_ne_rIdx n k hk2 h.symm)

theorem activeVAFactorsList_forall_probe_preserve
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ activeVAFactorsList M n k hk1 hk2)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeRight n k hk2) (f * p) =
      MvPolynomial.coeff (probeRight n k hk2) p := by
  unfold activeVAFactorsList at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange] at hf
  rcases hf with ((rfl | rfl) | ⟨q, _hq, rfl⟩)
  · exact coeff_probeRight_bool_v_mul n k hk2 p
  · exact coeff_probeRight_cadj_v_a_mul n k hk2 1 p
  · exact coeff_probeRight_cadj_v_a_mul n k hk2 (transCoeff M q) p

theorem coeff_probeRight_activeVA_prod_mul
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeRight n k hk2)
        ((activeVAFactorsList M n k hk1 hk2).prod * p) =
      MvPolynomial.coeff (probeRight n k hk2) p := by
  rw [probeRight_eq]
  apply coeff_X_a_X_b_list_prod_mul_of_forall_preserve
  intro f hf p'
  rw [← probeRight_eq]
  exact activeVAFactorsList_forall_probe_preserve M n k hk1 hk2 f hf p'

theorem activeUVFactorsList_forall_probe_preserve
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ activeUVFactorsList M n k hk1 hk2)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeRight n k hk2) (f * p) =
      MvPolynomial.coeff (probeRight n k hk2) p := by
  unfold activeUVFactorsList at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange] at hf
  rcases hf with (rfl | ⟨q, _hq, rfl⟩)
  · exact coeff_probeRight_cadj_u_v_mul n k hk1 hk2 1 p
  · exact coeff_probeRight_cadj_u_v_mul n k hk1 hk2 (transCoeff M q) p

theorem coeff_probeRight_activeUV_prod_mul
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeRight n k hk2)
        ((activeUVFactorsList M n k hk1 hk2).prod * p) =
      MvPolynomial.coeff (probeRight n k hk2) p := by
  rw [probeRight_eq]
  apply coeff_X_a_X_b_list_prod_mul_of_forall_preserve
  intro f hf p'
  rw [← probeRight_eq]
  exact activeUVFactorsList_forall_probe_preserve M n k hk1 hk2 f hf p'

theorem activeVAFactorsList_inert_at_u
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ activeVAFactorsList M n k hk1 hk2) :
    MvPolynomial.pderiv (uIdx n k hk1 hk2) f = 0 := by
  unfold activeVAFactorsList at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange] at hf
  rcases hf with ((rfl | rfl) | ⟨q, _hq, rfl⟩)
  · exact pderiv_one_sub_boolLC_factor_of_ne (vIdx n k hk2)
      (uIdx n k hk1 hk2) (uIdx_ne_vIdx n k hk1 hk2)
  · exact pderiv_one_sub_C_X_mul_X_at_other 1
      (vIdx n k hk2) (aIdx n k hk2) (uIdx n k hk1 hk2)
      (uIdx_ne_vIdx n k hk1 hk2) (uIdx_ne_aIdx n k hk1 hk2)
  · exact pderiv_one_sub_C_X_mul_X_at_other (transCoeff M q)
      (vIdx n k hk2) (aIdx n k hk2) (uIdx n k hk1 hk2)
      (uIdx_ne_vIdx n k hk1 hk2) (uIdx_ne_aIdx n k hk1 hk2)

theorem pderivListProdSum_u_activeVA_eq_zero
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    pderivListProdSum (uIdx n k hk1 hk2)
      (activeVAFactorsList M n k hk1 hk2) = 0 :=
  pderivListProdSum_eq_zero_of_all_inert (uIdx n k hk1 hk2)
    (activeVAFactorsList M n k hk1 hk2)
    (activeVAFactorsList_inert_at_u M n k hk1 hk2)

theorem pderivListProdSumTwice_activeVA_eq_zero
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
      (activeVAFactorsList M n k hk1 hk2) = 0 := by
  unfold pderivListProdSumTwice
  rw [pderivListProdSum_u_activeVA_eq_zero M n k hk1 hk2]
  exact map_zero _

theorem pderivListProdSumTwice_activeFactors_decompose
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
        (activeFactorsList M n k hk1 hk2) =
      pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
          (activeUVFactorsList M n k hk1 hk2) *
        (activeVAFactorsList M n k hk1 hk2).prod
      + pderivListProdSum (uIdx n k hk1 hk2)
          (activeUVFactorsList M n k hk1 hk2) *
        pderivListProdSum (vIdx n k hk2)
          (activeVAFactorsList M n k hk1 hk2) := by
  unfold activeFactorsList
  rw [pderivListProdSumTwice_append]
  rw [pderivListProdSum_u_activeVA_eq_zero M n k hk1 hk2]
  rw [pderivListProdSumTwice_activeVA_eq_zero M n k hk1 hk2]
  ring

theorem activeUVFactorsList_pderiv_u_has_X_v_factor
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ activeUVFactorsList M n k hk1 hk2) :
    ∃ q : MvPolynomial (Fin n) ℚ,
      MvPolynomial.pderiv (uIdx n k hk1 hk2) f =
        MvPolynomial.X (vIdx n k hk2) * q := by
  unfold activeUVFactorsList at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange] at hf
  rcases hf with (rfl | ⟨q, _hq, rfl⟩)
  · refine ⟨-(MvPolynomial.C (1 : ℚ)), ?_⟩
    rw [pderiv_one_sub_C_X_mul_X_at_fst]
    · ring
    · exact uIdx_ne_vIdx n k hk1 hk2
  · refine ⟨-(MvPolynomial.C (transCoeff M q)), ?_⟩
    rw [pderiv_one_sub_C_X_mul_X_at_fst]
    · ring
    · exact uIdx_ne_vIdx n k hk1 hk2

theorem pderivListProdSum_u_activeUV_has_X_v_factor
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    ∃ q : MvPolynomial (Fin n) ℚ,
      pderivListProdSum (uIdx n k hk1 hk2)
          (activeUVFactorsList M n k hk1 hk2) =
        MvPolynomial.X (vIdx n k hk2) * q :=
  pderivListProdSum_has_X_factor_of_forall
    (vIdx n k hk2) (uIdx n k hk1 hk2)
    (activeUVFactorsList M n k hk1 hk2)
    (activeUVFactorsList_pderiv_u_has_X_v_factor M n k hk1 hk2)

theorem coeff_probeRight_active_crossTerm_zero
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (probeRight n k hk2)
        ((inertFactorsList M n k hk1 hk2).prod *
          (pderivListProdSum (uIdx n k hk1 hk2)
              (activeUVFactorsList M n k hk1 hk2) *
            pderivListProdSum (vIdx n k hk2)
              (activeVAFactorsList M n k hk1 hk2))) = 0 := by
  obtain ⟨q, hq⟩ :=
    pderivListProdSum_u_activeUV_has_X_v_factor M n k hk1 hk2
  rw [hq]
  have hreassoc :
      ((inertFactorsList M n k hk1 hk2).prod *
          (MvPolynomial.X (vIdx n k hk2) * q *
            pderivListProdSum (vIdx n k hk2)
              (activeVAFactorsList M n k hk1 hk2)) :
        MvPolynomial (Fin n) ℚ) =
      MvPolynomial.X (vIdx n k hk2) *
        ((inertFactorsList M n k hk1 hk2).prod *
          (q * pderivListProdSum (vIdx n k hk2)
            (activeVAFactorsList M n k hk1 hk2))) := by
    ring
  rw [hreassoc, probeRight_eq]
  exact
    coeff_X_a_X_b_X_u_mul_zero
      (aIdx n k hk2) (bIdx n k hk2) (vIdx n k hk2)
      ((inertFactorsList M n k hk1 hk2).prod *
        (q * pderivListProdSum (vIdx n k hk2)
          (activeVAFactorsList M n k hk1 hk2)))
      (fun h => vIdx_ne_aIdx n k hk2 h)
      (fun h => vIdx_ne_bIdx n k hk2 h)

theorem coeff_probeRight_activeFactors_reduce_to_UV
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (probeRight n k hk2)
        ((inertFactorsList M n k hk1 hk2).prod *
          pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
            (activeFactorsList M n k hk1 hk2)) =
      MvPolynomial.coeff (probeRight n k hk2)
        ((inertFactorsList M n k hk1 hk2).prod *
          (pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
              (activeUVFactorsList M n k hk1 hk2) *
            (activeVAFactorsList M n k hk1 hk2).prod)) := by
  rw [pderivListProdSumTwice_activeFactors_decompose M n k hk1 hk2]
  have hdistrib :
      ((inertFactorsList M n k hk1 hk2).prod *
          (pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
              (activeUVFactorsList M n k hk1 hk2) *
            (activeVAFactorsList M n k hk1 hk2).prod
          + pderivListProdSum (uIdx n k hk1 hk2)
              (activeUVFactorsList M n k hk1 hk2) *
            pderivListProdSum (vIdx n k hk2)
              (activeVAFactorsList M n k hk1 hk2)) :
        MvPolynomial (Fin n) ℚ) =
      (inertFactorsList M n k hk1 hk2).prod *
        (pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
            (activeUVFactorsList M n k hk1 hk2) *
          (activeVAFactorsList M n k hk1 hk2).prod)
      + (inertFactorsList M n k hk1 hk2).prod *
        (pderivListProdSum (uIdx n k hk1 hk2)
            (activeUVFactorsList M n k hk1 hk2) *
          pderivListProdSum (vIdx n k hk2)
            (activeVAFactorsList M n k hk1 hk2)) := by
    ring
  rw [hdistrib, MvPolynomial.coeff_add]
  rw [coeff_probeRight_active_crossTerm_zero M n k hk1 hk2]
  ring

/-! ## Section E: inert-product coefficient -/

theorem inertFactorsList_forall_coeff_zero_one
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ inertFactorsList M n k hk1 hk2) :
    MvPolynomial.coeff 0 f = 1 := by
  unfold inertFactorsList at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange] at hf
  rcases hf with ((rfl | rfl | rfl | rfl) | ⟨q, _hq, rfl | rfl⟩)
  · exact coeff_zero_boolFactorPoly _
  · exact coeff_zero_boolFactorPoly _
  · exact coeff_zero_cadjFactorPoly 1 _ _
  · exact coeff_zero_cadjFactorPoly 1 _ _
  · exact coeff_zero_cadjFactorPoly (transCoeff M q) _ _
  · exact coeff_zero_cadjFactorPoly (transCoeff M q) _ _

theorem coeff_zero_inertFactorsList_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff 0 (inertFactorsList M n k hk1 hk2).prod = 1 :=
  ListProdDerivativeConstantCoeff.coeff_zero_list_prod_eq_one_of_forall
    (inertFactorsList M n k hk1 hk2)
    (inertFactorsList_forall_coeff_zero_one M n k hk1 hk2)

theorem coeff_probeRight_cadj_a_b_mul
    (n k : Nat) (hk2 : 3 * k + 3 < n)
    (c : ℚ) (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeRight n k hk2)
        (cadjFactorPoly c (aIdx n k hk2) (bIdx n k hk2) * p) =
      -c * MvPolynomial.coeff 0 p +
        MvPolynomial.coeff (probeRight n k hk2) p := by
  rw [probeRight_eq]
  have hab : aIdx n k hk2 ≠ bIdx n k hk2 := aIdx_ne_bIdx n k hk2
  rw [coeff_X_v_X_w_cadjFactorPoly_mul c
    (aIdx n k hk2) (bIdx n k hk2)
    (aIdx n k hk2) (bIdx n k hk2) p hab hab]
  have ha :
      MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
        (cadjFactorPoly c (aIdx n k hk2) (bIdx n k hk2)) = 0 := by
    exact coeff_X_a_one_sub_C_X_mul_X
      (aIdx n k hk2) (aIdx n k hk2) (bIdx n k hk2) hab c
  have hb :
      MvPolynomial.coeff (Finsupp.single (bIdx n k hk2) 1)
        (cadjFactorPoly c (aIdx n k hk2) (bIdx n k hk2)) = 0 := by
    exact coeff_X_a_one_sub_C_X_mul_X
      (bIdx n k hk2) (aIdx n k hk2) (bIdx n k hk2) hab c
  have hprobe :
      MvPolynomial.coeff
          (Finsupp.single (aIdx n k hk2) 1 + Finsupp.single (bIdx n k hk2) 1)
          (cadjFactorPoly c (aIdx n k hk2) (bIdx n k hk2)) = -c := by
    rw [coeff_X_v_X_w_cadjFactorPoly c
      (aIdx n k hk2) (bIdx n k hk2)
      (aIdx n k hk2) (bIdx n k hk2) hab hab]
    simp
  have hzero :
      MvPolynomial.coeff 0
          (cadjFactorPoly c (aIdx n k hk2) (bIdx n k hk2)) = 1 :=
    coeff_zero_cadjFactorPoly c (aIdx n k hk2) (bIdx n k hk2)
  rw [ha, hb, hprobe, hzero]
  ring

theorem coeff_probeRight_cadj_a_b_mul_of_coeff_zero_one
    (n k : Nat) (hk2 : 3 * k + 3 < n)
    (c : ℚ) (p : MvPolynomial (Fin n) ℚ)
    (hp0 : MvPolynomial.coeff 0 p = 1) :
    MvPolynomial.coeff (probeRight n k hk2)
        (cadjFactorPoly c (aIdx n k hk2) (bIdx n k hk2) * p) =
      MvPolynomial.coeff (probeRight n k hk2) p - c := by
  rw [coeff_probeRight_cadj_a_b_mul n k hk2 c p, hp0]
  ring

noncomputable def transABFactorsListFrom
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (qs : List (Fin M.numStates)) : List (MvPolynomial (Fin n) ℚ) :=
  qs.flatMap (fun q =>
    [cadjFactorPoly (transCoeff M q) (aIdx n k hk2) (bIdx n k hk2)])

theorem transABFactorsListFrom_forall_coeff_zero_one
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (qs : List (Fin M.numStates))
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ transABFactorsListFrom M n k hk2 qs) :
    MvPolynomial.coeff 0 f = 1 := by
  unfold transABFactorsListFrom at hf
  simp only [List.mem_flatMap, List.mem_singleton] at hf
  obtain ⟨q, _hq, rfl⟩ := hf
  exact coeff_zero_cadjFactorPoly (transCoeff M q) _ _

theorem coeff_zero_transABFactorsListFrom_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (qs : List (Fin M.numStates)) :
    MvPolynomial.coeff 0 (transABFactorsListFrom M n k hk2 qs).prod = 1 :=
  ListProdDerivativeConstantCoeff.coeff_zero_list_prod_eq_one_of_forall
    (transABFactorsListFrom M n k hk2 qs)
    (transABFactorsListFrom_forall_coeff_zero_one M n k hk2 qs)

theorem coeff_probeRight_transABFactorsListFrom_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (qs : List (Fin M.numStates)) :
    MvPolynomial.coeff (probeRight n k hk2)
        (transABFactorsListFrom M n k hk2 qs).prod =
      -((qs.map (fun q => transCoeff M q)).sum) := by
  induction qs with
  | nil =>
      unfold transABFactorsListFrom
      simp [probeRight_eq, coeff_two_mono_one]
  | cons q qs ih =>
      change MvPolynomial.coeff (probeRight n k hk2)
          ((cadjFactorPoly (transCoeff M q)
              (aIdx n k hk2) (bIdx n k hk2) ::
            transABFactorsListFrom M n k hk2 qs).prod) =
        -(((q :: qs).map (fun q => transCoeff M q)).sum)
      rw [List.prod_cons]
      rw [coeff_probeRight_cadj_a_b_mul_of_coeff_zero_one n k hk2
        (transCoeff M q) (transABFactorsListFrom M n k hk2 qs).prod
        (coeff_zero_transABFactorsListFrom_prod M n k hk2 qs)]
      rw [ih]
      simp only [List.map_cons, List.sum_cons]
      ring

noncomputable def directABFactorsList
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n) :
    List (MvPolynomial (Fin n) ℚ) :=
  [cadjFactorPoly 1 (aIdx n k hk2) (bIdx n k hk2)] ++
    transABFactorsListFrom M n k hk2 (List.finRange M.numStates)

theorem coeff_probeRight_directABFactorsList_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (probeRight n k hk2)
        (directABFactorsList M n k hk2).prod =
      -(1 + transCoeffSum M) := by
  unfold directABFactorsList
  change MvPolynomial.coeff (probeRight n k hk2)
      ((cadjFactorPoly 1 (aIdx n k hk2) (bIdx n k hk2) ::
        transABFactorsListFrom M n k hk2 (List.finRange M.numStates)).prod) =
    -(1 + transCoeffSum M)
  rw [List.prod_cons]
  rw [coeff_probeRight_cadj_a_b_mul_of_coeff_zero_one n k hk2 1
    (transABFactorsListFrom M n k hk2 (List.finRange M.numStates)).prod
    (coeff_zero_transABFactorsListFrom_prod M n k hk2 (List.finRange M.numStates))]
  rw [coeff_probeRight_transABFactorsListFrom_prod]
  rw [transCoeff_finRange_list_sum]
  ring

theorem coeff_probeRight_bool_a_bool_b_prod
    (n k : Nat) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (probeRight n k hk2)
        (boolFactorPoly n (aIdx n k hk2) *
          boolFactorPoly n (bIdx n k hk2)) = 1 := by
  rw [probeRight_eq]
  have hab : aIdx n k hk2 ≠ bIdx n k hk2 := aIdx_ne_bIdx n k hk2
  rw [coeff_two_mono_mul (aIdx n k hk2) (bIdx n k hk2) hab]
  rw [coeff_single_boolFactorPoly (aIdx n k hk2) (aIdx n k hk2)]
  rw [coeff_single_boolFactorPoly (bIdx n k hk2) (bIdx n k hk2)]
  rw [coeff_single_boolFactorPoly (bIdx n k hk2) (aIdx n k hk2)]
  rw [coeff_single_boolFactorPoly (aIdx n k hk2) (bIdx n k hk2)]
  rw [coeff_X_v_X_w_boolFactorPoly (aIdx n k hk2)
    (aIdx n k hk2) (bIdx n k hk2) hab]
  rw [coeff_zero_boolFactorPoly (aIdx n k hk2)]
  rw [coeff_X_v_X_w_boolFactorPoly (bIdx n k hk2)
    (aIdx n k hk2) (bIdx n k hk2) hab]
  rw [coeff_zero_boolFactorPoly (bIdx n k hk2)]
  simp [hab, hab.symm]

theorem coeff_zero_bool_a_bool_b_prod
    (n k : Nat) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff 0
        (boolFactorPoly n (aIdx n k hk2) *
          boolFactorPoly n (bIdx n k hk2)) = 1 := by
  have h :=
    ListProdDerivativeConstantCoeff.coeff_zero_list_prod_eq_one_of_forall
      ([boolFactorPoly n (aIdx n k hk2),
        boolFactorPoly n (bIdx n k hk2)] :
          List (MvPolynomial (Fin n) ℚ))
      (by
        intro f hf
        simp at hf
        rcases hf with rfl | rfl
        · exact coeff_zero_boolFactorPoly _
        · exact coeff_zero_boolFactorPoly _)
  simpa using h

theorem directABFactorsList_forall_coeff_zero_one
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ directABFactorsList M n k hk2) :
    MvPolynomial.coeff 0 f = 1 := by
  unfold directABFactorsList at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | hf
  · exact coeff_zero_cadjFactorPoly 1 _ _
  · exact transABFactorsListFrom_forall_coeff_zero_one
      M n k hk2 (List.finRange M.numStates) f hf

theorem coeff_zero_directABFactorsList_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff 0 (directABFactorsList M n k hk2).prod = 1 :=
  ListProdDerivativeConstantCoeff.coeff_zero_list_prod_eq_one_of_forall
    (directABFactorsList M n k hk2)
    (directABFactorsList_forall_coeff_zero_one M n k hk2)

theorem directABFactorsList_forall_coeff_single_zero
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (v : Fin n) (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ directABFactorsList M n k hk2) :
    MvPolynomial.coeff (Finsupp.single v 1) f = 0 := by
  unfold directABFactorsList at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | hf
  · exact coeff_X_a_one_sub_C_X_mul_X
      v (aIdx n k hk2) (bIdx n k hk2)
      (aIdx_ne_bIdx n k hk2) 1
  · unfold transABFactorsListFrom at hf
    simp only [List.mem_flatMap, List.mem_singleton] at hf
    obtain ⟨q, _hq, rfl⟩ := hf
    exact coeff_X_a_one_sub_C_X_mul_X
      v (aIdx n k hk2) (bIdx n k hk2)
      (aIdx_ne_bIdx n k hk2) (transCoeff M q)

theorem coeff_single_directABFactorsList_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (v : Fin n) :
    MvPolynomial.coeff (Finsupp.single v 1)
      (directABFactorsList M n k hk2).prod = 0 :=
  coeff_single_list_prod_eq_zero_of_forall v
    (directABFactorsList M n k hk2)
    (directABFactorsList_forall_coeff_single_zero M n k hk2 v)

theorem coeff_probeRight_boolPair_directAB_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (probeRight n k hk2)
        ((boolFactorPoly n (aIdx n k hk2) *
            boolFactorPoly n (bIdx n k hk2)) *
          (directABFactorsList M n k hk2).prod) =
      -transCoeffSum M := by
  rw [probeRight_eq]
  have hab : aIdx n k hk2 ≠ bIdx n k hk2 := aIdx_ne_bIdx n k hk2
  rw [coeff_two_mono_mul (aIdx n k hk2) (bIdx n k hk2) hab]
  rw [coeff_single_directABFactorsList_prod M n k hk2 (bIdx n k hk2)]
  rw [coeff_single_directABFactorsList_prod M n k hk2 (aIdx n k hk2)]
  have hbool := coeff_probeRight_bool_a_bool_b_prod n k hk2
  rw [probeRight_eq] at hbool
  rw [hbool]
  rw [coeff_zero_directABFactorsList_prod M n k hk2]
  rw [coeff_zero_bool_a_bool_b_prod n k hk2]
  have hdirect := coeff_probeRight_directABFactorsList_prod M n k hk2
  rw [probeRight_eq] at hdirect
  rw [hdirect]
  ring

noncomputable def rightBRFactorsListFrom
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (qs : List (Fin M.numStates)) : List (MvPolynomial (Fin n) ℚ) :=
  qs.flatMap (fun q =>
    [cadjFactorPoly (transCoeff M q) (bIdx n k hk2) (rIdx n k hk2)])

noncomputable def rightBRFactorsList
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n) :
    List (MvPolynomial (Fin n) ℚ) :=
  [cadjFactorPoly 1 (bIdx n k hk2) (rIdx n k hk2)] ++
    rightBRFactorsListFrom M n k hk2 (List.finRange M.numStates)

theorem rightBRFactorsList_forall_probe_preserve
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ rightBRFactorsList M n k hk2)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeRight n k hk2) (f * p) =
      MvPolynomial.coeff (probeRight n k hk2) p := by
  unfold rightBRFactorsList rightBRFactorsListFrom at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange] at hf
  rcases hf with rfl | ⟨q, _hq, rfl⟩
  · exact coeff_probeRight_cadj_b_r_mul n k hk2 1 p
  · exact coeff_probeRight_cadj_b_r_mul n k hk2 (transCoeff M q) p

theorem coeff_probeRight_rightBRFactorsList_prod_mul
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeRight n k hk2)
        ((rightBRFactorsList M n k hk2).prod * p) =
      MvPolynomial.coeff (probeRight n k hk2) p := by
  rw [probeRight_eq]
  apply coeff_X_a_X_b_list_prod_mul_of_forall_preserve
  intro f hf p'
  rw [← probeRight_eq]
  exact rightBRFactorsList_forall_probe_preserve M n k hk2 f hf p'

private theorem inertTrans_flatMap_perm_split_identityTwo
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n) :
    ((List.finRange M.numStates).flatMap (fun q =>
        [cadjFactorPoly (transCoeff M q) (aIdx n k hk2) (bIdx n k hk2),
         cadjFactorPoly (transCoeff M q) (bIdx n k hk2) (rIdx n k hk2)])).Perm
      (transABFactorsListFrom M n k hk2 (List.finRange M.numStates) ++
       rightBRFactorsListFrom M n k hk2 (List.finRange M.numStates)) := by
  unfold transABFactorsListFrom rightBRFactorsListFrom
  exact (List.flatMap_append_perm (List.finRange M.numStates)
    (fun q : Fin M.numStates =>
      [cadjFactorPoly (transCoeff M q) (aIdx n k hk2) (bIdx n k hk2)])
    (fun q : Fin M.numStates =>
      [cadjFactorPoly (transCoeff M q) (bIdx n k hk2) (rIdx n k hk2)])).symm

theorem inertFactorsList_perm_right_base
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    (inertFactorsList M n k hk1 hk2).Perm
      (rightBRFactorsList M n k hk2 ++
        ([boolFactorPoly n (aIdx n k hk2),
          boolFactorPoly n (bIdx n k hk2)] ++
          directABFactorsList M n k hk2)) := by
  unfold inertFactorsList rightBRFactorsList directABFactorsList
  set Ba : MvPolynomial (Fin n) ℚ := boolFactorPoly n (aIdx n k hk2)
  set Bb : MvPolynomial (Fin n) ℚ := boolFactorPoly n (bIdx n k hk2)
  set D0 : MvPolynomial (Fin n) ℚ :=
    cadjFactorPoly 1 (aIdx n k hk2) (bIdx n k hk2)
  set R0 : MvPolynomial (Fin n) ℚ :=
    cadjFactorPoly 1 (bIdx n k hk2) (rIdx n k hk2)
  set FD : List (MvPolynomial (Fin n) ℚ) :=
    transABFactorsListFrom M n k hk2 (List.finRange M.numStates)
  set FR : List (MvPolynomial (Fin n) ℚ) :=
    rightBRFactorsListFrom M n k hk2 (List.finRange M.numStates)
  have hflat :
      ((List.finRange M.numStates).flatMap (fun q =>
        [cadjFactorPoly (transCoeff M q) (aIdx n k hk2) (bIdx n k hk2),
         cadjFactorPoly (transCoeff M q) (bIdx n k hk2) (rIdx n k hk2)])).Perm
        (FD ++ FR) := by
    simpa [FD, FR] using inertTrans_flatMap_perm_split_identityTwo M n k hk2
  refine (List.Perm.append_left [Ba, Bb, D0, R0] hflat).trans ?_
  have hmoveR :
      (([Ba, Bb, D0, R0] : List (MvPolynomial (Fin n) ℚ)) ++ (FD ++ FR)).Perm
        ([R0] ++ (FR ++ [Ba, Bb, D0]) ++ FD) := by
    have hfront :
        (([Ba, Bb, D0, R0] : List (MvPolynomial (Fin n) ℚ)) ++ (FD ++ FR)).Perm
          (R0 :: (([Ba, Bb, D0] : List (MvPolynomial (Fin n) ℚ)) ++ (FD ++ FR))) := by
      simpa [List.append_assoc] using
        (List.perm_middle (l₁ := ([Ba, Bb, D0] : List (MvPolynomial (Fin n) ℚ)))
          (a := R0) (l₂ := FD ++ FR))
    have htail :
        (([Ba, Bb, D0] : List (MvPolynomial (Fin n) ℚ)) ++ (FD ++ FR)).Perm
          ((FR ++ [Ba, Bb, D0]) ++ FD) := by
      simpa [List.append_assoc] using
        (List.perm_append_comm
          (l₁ := ([Ba, Bb, D0] : List (MvPolynomial (Fin n) ℚ)) ++ FD)
          (l₂ := FR))
    exact hfront.trans (by
      simpa [List.append_assoc] using (List.Perm.cons R0 htail))
  simpa [FD, FR, List.append_assoc] using hmoveR

theorem coeff_probeRight_inertFactorsList_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (probeRight n k hk2)
        (inertFactorsList M n k hk1 hk2).prod =
      -transCoeffSum M := by
  have hperm := inertFactorsList_perm_right_base M n k hk1 hk2
  rw [List.Perm.prod_eq hperm]
  rw [List.prod_append]
  rw [coeff_probeRight_rightBRFactorsList_prod_mul M n k hk2]
  have hbase :
      (([boolFactorPoly n (aIdx n k hk2),
          boolFactorPoly n (bIdx n k hk2)] ++
          directABFactorsList M n k hk2).prod :
        MvPolynomial (Fin n) ℚ) =
        (boolFactorPoly n (aIdx n k hk2) *
          boolFactorPoly n (bIdx n k hk2)) *
          (directABFactorsList M n k hk2).prod := by
    simp
    ring
  rw [hbase]
  exact coeff_probeRight_boolPair_directAB_prod M n k hk2

/-! ## Section F: self-term state sum -/

noncomputable def uvFactorsFromCoeffs
    (n : Nat) (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) : List (MvPolynomial (Fin n) ℚ) :=
  cs.map (fun c =>
    cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2))

@[simp] theorem uvFactorsFromCoeffs_nil
    (n : Nat) (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    uvFactorsFromCoeffs n k hk1 hk2 [] = [] := by
  unfold uvFactorsFromCoeffs
  rfl

@[simp] theorem uvFactorsFromCoeffs_cons
    (n : Nat) (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (c : ℚ) (cs : List ℚ) :
    uvFactorsFromCoeffs n k hk1 hk2 (c :: cs) =
      cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2) ::
      uvFactorsFromCoeffs n k hk1 hk2 cs := by
  unfold uvFactorsFromCoeffs
  rfl

theorem activeUVFactorsList_eq_uvFactorsFromCoeffs
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    activeUVFactorsList M n k hk1 hk2 =
      uvFactorsFromCoeffs n k hk1 hk2
        (1 :: (List.finRange M.numStates).map (fun q => transCoeff M q)) := by
  unfold activeUVFactorsList uvFactorsFromCoeffs
  simp only [List.map_cons, List.singleton_append, List.map_map]
  have htail := List.flatMap_pure_eq_map
    (fun q : Fin M.numStates =>
      cadjFactorPoly (transCoeff M q)
        (uIdx n k hk1 hk2) (vIdx n k hk2))
    (List.finRange M.numStates)
  simpa [Function.comp_def] using
    congrArg
      (fun t =>
        cadjFactorPoly 1 (uIdx n k hk1 hk2) (vIdx n k hk2) :: t)
      htail

theorem uvFactorsFromCoeffs_forall_probe_preserve
    (n : Nat) (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ uvFactorsFromCoeffs n k hk1 hk2 cs)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeRight n k hk2) (f * p) =
      MvPolynomial.coeff (probeRight n k hk2) p := by
  unfold uvFactorsFromCoeffs at hf
  simp only [List.mem_map] at hf
  obtain ⟨c, _hc, rfl⟩ := hf
  exact coeff_probeRight_cadj_u_v_mul n k hk1 hk2 c p

theorem coeff_probeRight_uvFactorsFromCoeffs_prod_mul
    (n : Nat) (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeRight n k hk2)
        ((uvFactorsFromCoeffs n k hk1 hk2 cs).prod * p) =
      MvPolynomial.coeff (probeRight n k hk2) p := by
  rw [probeRight_eq]
  apply coeff_X_a_X_b_list_prod_mul_of_forall_preserve
  intro f hf p'
  rw [← probeRight_eq]
  exact uvFactorsFromCoeffs_forall_probe_preserve n k hk1 hk2 cs f hf p'

theorem coeff_probeRight_inert_VA_uvFactorsFromCoeffs_twice
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff (probeRight n k hk2)
        ((inertFactorsList M n k hk1 hk2).prod *
          (pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
              (uvFactorsFromCoeffs n k hk1 hk2 cs) *
            (activeVAFactorsList M n k hk1 hk2).prod)) =
      cs.sum * transCoeffSum M := by
  induction cs with
  | nil =>
      rw [uvFactorsFromCoeffs_nil, pderivListProdSumTwice_nil]
      simp
  | cons c cs ih =>
      rw [uvFactorsFromCoeffs_cons]
      rw [pderivListProdSumTwice_cons]
      have huv : uIdx n k hk1 hk2 ≠ vIdx n k hk2 := uIdx_ne_vIdx n k hk1 hk2
      rw [pderiv_w_pderiv_v_one_sub_C_X_mul_X_ij c
        (uIdx n k hk1 hk2) (vIdx n k hk2) huv]
      rw [pderiv_one_sub_C_X_mul_X_at_fst c
        (uIdx n k hk1 hk2) (vIdx n k hk2) huv]
      rw [pderiv_one_sub_C_X_mul_X_at_snd c
        (uIdx n k hk1 hk2) (vIdx n k hk2) huv]
      have hdistrib :
          ((inertFactorsList M n k hk1 hk2).prod *
              (((-(MvPolynomial.C c)) *
                    (uvFactorsFromCoeffs n k hk1 hk2 cs).prod
                  + (-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
                    MvPolynomial.pderiv (vIdx n k hk2)
                      (uvFactorsFromCoeffs n k hk1 hk2 cs).prod
                  + (-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk1 hk2))) *
                    pderivListProdSum (uIdx n k hk1 hk2)
                      (uvFactorsFromCoeffs n k hk1 hk2 cs)
                  + cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2) *
                    pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
                      (uvFactorsFromCoeffs n k hk1 hk2 cs)) *
                (activeVAFactorsList M n k hk1 hk2).prod) :
            MvPolynomial (Fin n) ℚ) =
          (inertFactorsList M n k hk1 hk2).prod *
              ((-(MvPolynomial.C c)) *
                (uvFactorsFromCoeffs n k hk1 hk2 cs).prod *
                (activeVAFactorsList M n k hk1 hk2).prod)
            + (inertFactorsList M n k hk1 hk2).prod *
              (((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
                MvPolynomial.pderiv (vIdx n k hk2)
                  (uvFactorsFromCoeffs n k hk1 hk2 cs).prod) *
                (activeVAFactorsList M n k hk1 hk2).prod)
            + (inertFactorsList M n k hk1 hk2).prod *
              (((-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk1 hk2))) *
                pderivListProdSum (uIdx n k hk1 hk2)
                  (uvFactorsFromCoeffs n k hk1 hk2 cs)) *
                (activeVAFactorsList M n k hk1 hk2).prod)
            + (inertFactorsList M n k hk1 hk2).prod *
              ((cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2) *
                pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
                  (uvFactorsFromCoeffs n k hk1 hk2 cs)) *
                (activeVAFactorsList M n k hk1 hk2).prod) := by
        ring
      rw [hdistrib]
      rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add]
      have hdiag :
          MvPolynomial.coeff (probeRight n k hk2)
            ((inertFactorsList M n k hk1 hk2).prod *
              ((-(MvPolynomial.C c)) *
                (uvFactorsFromCoeffs n k hk1 hk2 cs).prod *
                (activeVAFactorsList M n k hk1 hk2).prod)) =
            c * transCoeffSum M := by
        have hreassoc :
            ((inertFactorsList M n k hk1 hk2).prod *
              ((-(MvPolynomial.C c)) *
                (uvFactorsFromCoeffs n k hk1 hk2 cs).prod *
                (activeVAFactorsList M n k hk1 hk2).prod) :
              MvPolynomial (Fin n) ℚ) =
            MvPolynomial.C (-c) *
              ((uvFactorsFromCoeffs n k hk1 hk2 cs).prod *
                ((activeVAFactorsList M n k hk1 hk2).prod *
                  (inertFactorsList M n k hk1 hk2).prod)) := by
          rw [map_neg]
          ring
        rw [hreassoc, MvPolynomial.coeff_C_mul]
        rw [coeff_probeRight_uvFactorsFromCoeffs_prod_mul n k hk1 hk2 cs]
        rw [coeff_probeRight_activeVA_prod_mul M n k hk1 hk2]
        rw [coeff_probeRight_inertFactorsList_prod M n k hk1 hk2]
        ring
      have hcrossV :
          MvPolynomial.coeff (probeRight n k hk2)
            ((inertFactorsList M n k hk1 hk2).prod *
              (((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
                MvPolynomial.pderiv (vIdx n k hk2)
                  (uvFactorsFromCoeffs n k hk1 hk2 cs).prod) *
                (activeVAFactorsList M n k hk1 hk2).prod)) = 0 := by
        have hreassoc :
            ((inertFactorsList M n k hk1 hk2).prod *
              (((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
                MvPolynomial.pderiv (vIdx n k hk2)
                  (uvFactorsFromCoeffs n k hk1 hk2 cs).prod) *
                (activeVAFactorsList M n k hk1 hk2).prod) :
              MvPolynomial (Fin n) ℚ) =
            MvPolynomial.X (vIdx n k hk2) *
              (-(MvPolynomial.C c) *
                ((inertFactorsList M n k hk1 hk2).prod *
                  (MvPolynomial.pderiv (vIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk1 hk2 cs).prod *
                    (activeVAFactorsList M n k hk1 hk2).prod))) := by
          ring
        rw [hreassoc, probeRight_eq]
        exact
          coeff_X_a_X_b_X_u_mul_zero
            (aIdx n k hk2) (bIdx n k hk2) (vIdx n k hk2)
            (-(MvPolynomial.C c) *
              ((inertFactorsList M n k hk1 hk2).prod *
                (MvPolynomial.pderiv (vIdx n k hk2)
                  (uvFactorsFromCoeffs n k hk1 hk2 cs).prod *
                  (activeVAFactorsList M n k hk1 hk2).prod)))
            (fun h => vIdx_ne_aIdx n k hk2 h)
            (fun h => vIdx_ne_bIdx n k hk2 h)
      have hcrossU :
          MvPolynomial.coeff (probeRight n k hk2)
            ((inertFactorsList M n k hk1 hk2).prod *
              (((-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk1 hk2))) *
                pderivListProdSum (uIdx n k hk1 hk2)
                  (uvFactorsFromCoeffs n k hk1 hk2 cs)) *
                (activeVAFactorsList M n k hk1 hk2).prod)) = 0 := by
        have hreassoc :
            ((inertFactorsList M n k hk1 hk2).prod *
              (((-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk1 hk2))) *
                pderivListProdSum (uIdx n k hk1 hk2)
                  (uvFactorsFromCoeffs n k hk1 hk2 cs)) *
                (activeVAFactorsList M n k hk1 hk2).prod) :
              MvPolynomial (Fin n) ℚ) =
            MvPolynomial.X (uIdx n k hk1 hk2) *
              (-(MvPolynomial.C c) *
                ((inertFactorsList M n k hk1 hk2).prod *
                  (pderivListProdSum (uIdx n k hk1 hk2)
                    (uvFactorsFromCoeffs n k hk1 hk2 cs) *
                    (activeVAFactorsList M n k hk1 hk2).prod))) := by
          ring
        rw [hreassoc, probeRight_eq]
        exact
          coeff_X_a_X_b_X_u_mul_zero
            (aIdx n k hk2) (bIdx n k hk2) (uIdx n k hk1 hk2)
            (-(MvPolynomial.C c) *
              ((inertFactorsList M n k hk1 hk2).prod *
                (pderivListProdSum (uIdx n k hk1 hk2)
                  (uvFactorsFromCoeffs n k hk1 hk2 cs) *
                  (activeVAFactorsList M n k hk1 hk2).prod)))
            (fun h => uIdx_ne_aIdx n k hk1 hk2 h)
            (fun h => uIdx_ne_bIdx n k hk1 hk2 h)
      have hrec :
          MvPolynomial.coeff (probeRight n k hk2)
            ((inertFactorsList M n k hk1 hk2).prod *
              ((cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2) *
                pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
                  (uvFactorsFromCoeffs n k hk1 hk2 cs)) *
                (activeVAFactorsList M n k hk1 hk2).prod)) =
            cs.sum * transCoeffSum M := by
        have hreassoc :
            ((inertFactorsList M n k hk1 hk2).prod *
              ((cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2) *
                pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
                  (uvFactorsFromCoeffs n k hk1 hk2 cs)) *
                (activeVAFactorsList M n k hk1 hk2).prod) :
              MvPolynomial (Fin n) ℚ) =
            cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2) *
              ((inertFactorsList M n k hk1 hk2).prod *
                (pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
                  (uvFactorsFromCoeffs n k hk1 hk2 cs) *
                  (activeVAFactorsList M n k hk1 hk2).prod)) := by
          ring
        rw [hreassoc]
        rw [coeff_probeRight_cadj_u_v_mul n k hk1 hk2 c]
        exact ih
      rw [hdiag, hcrossV, hcrossU, hrec]
      simp only [List.sum_cons]
      ring

theorem identityTwo_residualActiveClaim_holds
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    identityTwo_residualActiveClaim M n k hk1 hk2 := by
  unfold identityTwo_residualActiveClaim
  rw [coeff_probeRight_activeFactors_reduce_to_UV M n k hk1 hk2]
  rw [activeUVFactorsList_eq_uvFactorsFromCoeffs M n k hk1 hk2]
  rw [coeff_probeRight_inert_VA_uvFactorsFromCoeffs_twice M n k hk1 hk2]
  simp only [List.sum_cons]
  rw [transCoeff_finRange_list_sum M]
  unfold crossBlockKValue
  ring

theorem identityTwo_perPairSum
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    BridgeAKappaTwoIdentityTwo.identityTwo_perPairSum
      M n hn htb hns k hk1 hk2 :=
  identityTwo_perPairSum_of_decomposition
    M n hn htb hns k hk1 hk2
    (touchedListPoly_perm_partition M n k hk1 hk2)
    (identityTwo_residualActiveClaim_holds M n k hk1 hk2)

theorem kappaTwoIdentityTwo
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (probeRight n k hk2)
        (mlProj (iterDerivList (rowLeft n k hk1 hk2)
          (cookLevinLocalBlockQ M n hn htb hns
            ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
      crossBlockKValue (transCoeffSum M) :=
  BridgeAKappaTwoIdentityTwo.kappaTwoIdentityTwo
    M n hn htb hns k hk1 hk2
    (identityTwo_perPairSum M n hn htb hns k hk1 hk2)

/-! ## Axiom audit anchors -/

#print axioms touchedListPoly_perm_partition
#print axioms identityTwo_residualActiveClaim_holds
#print axioms identityTwo_perPairSum
#print axioms kappaTwoIdentityTwo

end BridgeAKappaTwoIdentityTwoResidualActive

end PallLean.Paper93.Paper283
