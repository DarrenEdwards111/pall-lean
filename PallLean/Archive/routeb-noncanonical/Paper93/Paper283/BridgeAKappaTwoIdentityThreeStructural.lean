import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityThreeAux
import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityTwoAux
import PallLean.Paper93.Paper283.BridgeAKappaTwoListInductionHelpers

/-!
# Structural reduction for identity (3) per-pair sum

This file applies the inert-prefix/suffix pass-through machinery from
`BridgeAKappaTwoListInductionHelpers` to the identity-(3) setting,
peeling off every "fully-inert" factor in the touched-list.

## Identity (3) data

* `u = uIdx = ⟨3*k+2, _⟩`  (first differentiation index)
* `v = vIdx = ⟨3*k+3, _⟩`  (second differentiation index)
* probe = `probeLeft = X_{3k} · X_{3k+1}`

A factor is **inert under (u, v)** iff `pderiv u f = 0 ∧ pderiv v f = 0`.

By Family A (`pderiv_one_sub_boolLC_factor_of_ne`) and Family B
(`pderiv_one_sub_C_X_mul_X_at_other`), the inert factors among the
literal touched-list at an interior block (with `u = 3k+2`, `v = 3k+3`)
are exactly:

* **bool@3k**, **bool@3k+1**: derivatives at `(3k+2)` and `(3k+3)`
  vanish since neither index matches `3k` or `3k+1`.
* **adj@3k-1** (carries `X_{3k-1}, X_{3k}`): derivatives at `(3k+2)`
  and `(3k+3)` vanish since neither index matches `3k-1` or `3k`.
* **adj@3k** (carries `X_{3k}, X_{3k+1}`): derivatives at `(3k+2)` and
  `(3k+3)` vanish since neither index matches `3k` or `3k+1`.
* **trans@3k-1_q**, **trans@3k_q**: same as `adj` analogs.

The **active factors** are:

* **bool@3k+2** (∂_u ≠ 0, ∂_v = 0)
* **adj@3k+1** (∂_u ≠ 0, ∂_v = 0)
* **adj@3k+2** (∂_u ≠ 0, ∂_v ≠ 0)  ← supplies the self-term `-c = -1`
* **trans@3k+1_q**, **trans@3k+2_q**

## Hard rules
* No `sorry`.  No new axioms.
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
open BridgeAKappaTwoIdentityFour
open BridgeAKappaTwoIdentityThreeAux

open BridgeAKappaTwoListInductionHelpers

attribute [local instance] Classical.dec

namespace BridgeAKappaTwoIdentityThreeStructural

/-! ## Section A: per-factor inertness classification at `(u, v) = (3k+2, 3k+3)` -/

/-- bool@3k is inert at `(u, v) = (3k+2, 3k+3)`. -/
theorem bool_at_3k_inert
    (n k : Nat) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.pderiv (uIdx n k hk2)
        (boolFactorPoly n ⟨3 * k, by omega⟩) = 0 ∧
    MvPolynomial.pderiv (vIdx n k hk2)
        (boolFactorPoly n ⟨3 * k, by omega⟩) = 0 := by
  refine ⟨?_, ?_⟩
  · apply pderiv_one_sub_boolLC_factor_of_ne
    intro h
    have := congr_arg Fin.val h
    unfold uIdx at this
    simp at this
  · apply pderiv_one_sub_boolLC_factor_of_ne
    intro h
    have := congr_arg Fin.val h
    unfold vIdx at this
    simp at this

/-- bool@(3k+1) is inert at `(u, v) = (3k+2, 3k+3)`. -/
theorem bool_at_3k_plus_1_inert
    (n k : Nat) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.pderiv (uIdx n k hk2)
        (boolFactorPoly n ⟨3 * k + 1, by omega⟩) = 0 ∧
    MvPolynomial.pderiv (vIdx n k hk2)
        (boolFactorPoly n ⟨3 * k + 1, by omega⟩) = 0 := by
  refine ⟨?_, ?_⟩
  · apply pderiv_one_sub_boolLC_factor_of_ne
    intro h
    have := congr_arg Fin.val h
    unfold uIdx at this
    simp at this
  · apply pderiv_one_sub_boolLC_factor_of_ne
    intro h
    have := congr_arg Fin.val h
    unfold vIdx at this
    simp at this

/-- cadj@(3k-1, 3k) is inert at `(u, v) = (3k+2, 3k+3)` for any
coefficient `c`. -/
theorem cadj_at_3k_minus_1_inert
    (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) (c : ℚ) :
    MvPolynomial.pderiv (uIdx n k hk2)
        (cadjFactorPoly c
          (⟨3 * k - 1, by omega⟩ : Fin n)
          (⟨3 * k - 1 + 1, by omega⟩ : Fin n)) = 0 ∧
    MvPolynomial.pderiv (vIdx n k hk2)
        (cadjFactorPoly c
          (⟨3 * k - 1, by omega⟩ : Fin n)
          (⟨3 * k - 1 + 1, by omega⟩ : Fin n)) = 0 := by
  refine ⟨?_, ?_⟩
  · apply pderiv_one_sub_C_X_mul_X_at_other
    · intro h
      have := congr_arg Fin.val h
      unfold uIdx at this
      simp at this; omega
    · intro h
      have := congr_arg Fin.val h
      unfold uIdx at this
      simp at this
      omega
  · apply pderiv_one_sub_C_X_mul_X_at_other
    · intro h
      have := congr_arg Fin.val h
      unfold vIdx at this
      simp at this
      omega
    · intro h
      have := congr_arg Fin.val h
      unfold vIdx at this
      simp at this
      omega

/-- cadj@(3k, 3k+1) is inert at `(u, v) = (3k+2, 3k+3)` for any
coefficient `c`. -/
theorem cadj_at_3k_inert
    (n k : Nat) (hk2 : 3 * k + 3 < n) (c : ℚ) :
    MvPolynomial.pderiv (uIdx n k hk2)
        (cadjFactorPoly c
          (⟨3 * k, by omega⟩ : Fin n)
          (⟨3 * k + 1, by omega⟩ : Fin n)) = 0 ∧
    MvPolynomial.pderiv (vIdx n k hk2)
        (cadjFactorPoly c
          (⟨3 * k, by omega⟩ : Fin n)
          (⟨3 * k + 1, by omega⟩ : Fin n)) = 0 := by
  refine ⟨?_, ?_⟩
  · apply pderiv_one_sub_C_X_mul_X_at_other
    · intro h
      have := congr_arg Fin.val h
      unfold uIdx at this
      simp at this
    · intro h
      have := congr_arg Fin.val h
      unfold uIdx at this
      simp at this
  · apply pderiv_one_sub_C_X_mul_X_at_other
    · intro h
      have := congr_arg Fin.val h
      unfold vIdx at this
      simp at this
    · intro h
      have := congr_arg Fin.val h
      unfold vIdx at this
      simp at this

/-! ## Section B: active-factor derivative shapes -/

/-- bool@(3k+2): `pderiv u (bool@3k+2) = -1 + 2 X_{3k+2}` at `u = 3k+2`,
`pderiv v (bool@3k+2) = 0` at `v = 3k+3`. -/
theorem bool_at_3k_plus_2_active_at_u
    (n k : Nat) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.pderiv (uIdx n k hk2)
        (boolFactorPoly n ⟨3 * k + 2, by omega⟩) =
      -1 + 2 * MvPolynomial.X (uIdx n k hk2) := by
  unfold uIdx
  exact pderiv_one_sub_boolLC_factor_self ⟨3 * k + 2, by omega⟩

theorem bool_at_3k_plus_2_inert_at_v
    (n k : Nat) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.pderiv (vIdx n k hk2)
        (boolFactorPoly n ⟨3 * k + 2, by omega⟩) = 0 := by
  apply pderiv_one_sub_boolLC_factor_of_ne
  intro h
  have := congr_arg Fin.val h
  unfold vIdx at this
  simp at this

/-- cadj@(3k+1, 3k+2): `pderiv u f = -c · X_{3k+1}` at `u = 3k+2`,
`pderiv v f = 0` at `v = 3k+3`. -/
theorem cadj_at_3k_plus_1_active_at_u
    (n k : Nat) (hk2 : 3 * k + 3 < n) (c : ℚ) :
    MvPolynomial.pderiv (uIdx n k hk2)
        (cadjFactorPoly c
          (⟨3 * k + 1, by omega⟩ : Fin n)
          (⟨3 * k + 2, by omega⟩ : Fin n)) =
      -(MvPolynomial.C c * MvPolynomial.X (⟨3 * k + 1, by omega⟩ : Fin n)) := by
  have hij : (⟨3 * k + 1, by omega⟩ : Fin n) ≠ ⟨3 * k + 2, by omega⟩ := by
    intro h
    have := congr_arg Fin.val h
    simp at this
  have huidx : (uIdx n k hk2) = (⟨3 * k + 2, by omega⟩ : Fin n) := rfl
  rw [huidx]
  exact pderiv_one_sub_C_X_mul_X_at_snd c
    (⟨3 * k + 1, by omega⟩ : Fin n)
    (⟨3 * k + 2, by omega⟩ : Fin n) hij

theorem cadj_at_3k_plus_1_inert_at_v
    (n k : Nat) (hk2 : 3 * k + 3 < n) (c : ℚ) :
    MvPolynomial.pderiv (vIdx n k hk2)
        (cadjFactorPoly c
          (⟨3 * k + 1, by omega⟩ : Fin n)
          (⟨3 * k + 2, by omega⟩ : Fin n)) = 0 := by
  apply pderiv_one_sub_C_X_mul_X_at_other
  · intro h
    have := congr_arg Fin.val h
    unfold vIdx at this
    simp at this
  · intro h
    have := congr_arg Fin.val h
    unfold vIdx at this
    simp at this

/-- cadj@(3k+2, 3k+3): the *only* fully-active factor.
`pderiv u f = -c · X_{3k+3}` at `u = 3k+2`,
`pderiv v f = -c · X_{3k+2}` at `v = 3k+3`,
`pderiv v (pderiv u f) = -c`. -/
theorem cadj_at_3k_plus_2_active_at_u
    (n k : Nat) (hk2 : 3 * k + 3 < n) (c : ℚ) :
    MvPolynomial.pderiv (uIdx n k hk2)
        (cadjFactorPoly c
          (⟨3 * k + 2, by omega⟩ : Fin n)
          (⟨3 * k + 3, hk2⟩ : Fin n)) =
      -(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2)) := by
  have hij : (⟨3 * k + 2, by omega⟩ : Fin n) ≠ ⟨3 * k + 3, hk2⟩ := by
    intro h
    have := congr_arg Fin.val h
    simp at this
  have huidx : (uIdx n k hk2) = (⟨3 * k + 2, by omega⟩ : Fin n) := rfl
  have hvidx : (vIdx n k hk2) = (⟨3 * k + 3, hk2⟩ : Fin n) := rfl
  rw [huidx, hvidx]
  exact pderiv_one_sub_C_X_mul_X_at_fst c
    (⟨3 * k + 2, by omega⟩ : Fin n)
    (⟨3 * k + 3, hk2⟩ : Fin n) hij

theorem cadj_at_3k_plus_2_active_at_v
    (n k : Nat) (hk2 : 3 * k + 3 < n) (c : ℚ) :
    MvPolynomial.pderiv (vIdx n k hk2)
        (cadjFactorPoly c
          (⟨3 * k + 2, by omega⟩ : Fin n)
          (⟨3 * k + 3, hk2⟩ : Fin n)) =
      -(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk2)) := by
  have hij : (⟨3 * k + 2, by omega⟩ : Fin n) ≠ ⟨3 * k + 3, hk2⟩ := by
    intro h
    have := congr_arg Fin.val h
    simp at this
  have huidx : (uIdx n k hk2) = (⟨3 * k + 2, by omega⟩ : Fin n) := rfl
  have hvidx : (vIdx n k hk2) = (⟨3 * k + 3, hk2⟩ : Fin n) := rfl
  rw [huidx, hvidx]
  exact pderiv_one_sub_C_X_mul_X_at_snd c
    (⟨3 * k + 2, by omega⟩ : Fin n)
    (⟨3 * k + 3, hk2⟩ : Fin n) hij

/-- The **diagonal contribution** of cadj@(3k+2, 3k+3): `∂_v (∂_u f) = -c`. -/
theorem cadj_at_3k_plus_2_diagonal
    (n k : Nat) (hk2 : 3 * k + 3 < n) (c : ℚ) :
    MvPolynomial.pderiv (vIdx n k hk2)
        (MvPolynomial.pderiv (uIdx n k hk2)
          (cadjFactorPoly c
            (⟨3 * k + 2, by omega⟩ : Fin n)
            (⟨3 * k + 3, hk2⟩ : Fin n))) =
      -(MvPolynomial.C c) := by
  have hij : (⟨3 * k + 2, by omega⟩ : Fin n) ≠ ⟨3 * k + 3, hk2⟩ := by
    intro h
    have := congr_arg Fin.val h
    simp at this
  have huidx : (uIdx n k hk2) = (⟨3 * k + 2, by omega⟩ : Fin n) := rfl
  have hvidx : (vIdx n k hk2) = (⟨3 * k + 3, hk2⟩ : Fin n) := rfl
  rw [huidx, hvidx]
  exact pderiv_w_pderiv_v_one_sub_C_X_mul_X_ij c
    (⟨3 * k + 2, by omega⟩ : Fin n)
    (⟨3 * k + 3, hk2⟩ : Fin n) hij

/-! ## Section C: bool factors as a 3-list, splitting bool@3k+2 -/

/-- The bool factor list expansion at the interior block, after
`(1 - c.poly)` mapping: `[1 - boolLC_3k.poly, 1 - boolLC_{3k+1}.poly,
1 - boolLC_{3k+2}.poly]`. -/
theorem boolFactors_mapped_form
    (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    (kappaTwoTouchedList_boolFactors n k hk1 hk2).map
      (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly) =
      [boolFactorPoly n ⟨3 * k, by omega⟩,
       boolFactorPoly n ⟨3 * k + 1, by omega⟩,
       boolFactorPoly n ⟨3 * k + 2, by omega⟩] := by
  unfold kappaTwoTouchedList_boolFactors
  simp only [List.map_cons, List.map_nil]
  unfold boolFactorPoly
  show _ :: _ :: _ :: _ = _
  refine List.cons_eq_cons.mpr ⟨?_, ?_⟩
  · -- 1 - (boolLC n ⟨3*k, _⟩).poly = 1 - X_{3k} (1 - X_{3k})
    show (1 : MvPolynomial (Fin n) ℚ) - (boolLC n ⟨3 * k, by omega⟩).poly =
      (1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.X (⟨3 * k, by omega⟩ : Fin n) *
        ((1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.X (⟨3 * k, by omega⟩ : Fin n))
    rfl
  · refine List.cons_eq_cons.mpr ⟨?_, ?_⟩
    · rfl
    · refine List.cons_eq_cons.mpr ⟨?_, ?_⟩
      · rfl
      · rfl

/-! ## Axiom audit anchors -/

#print axioms bool_at_3k_inert
#print axioms bool_at_3k_plus_1_inert
#print axioms cadj_at_3k_minus_1_inert
#print axioms cadj_at_3k_inert
#print axioms bool_at_3k_plus_2_active_at_u
#print axioms bool_at_3k_plus_2_inert_at_v
#print axioms cadj_at_3k_plus_1_active_at_u
#print axioms cadj_at_3k_plus_1_inert_at_v
#print axioms cadj_at_3k_plus_2_active_at_u
#print axioms cadj_at_3k_plus_2_active_at_v
#print axioms cadj_at_3k_plus_2_diagonal
#print axioms boolFactors_mapped_form

end BridgeAKappaTwoIdentityThreeStructural

end PallLean.Paper93.Paper283

namespace PallLean.Paper93.Paper283

namespace BridgeAKappaTwoIdentityThreeStructural

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP
open BridgeABlockProductRule
open BridgeAKappaTwoTwoFoldLeibnizExpansion
open BridgeAKappaTwoFactorPairLemmas
open BridgeAKappaTwoIdentityOne
open BridgeAKappaTwoIdentityFour
open BridgeAKappaTwoIdentityThreeAux
open BridgeAKappaTwoListInductionHelpers

attribute [local instance] Classical.dec

/-! ## Section D: bool-prefix peel-off

The first two bool factors (`bool@3k`, `bool@3k+1`) are fully inert at
`(u, v) = (uIdx, vIdx)` (Section A).  By
`pderivListProdSumTwice_cons_inert` (from `IdentityTwoAux`), each can
be peeled off as a multiplicative prefix.
-/

/-- Pull `bool@3k` through the two-fold Leibniz sum. -/
theorem pull_bool_at_3k_through_pderivListProdSumTwice
    (n k : Nat) (hk2 : 3 * k + 3 < n)
    (rest : List (MvPolynomial (Fin n) ℚ)) :
    pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
        (boolFactorPoly n ⟨3 * k, by omega⟩ :: rest) =
      boolFactorPoly n ⟨3 * k, by omega⟩ *
        pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2) rest := by
  obtain ⟨hu, hv⟩ := bool_at_3k_inert n k hk2
  exact BridgeAKappaTwoIdentityTwoAux.pderivListProdSumTwice_cons_inert
    (uIdx n k hk2) (vIdx n k hk2)
    (boolFactorPoly n ⟨3 * k, by omega⟩) rest hu hv

/-- Pull `bool@3k+1` through the two-fold Leibniz sum. -/
theorem pull_bool_at_3k_plus_1_through_pderivListProdSumTwice
    (n k : Nat) (hk2 : 3 * k + 3 < n)
    (rest : List (MvPolynomial (Fin n) ℚ)) :
    pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
        (boolFactorPoly n ⟨3 * k + 1, by omega⟩ :: rest) =
      boolFactorPoly n ⟨3 * k + 1, by omega⟩ *
        pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2) rest := by
  obtain ⟨hu, hv⟩ := bool_at_3k_plus_1_inert n k hk2
  exact BridgeAKappaTwoIdentityTwoAux.pderivListProdSumTwice_cons_inert
    (uIdx n k hk2) (vIdx n k hk2)
    (boolFactorPoly n ⟨3 * k + 1, by omega⟩) rest hu hv

/-- Pull `cadj@(3k-1, 3k)` (with any coefficient `c`) through the
two-fold Leibniz sum. -/
theorem pull_cadj_at_3k_minus_1_through_pderivListProdSumTwice
    (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) (c : ℚ)
    (rest : List (MvPolynomial (Fin n) ℚ)) :
    pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
        (cadjFactorPoly c
          (⟨3 * k - 1, by omega⟩ : Fin n)
          (⟨3 * k - 1 + 1, by omega⟩ : Fin n) :: rest) =
      cadjFactorPoly c
        (⟨3 * k - 1, by omega⟩ : Fin n)
        (⟨3 * k - 1 + 1, by omega⟩ : Fin n) *
        pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2) rest := by
  obtain ⟨hu, hv⟩ := cadj_at_3k_minus_1_inert n k hk1 hk2 c
  exact BridgeAKappaTwoIdentityTwoAux.pderivListProdSumTwice_cons_inert
    (uIdx n k hk2) (vIdx n k hk2) _ rest hu hv

/-- Pull `cadj@(3k, 3k+1)` (with any coefficient `c`) through the
two-fold Leibniz sum. -/
theorem pull_cadj_at_3k_through_pderivListProdSumTwice
    (n k : Nat) (hk2 : 3 * k + 3 < n) (c : ℚ)
    (rest : List (MvPolynomial (Fin n) ℚ)) :
    pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
        (cadjFactorPoly c
          (⟨3 * k, by omega⟩ : Fin n)
          (⟨3 * k + 1, by omega⟩ : Fin n) :: rest) =
      cadjFactorPoly c
        (⟨3 * k, by omega⟩ : Fin n)
        (⟨3 * k + 1, by omega⟩ : Fin n) *
        pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2) rest := by
  obtain ⟨hu, hv⟩ := cadj_at_3k_inert n k hk2 c
  exact BridgeAKappaTwoIdentityTwoAux.pderivListProdSumTwice_cons_inert
    (uIdx n k hk2) (vIdx n k hk2) _ rest hu hv

/-! ## Section E: residual list after inert peel-off

After peeling all the inert factors at the front of the touched-list
(but before the active factors begin), what remains is a list of
"interspersed" factors where some are active and some are inert.

The cleanest encoding here is to apply `pderivListProdSumTwice_append`
on the touched-list re-grouping
`(allInertFactors) ++ (allActiveFactors)`, but this requires a list
permutation (which doesn't change `prod` but does change the recursive
structure of `pderivListProdSumTwice`).

We **avoid** the permutation by using `pderiv_pderiv_list_prod` to
re-ground both sides as `pderiv v (pderiv u (list.prod))`, which is
permutation-invariant (since `prod` is commutative).
-/

/-- The two-fold Leibniz sum is invariant under list permutations
(both sides equal `pderiv w (pderiv v (list.prod))`, and `prod` is
permutation-invariant in a commutative ring). -/
theorem pderivListProdSumTwice_perm
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]
    (v w : σ) (l₁ l₂ : List (MvPolynomial σ R))
    (hperm : l₁.Perm l₂) :
    pderivListProdSumTwice v w l₁ = pderivListProdSumTwice v w l₂ := by
  have h1 := pderiv_pderiv_list_prod (R := R) v w l₁
  have h2 := pderiv_pderiv_list_prod (R := R) v w l₂
  rw [← h1, ← h2]
  rw [List.Perm.prod_eq hperm]

/-! ## Axiom audit anchors -/

#print axioms pull_bool_at_3k_through_pderivListProdSumTwice
#print axioms pull_bool_at_3k_plus_1_through_pderivListProdSumTwice
#print axioms pull_cadj_at_3k_minus_1_through_pderivListProdSumTwice
#print axioms pull_cadj_at_3k_through_pderivListProdSumTwice
#print axioms pderivListProdSumTwice_perm

end BridgeAKappaTwoIdentityThreeStructural

end PallLean.Paper93.Paper283

namespace PallLean.Paper93.Paper283

namespace BridgeAKappaTwoIdentityThreeStructural

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP
open BridgeABlockProductRule
open BridgeAKappaTwoTwoFoldLeibnizExpansion
open BridgeAKappaTwoFactorPairLemmas
open BridgeAKappaTwoIdentityOne
open BridgeAKappaTwoIdentityFour
open BridgeAKappaTwoIdentityThreeAux
open BridgeAKappaTwoListInductionHelpers

attribute [local instance] Classical.dec

/-! ## Section F: factor partition for identity (3)

We construct two sub-lists of the literal touched-list (mapped through
`(1 - c.poly)`):

* `inertFactorsList` — collects all factors fully inert at
  `(u, v) = (uIdx, vIdx)`: `bool@3k`, `bool@3k+1`,
  `adj@3k-1`, `adj@3k`, and for each `q : Fin numStates`,
  `trans@3k-1_q`, `trans@3k_q`.
* `activeFactorsList` — the remaining factors:
  `bool@3k+2`, `adj@3k+1`, `adj@3k+2`, and for each `q`,
  `trans@3k+1_q`, `trans@3k+2_q`.

Both are subsets of the touched-list with the same `prod` (modulo
permutation). -/

/-- The "inert factors" list: all factors of the touched-list (mapped
through `1 - c.poly`) which are fully inert at `(uIdx, vIdx)`. -/
noncomputable def inertFactorsList
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    List (MvPolynomial (Fin n) ℚ) :=
  [boolFactorPoly n ⟨3 * k, by omega⟩,
   boolFactorPoly n ⟨3 * k + 1, by omega⟩,
   cadjFactorPoly 1 (⟨3 * k - 1, by omega⟩ : Fin n)
     (⟨3 * k - 1 + 1, by omega⟩ : Fin n),
   cadjFactorPoly 1 (⟨3 * k, by omega⟩ : Fin n)
     (⟨3 * k + 1, by omega⟩ : Fin n)] ++
  (List.finRange M.numStates).flatMap (fun q =>
    [cadjFactorPoly (transCoeff M q)
       (⟨3 * k - 1, by omega⟩ : Fin n)
       (⟨3 * k - 1 + 1, by omega⟩ : Fin n),
     cadjFactorPoly (transCoeff M q)
       (⟨3 * k, by omega⟩ : Fin n)
       (⟨3 * k + 1, by omega⟩ : Fin n)])

/-- The "active factors" list: complement of the inert list. -/
noncomputable def activeFactorsList
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    List (MvPolynomial (Fin n) ℚ) :=
  [boolFactorPoly n ⟨3 * k + 2, by omega⟩,
   cadjFactorPoly 1 (⟨3 * k + 1, by omega⟩ : Fin n)
     (⟨3 * k + 2, by omega⟩ : Fin n),
   cadjFactorPoly 1 (⟨3 * k + 2, by omega⟩ : Fin n)
     (⟨3 * k + 3, hk2⟩ : Fin n)] ++
  (List.finRange M.numStates).flatMap (fun q =>
    [cadjFactorPoly (transCoeff M q)
       (⟨3 * k + 1, by omega⟩ : Fin n)
       (⟨3 * k + 2, by omega⟩ : Fin n),
     cadjFactorPoly (transCoeff M q)
       (⟨3 * k + 2, by omega⟩ : Fin n)
       (⟨3 * k + 3, hk2⟩ : Fin n)])

/-- Every factor in `inertFactorsList` is inert under `pderiv (uIdx)`. -/
theorem inertFactorsList_inert_at_u
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ inertFactorsList M n k hk1 hk2) :
    MvPolynomial.pderiv (uIdx n k hk2) f = 0 := by
  unfold inertFactorsList at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange] at hf
  rcases hf with ((rfl | rfl | rfl | rfl) | ⟨q, _hq, rfl | rfl⟩)
  · exact (bool_at_3k_inert n k hk2).1
  · exact (bool_at_3k_plus_1_inert n k hk2).1
  · exact (cadj_at_3k_minus_1_inert n k hk1 hk2 1).1
  · exact (cadj_at_3k_inert n k hk2 1).1
  · exact (cadj_at_3k_minus_1_inert n k hk1 hk2 (transCoeff M q)).1
  · exact (cadj_at_3k_inert n k hk2 (transCoeff M q)).1

/-- Every factor in `inertFactorsList` is inert under `pderiv (vIdx)`. -/
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
  · exact (bool_at_3k_inert n k hk2).2
  · exact (bool_at_3k_plus_1_inert n k hk2).2
  · exact (cadj_at_3k_minus_1_inert n k hk1 hk2 1).2
  · exact (cadj_at_3k_inert n k hk2 1).2
  · exact (cadj_at_3k_minus_1_inert n k hk1 hk2 (transCoeff M q)).2
  · exact (cadj_at_3k_inert n k hk2 (transCoeff M q)).2

/-! ## Axiom audit anchors -/

#print axioms inertFactorsList_inert_at_u
#print axioms inertFactorsList_inert_at_v

end BridgeAKappaTwoIdentityThreeStructural

end PallLean.Paper93.Paper283

namespace PallLean.Paper93.Paper283

namespace BridgeAKappaTwoIdentityThreeStructural

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP
open BridgeABlockProductRule
open BridgeAKappaTwoTwoFoldLeibnizExpansion
open BridgeAKappaTwoFactorPairLemmas
open BridgeAKappaTwoIdentityOne
open BridgeAKappaTwoIdentityFour
open BridgeAKappaTwoIdentityThreeAux
open BridgeAKappaTwoListInductionHelpers

attribute [local instance] Classical.dec

/-! ## Section G: touched-list polynomial form

We expose the touched-list (mapped through `1 - c.poly`) directly as a
list of polynomial factors whose `prod` matches the partition
`inertFactorsList ++ activeFactorsList` permutationally.

The key invariants:
* The literal touched-list polynomial form contains exactly the same
  multiset of factors as `inertFactorsList ++ activeFactorsList`.
* Therefore the products are equal (since multiplication is commutative).

Note: we do **not** prove a `List.Perm` directly here because the order
of factors is irrelevant for our target (`pderivListProdSumTwice` is
permutation-invariant by `pderivListProdSumTwice_perm`).  Instead, we
exhibit the prod-equality, which suffices.
-/

/-- The mapped-touched-list polynomial form: the literal touched-list
under `(1 - c.poly)` mapping. -/
noncomputable def touchedListPoly
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    List (MvPolynomial (Fin n) ℚ) :=
  (kappaTwoTouchedList_explicit M n k hk1 hk2).map
    (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly)

/-- For convenience: the literal expansion of `touchedListPoly` at the
level of the bool factors.  (Decomposes the bool prefix.) -/
theorem touchedListPoly_eq_bool_prefix_append
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    touchedListPoly M n k hk1 hk2 =
      [boolFactorPoly n ⟨3 * k, by omega⟩,
       boolFactorPoly n ⟨3 * k + 1, by omega⟩,
       boolFactorPoly n ⟨3 * k + 2, by omega⟩] ++
      ((kappaTwoTouchedList_adjFactors n k hk1 hk2).map
        (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly) ++
       (kappaTwoTouchedList_transSkelFactorsFlat M n k hk1 hk2).map
        (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly)) := by
  unfold touchedListPoly kappaTwoTouchedList_explicit
  rw [List.map_append, List.map_append]
  rw [boolFactors_mapped_form]
  rw [List.append_assoc]

/-! ## Axiom audit anchors -/

#print axioms touchedListPoly_eq_bool_prefix_append

end BridgeAKappaTwoIdentityThreeStructural

end PallLean.Paper93.Paper283

namespace PallLean.Paper93.Paper283

namespace BridgeAKappaTwoIdentityThreeStructural

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP
open BridgeABlockProductRule
open BridgeAKappaTwoTwoFoldLeibnizExpansion
open BridgeAKappaTwoFactorPairLemmas
open BridgeAKappaTwoIdentityOne
open BridgeAKappaTwoIdentityFour
open BridgeAKappaTwoIdentityThreeAux
open BridgeAKappaTwoListInductionHelpers

attribute [local instance] Classical.dec

/-! ## Section H: residual-claim formalisation

Given the inert/active partition, identity (3)'s per-pair sum reduces
to the following claim: there exists a list `L_perm` permutationally
equivalent to the touched-list-polynomial form, with
`L_perm = inertFactorsList ++ activeFactorsList`, such that

  `coeff probeLeft (pderivListProdSumTwice u v L_perm)
   = inertFactorsList.prod *
     coeff probeLeft (pderivListProdSumTwice u v activeFactorsList)`

via `pderivListProdSumTwice_append_inert_prefix`.  Then by Section J's
cross-term vanishing applied to the active-list, only the
self-contribution from cadj@(3k+2, 3k+3) survives, summing to the
target `K`.

We state this as a clean residual lemma. -/

/-- Hypothesis encoding the multiset/permutation equivalence between
the literal touched-list (mapped through `1 - c.poly`) and the
inert/active partition.

This is the structural permutation claim that the inert and active
sub-lists together cover the touched-list with the correct multiset of
factors.  The proof requires expanding `kappaTwoTouchedList_explicit`
through `boolFactors`, `adjFactors`, `transSkelFactorsFlat`, and showing
each factor is matched to its inert/active counterpart by literal
coefficient comparison.  -/
def touchedListPoly_perm_partition_claim
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) : Prop :=
  (touchedListPoly M n k hk1 hk2).Perm
    (inertFactorsList M n k hk1 hk2 ++ activeFactorsList M n k hk1 hk2)

/-- Hypothesis encoding the active-list per-pair sum: the bilinear
coefficient at `probeLeft` of `pderivListProdSumTwice u v
activeFactorsList`, multiplied by the inert product, equals
`crossBlockKValue (transCoeffSum M)`.

This is the residual quantitative claim left after the structural
reductions of Sections D-G.  It is the analytic content, encoding the
self-term (cadj@(3k+2,3k+3) × prod-of-rest) + cross-term-vanishing
(Section J) computation. -/
def identityThree_residualActiveClaim
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) : Prop :=
  MvPolynomial.coeff (probeLeft n k hk2)
      ((inertFactorsList M n k hk1 hk2).prod *
        pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
          (activeFactorsList M n k hk1 hk2)) =
    crossBlockKValue (transCoeffSum M)

/-- **Identity (3) closure under the structural decomposition**: from
the permutation claim and the residual active claim,
`identityThree_perPairSum` follows. -/
theorem identityThree_perPairSum_of_decomposition
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (hperm : touchedListPoly_perm_partition_claim M n k hk1 hk2)
    (hres : identityThree_residualActiveClaim M n k hk1 hk2) :
    BridgeAKappaTwoIdentityThree.identityThree_perPairSum M n hn htb hns k hk1 hk2 := by
  unfold BridgeAKappaTwoIdentityThree.identityThree_perPairSum
  -- step 1: rewrite the touched-list-polynomial form via permutation
  have hpermSum : pderivListProdSumTwice
        (⟨3 * k + 2, by omega⟩ : Fin n)
        (⟨3 * k + 3, hk2⟩ : Fin n)
        (touchedListPoly M n k hk1 hk2) =
      pderivListProdSumTwice
        (⟨3 * k + 2, by omega⟩ : Fin n)
        (⟨3 * k + 3, hk2⟩ : Fin n)
        (inertFactorsList M n k hk1 hk2 ++ activeFactorsList M n k hk1 hk2) := by
    apply pderivListProdSumTwice_perm
    exact hperm
  -- show the touched-list polynomial form matches the literal map
  have htlp : touchedListPoly M n k hk1 hk2 =
    (kappaTwoTouchedList_explicit M n k hk1 hk2).map
      (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly) := rfl
  -- step 2: rewrite using the inert prefix collapse
  have hinert :
    pderivListProdSumTwice
        (⟨3 * k + 2, by omega⟩ : Fin n)
        (⟨3 * k + 3, hk2⟩ : Fin n)
        (inertFactorsList M n k hk1 hk2 ++ activeFactorsList M n k hk1 hk2) =
      (inertFactorsList M n k hk1 hk2).prod *
        pderivListProdSumTwice
          (⟨3 * k + 2, by omega⟩ : Fin n)
          (⟨3 * k + 3, hk2⟩ : Fin n)
          (activeFactorsList M n k hk1 hk2) := by
    apply pderivListProdSumTwice_append_inert_prefix
    · intro f hf
      have h := inertFactorsList_inert_at_u M n k hk1 hk2 f hf
      change MvPolynomial.pderiv (uIdx n k hk2) f = 0 at h
      unfold uIdx at h
      exact h
    · intro f hf
      have h := inertFactorsList_inert_at_v M n k hk1 hk2 f hf
      change MvPolynomial.pderiv (vIdx n k hk2) f = 0 at h
      unfold vIdx at h
      exact h
  -- step 3: combine with the residual claim
  rw [← htlp]
  rw [hpermSum, hinert]
  exact hres

/-! ## Axiom audit anchors -/

#print axioms identityThree_perPairSum_of_decomposition

end BridgeAKappaTwoIdentityThreeStructural

end PallLean.Paper93.Paper283

namespace PallLean.Paper93.Paper283

namespace BridgeAKappaTwoIdentityThreeStructural

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP
open BridgeABlockProductRule
open BridgeAKappaTwoTwoFoldLeibnizExpansion
open BridgeAKappaTwoFactorPairLemmas
open BridgeAKappaTwoIdentityOne
open BridgeAKappaTwoIdentityFour
open BridgeAKappaTwoIdentityThreeAux
open BridgeAKappaTwoListInductionHelpers

attribute [local instance] Classical.dec

/-! ## Section I: poly-form normalisation lemmas

The literal touched-list `kappaTwoTouchedList_explicit` is built from
`boolLC`, `adjLC`, and `transSkelLC` constraints; after the
`(fun c => 1 - c.poly)` mapping, each constraint factor becomes the
corresponding `boolFactorPoly` / `cadjFactorPoly` term used in
`inertFactorsList` / `activeFactorsList`.  These three small lemmas
make that conversion explicit. -/

/-- `1 - (boolLC n a).poly` syntactically reduces to `boolFactorPoly n a`. -/
theorem one_sub_boolLC_poly_eq_boolFactorPoly
    (n : ℕ) (a : Fin n) :
    (1 : MvPolynomial (Fin n) ℚ) - (boolLC n a).poly = boolFactorPoly n a := rfl

/-- `1 - (adjLC n i hi).poly = cadjFactorPoly 1 i ⟨i.val + 1, hi⟩`. -/
theorem one_sub_adjLC_poly_eq_cadjFactorPoly
    {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) :
    (1 : MvPolynomial (Fin n) ℚ) - (adjLC n i hi).poly =
      cadjFactorPoly 1 i ⟨i.val + 1, hi⟩ := by
  unfold cadjFactorPoly
  rw [MvPolynomial.C_1, one_mul]
  rfl

/-- `1 - (transSkelLC M n q i hi).poly = cadjFactorPoly (transCoeff M q) i ⟨i.val + 1, hi⟩`. -/
theorem one_sub_transSkelLC_poly_eq_cadjFactorPoly
    (M : TuringMachine.DTM) {n : ℕ} (q : Fin M.numStates)
    (i : Fin n) (hi : i.val + 1 < n) :
    (1 : MvPolynomial (Fin n) ℚ) - (transSkelLC M n q i hi).poly =
      cadjFactorPoly (transCoeff M q) i ⟨i.val + 1, hi⟩ := rfl

/-! ## Section J: explicit literal forms after `(fun c => 1 - c.poly)` mapping

We expand the `adjFactors` and `transSkelFactorsForState` sub-lists
under the polynomial mapping, mirroring the existing
`boolFactors_mapped_form` (Section C). -/

/-- The mapped adjacency factor list is exactly the literal length-4 list
of `cadjFactorPoly 1` factors. -/
theorem adjFactors_mapped_form
    (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    (kappaTwoTouchedList_adjFactors n k hk1 hk2).map
      (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly) =
      [cadjFactorPoly 1 (⟨3 * k - 1, by omega⟩ : Fin n)
          (⟨3 * k - 1 + 1, by omega⟩ : Fin n),
       cadjFactorPoly 1 (⟨3 * k, by omega⟩ : Fin n)
          (⟨3 * k + 1, by omega⟩ : Fin n),
       cadjFactorPoly 1 (⟨3 * k + 1, by omega⟩ : Fin n)
          (⟨3 * k + 2, by omega⟩ : Fin n),
       cadjFactorPoly 1 (⟨3 * k + 2, by omega⟩ : Fin n)
          (⟨3 * k + 3, hk2⟩ : Fin n)] := by
  unfold kappaTwoTouchedList_adjFactors
  simp only [List.map_cons, List.map_nil,
    one_sub_adjLC_poly_eq_cadjFactorPoly]

/-- The mapped per-state transition-skeleton list is exactly the literal
length-4 list of `cadjFactorPoly (transCoeff M q)` factors. -/
theorem transSkelFactorsForState_mapped_form
    (M : TuringMachine.DTM) (n : Nat) (q : Fin M.numStates)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    (kappaTwoTouchedList_transSkelFactorsForState M n q k hk1 hk2).map
      (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly) =
      [cadjFactorPoly (transCoeff M q)
         (⟨3 * k - 1, by omega⟩ : Fin n)
         (⟨3 * k - 1 + 1, by omega⟩ : Fin n),
       cadjFactorPoly (transCoeff M q)
         (⟨3 * k, by omega⟩ : Fin n)
         (⟨3 * k + 1, by omega⟩ : Fin n),
       cadjFactorPoly (transCoeff M q)
         (⟨3 * k + 1, by omega⟩ : Fin n)
         (⟨3 * k + 2, by omega⟩ : Fin n),
       cadjFactorPoly (transCoeff M q)
         (⟨3 * k + 2, by omega⟩ : Fin n)
         (⟨3 * k + 3, hk2⟩ : Fin n)] := by
  unfold kappaTwoTouchedList_transSkelFactorsForState
  simp only [List.map_cons, List.map_nil,
    one_sub_transSkelLC_poly_eq_cadjFactorPoly]

end BridgeAKappaTwoIdentityThreeStructural

end PallLean.Paper93.Paper283

namespace PallLean.Paper93.Paper283

namespace BridgeAKappaTwoIdentityThreeStructural

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP
open BridgeABlockProductRule
open BridgeAKappaTwoTwoFoldLeibnizExpansion
open BridgeAKappaTwoFactorPairLemmas
open BridgeAKappaTwoIdentityOne
open BridgeAKappaTwoIdentityFour
open BridgeAKappaTwoIdentityThreeAux
open BridgeAKappaTwoListInductionHelpers

attribute [local instance] Classical.dec

/-! ## Section K: canonical "explicit" form of `touchedListPoly`

Combining the three `_mapped_form` lemmas, `touchedListPoly` equals
the canonical concatenation
`bool ++ adj ++ flatMap_q transSkelForState_q`, where every constraint
has been replaced by its `boolFactorPoly` / `cadjFactorPoly` equivalent.
-/

/-- The mapped flattened transition-skeleton list as a single `flatMap`
over the per-state literal cadj lists. -/
theorem transSkelFactorsFlat_mapped_form
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    (kappaTwoTouchedList_transSkelFactorsFlat M n k hk1 hk2).map
      (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly) =
      (List.finRange M.numStates).flatMap (fun q =>
        [cadjFactorPoly (transCoeff M q)
           (⟨3 * k - 1, by omega⟩ : Fin n)
           (⟨3 * k - 1 + 1, by omega⟩ : Fin n),
         cadjFactorPoly (transCoeff M q)
           (⟨3 * k, by omega⟩ : Fin n)
           (⟨3 * k + 1, by omega⟩ : Fin n),
         cadjFactorPoly (transCoeff M q)
           (⟨3 * k + 1, by omega⟩ : Fin n)
           (⟨3 * k + 2, by omega⟩ : Fin n),
         cadjFactorPoly (transCoeff M q)
           (⟨3 * k + 2, by omega⟩ : Fin n)
           (⟨3 * k + 3, hk2⟩ : Fin n)]) := by
  unfold kappaTwoTouchedList_transSkelFactorsFlat
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro q _hq
  exact transSkelFactorsForState_mapped_form M n q k hk1 hk2

/-- The canonical "explicit" form of `touchedListPoly`: an explicit
length-7 head followed by a `flatMap` of length-4 per-state cadj lists. -/
theorem touchedListPoly_explicit_form
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    touchedListPoly M n k hk1 hk2 =
      ([boolFactorPoly n ⟨3 * k, by omega⟩,
        boolFactorPoly n ⟨3 * k + 1, by omega⟩,
        boolFactorPoly n ⟨3 * k + 2, by omega⟩] ++
       [cadjFactorPoly 1 (⟨3 * k - 1, by omega⟩ : Fin n)
           (⟨3 * k - 1 + 1, by omega⟩ : Fin n),
        cadjFactorPoly 1 (⟨3 * k, by omega⟩ : Fin n)
           (⟨3 * k + 1, by omega⟩ : Fin n),
        cadjFactorPoly 1 (⟨3 * k + 1, by omega⟩ : Fin n)
           (⟨3 * k + 2, by omega⟩ : Fin n),
        cadjFactorPoly 1 (⟨3 * k + 2, by omega⟩ : Fin n)
           (⟨3 * k + 3, hk2⟩ : Fin n)]) ++
      (List.finRange M.numStates).flatMap (fun q =>
        [cadjFactorPoly (transCoeff M q)
           (⟨3 * k - 1, by omega⟩ : Fin n)
           (⟨3 * k - 1 + 1, by omega⟩ : Fin n),
         cadjFactorPoly (transCoeff M q)
           (⟨3 * k, by omega⟩ : Fin n)
           (⟨3 * k + 1, by omega⟩ : Fin n),
         cadjFactorPoly (transCoeff M q)
           (⟨3 * k + 1, by omega⟩ : Fin n)
           (⟨3 * k + 2, by omega⟩ : Fin n),
         cadjFactorPoly (transCoeff M q)
           (⟨3 * k + 2, by omega⟩ : Fin n)
           (⟨3 * k + 3, hk2⟩ : Fin n)]) := by
  unfold touchedListPoly kappaTwoTouchedList_explicit
  rw [List.map_append, List.map_append]
  rw [boolFactors_mapped_form, adjFactors_mapped_form,
      transSkelFactorsFlat_mapped_form]

end BridgeAKappaTwoIdentityThreeStructural

end PallLean.Paper93.Paper283

namespace PallLean.Paper93.Paper283

namespace BridgeAKappaTwoIdentityThreeStructural

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP
open BridgeABlockProductRule
open BridgeAKappaTwoTwoFoldLeibnizExpansion
open BridgeAKappaTwoFactorPairLemmas
open BridgeAKappaTwoIdentityOne
open BridgeAKappaTwoIdentityFour
open BridgeAKappaTwoIdentityThreeAux
open BridgeAKappaTwoListInductionHelpers

attribute [local instance] Classical.dec

/-! ## Section L: canonical "explicit" form of `inertFactorsList ++ activeFactorsList`

We expand the inert/active partition into a parallel canonical
length-4 + length-3 + per-state cadj structure, ready for direct
permutation comparison with `touchedListPoly_explicit_form`. -/

/-- The inert + active partition expressed as a parallel concatenation
form: `(inert_bool ++ inert_adj ++ flatMap_q inert_trans_q) ++
(active_bool ++ active_adj ++ flatMap_q active_trans_q)`. -/
theorem inert_active_explicit_form
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    inertFactorsList M n k hk1 hk2 ++ activeFactorsList M n k hk1 hk2 =
      ([boolFactorPoly n ⟨3 * k, by omega⟩,
        boolFactorPoly n ⟨3 * k + 1, by omega⟩,
        cadjFactorPoly 1 (⟨3 * k - 1, by omega⟩ : Fin n)
           (⟨3 * k - 1 + 1, by omega⟩ : Fin n),
        cadjFactorPoly 1 (⟨3 * k, by omega⟩ : Fin n)
           (⟨3 * k + 1, by omega⟩ : Fin n)] ++
       (List.finRange M.numStates).flatMap (fun q =>
         [cadjFactorPoly (transCoeff M q)
            (⟨3 * k - 1, by omega⟩ : Fin n)
            (⟨3 * k - 1 + 1, by omega⟩ : Fin n),
          cadjFactorPoly (transCoeff M q)
            (⟨3 * k, by omega⟩ : Fin n)
            (⟨3 * k + 1, by omega⟩ : Fin n)])) ++
      ([boolFactorPoly n ⟨3 * k + 2, by omega⟩,
        cadjFactorPoly 1 (⟨3 * k + 1, by omega⟩ : Fin n)
           (⟨3 * k + 2, by omega⟩ : Fin n),
        cadjFactorPoly 1 (⟨3 * k + 2, by omega⟩ : Fin n)
           (⟨3 * k + 3, hk2⟩ : Fin n)] ++
       (List.finRange M.numStates).flatMap (fun q =>
         [cadjFactorPoly (transCoeff M q)
            (⟨3 * k + 1, by omega⟩ : Fin n)
            (⟨3 * k + 2, by omega⟩ : Fin n),
          cadjFactorPoly (transCoeff M q)
            (⟨3 * k + 2, by omega⟩ : Fin n)
            (⟨3 * k + 3, hk2⟩ : Fin n)])) := by
  unfold inertFactorsList activeFactorsList
  rfl

end BridgeAKappaTwoIdentityThreeStructural

end PallLean.Paper93.Paper283

namespace PallLean.Paper93.Paper283

namespace BridgeAKappaTwoIdentityThreeStructural

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP
open BridgeABlockProductRule
open BridgeAKappaTwoTwoFoldLeibnizExpansion
open BridgeAKappaTwoFactorPairLemmas
open BridgeAKappaTwoIdentityOne
open BridgeAKappaTwoIdentityFour
open BridgeAKappaTwoIdentityThreeAux
open BridgeAKappaTwoListInductionHelpers

attribute [local instance] Classical.dec

/-! ## Section M: `touchedListPoly_perm_partition_claim` — the principal
permutation theorem

Given the canonical forms exposed in Sections K and L, the permutation
between `touchedListPoly` and `inertFactorsList ++ activeFactorsList`
reduces to a finite shuffling of the bool prefix, the cadj `1` block,
and the per-state `flatMap` (split into two halves via `flatMap_append_perm`).
-/

/-- Splitting the per-state cadj `flatMap` of length-4 lists into two
parallel length-2 `flatMap`s (inert + active), as a permutation. -/
private theorem transSkel_flatMap_perm_split
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    ((List.finRange M.numStates).flatMap (fun q =>
        [cadjFactorPoly (transCoeff M q)
           (⟨3 * k - 1, by omega⟩ : Fin n)
           (⟨3 * k - 1 + 1, by omega⟩ : Fin n),
         cadjFactorPoly (transCoeff M q)
           (⟨3 * k, by omega⟩ : Fin n)
           (⟨3 * k + 1, by omega⟩ : Fin n),
         cadjFactorPoly (transCoeff M q)
           (⟨3 * k + 1, by omega⟩ : Fin n)
           (⟨3 * k + 2, by omega⟩ : Fin n),
         cadjFactorPoly (transCoeff M q)
           (⟨3 * k + 2, by omega⟩ : Fin n)
           (⟨3 * k + 3, hk2⟩ : Fin n)])).Perm
      ((List.finRange M.numStates).flatMap (fun q =>
          [cadjFactorPoly (transCoeff M q)
             (⟨3 * k - 1, by omega⟩ : Fin n)
             (⟨3 * k - 1 + 1, by omega⟩ : Fin n),
           cadjFactorPoly (transCoeff M q)
             (⟨3 * k, by omega⟩ : Fin n)
             (⟨3 * k + 1, by omega⟩ : Fin n)]) ++
       (List.finRange M.numStates).flatMap (fun q =>
          [cadjFactorPoly (transCoeff M q)
             (⟨3 * k + 1, by omega⟩ : Fin n)
             (⟨3 * k + 2, by omega⟩ : Fin n),
           cadjFactorPoly (transCoeff M q)
             (⟨3 * k + 2, by omega⟩ : Fin n)
             (⟨3 * k + 3, hk2⟩ : Fin n)])) := by
  -- Each per-state list `[a, b, c, d]` is `[a, b] ++ [c, d]`; mathlib's
  -- `List.flatMap_append_perm` packages exactly the splitting fact.
  exact (List.flatMap_append_perm (List.finRange M.numStates)
    (fun q : Fin M.numStates =>
      [cadjFactorPoly (transCoeff M q)
         (⟨3 * k - 1, by omega⟩ : Fin n)
         (⟨3 * k - 1 + 1, by omega⟩ : Fin n),
       cadjFactorPoly (transCoeff M q)
         (⟨3 * k, by omega⟩ : Fin n)
         (⟨3 * k + 1, by omega⟩ : Fin n)])
    (fun q : Fin M.numStates =>
      [cadjFactorPoly (transCoeff M q)
         (⟨3 * k + 1, by omega⟩ : Fin n)
         (⟨3 * k + 2, by omega⟩ : Fin n),
       cadjFactorPoly (transCoeff M q)
         (⟨3 * k + 2, by omega⟩ : Fin n)
         (⟨3 * k + 3, hk2⟩ : Fin n)])).symm

/-- The principal structural permutation: the literal touched-list
polynomial form is permutation-equivalent to the inert/active
partition. -/
theorem touchedListPoly_perm_partition
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    touchedListPoly_perm_partition_claim M n k hk1 hk2 := by
  unfold touchedListPoly_perm_partition_claim
  -- Step 1: rewrite both sides into their canonical "explicit" forms.
  rw [touchedListPoly_explicit_form, inert_active_explicit_form]
  -- Notation: name the fixed sub-lists for readability.
  set B0 : MvPolynomial (Fin n) ℚ := boolFactorPoly n ⟨3 * k, by omega⟩
  set B1 : MvPolynomial (Fin n) ℚ := boolFactorPoly n ⟨3 * k + 1, by omega⟩
  set B2 : MvPolynomial (Fin n) ℚ := boolFactorPoly n ⟨3 * k + 2, by omega⟩
  set A0 : MvPolynomial (Fin n) ℚ :=
    cadjFactorPoly 1 (⟨3 * k - 1, by omega⟩ : Fin n)
      (⟨3 * k - 1 + 1, by omega⟩ : Fin n)
  set A1 : MvPolynomial (Fin n) ℚ :=
    cadjFactorPoly 1 (⟨3 * k, by omega⟩ : Fin n)
      (⟨3 * k + 1, by omega⟩ : Fin n)
  set A2 : MvPolynomial (Fin n) ℚ :=
    cadjFactorPoly 1 (⟨3 * k + 1, by omega⟩ : Fin n)
      (⟨3 * k + 2, by omega⟩ : Fin n)
  set A3 : MvPolynomial (Fin n) ℚ :=
    cadjFactorPoly 1 (⟨3 * k + 2, by omega⟩ : Fin n)
      (⟨3 * k + 3, hk2⟩ : Fin n)
  set Finert : List (MvPolynomial (Fin n) ℚ) :=
    (List.finRange M.numStates).flatMap (fun q =>
      [cadjFactorPoly (transCoeff M q)
         (⟨3 * k - 1, by omega⟩ : Fin n)
         (⟨3 * k - 1 + 1, by omega⟩ : Fin n),
       cadjFactorPoly (transCoeff M q)
         (⟨3 * k, by omega⟩ : Fin n)
         (⟨3 * k + 1, by omega⟩ : Fin n)])
  set Factive : List (MvPolynomial (Fin n) ℚ) :=
    (List.finRange M.numStates).flatMap (fun q =>
      [cadjFactorPoly (transCoeff M q)
         (⟨3 * k + 1, by omega⟩ : Fin n)
         (⟨3 * k + 2, by omega⟩ : Fin n),
       cadjFactorPoly (transCoeff M q)
         (⟨3 * k + 2, by omega⟩ : Fin n)
         (⟨3 * k + 3, hk2⟩ : Fin n)])
  -- LHS canonical form (after rewrites):
  --   ([B0, B1, B2] ++ [A0, A1, A2, A3]) ++ flatMap_full
  -- RHS canonical form:
  --   ([B0, B1, A0, A1] ++ Finert) ++ ([B2, A2, A3] ++ Factive)
  -- Step 2: split the LHS flatMap_full into Finert ++ Factive (perm).
  have hflat : ((List.finRange M.numStates).flatMap (fun q =>
      [cadjFactorPoly (transCoeff M q)
         (⟨3 * k - 1, by omega⟩ : Fin n)
         (⟨3 * k - 1 + 1, by omega⟩ : Fin n),
       cadjFactorPoly (transCoeff M q)
         (⟨3 * k, by omega⟩ : Fin n)
         (⟨3 * k + 1, by omega⟩ : Fin n),
       cadjFactorPoly (transCoeff M q)
         (⟨3 * k + 1, by omega⟩ : Fin n)
         (⟨3 * k + 2, by omega⟩ : Fin n),
       cadjFactorPoly (transCoeff M q)
         (⟨3 * k + 2, by omega⟩ : Fin n)
         (⟨3 * k + 3, hk2⟩ : Fin n)])).Perm (Finert ++ Factive) :=
    transSkel_flatMap_perm_split M n k hk1 hk2
  -- Step 3: assemble the perm chain.
  -- LHS = [B0,B1,B2] ++ [A0,A1,A2,A3] ++ flatMap_full
  --     ~ [B0,B1,B2] ++ [A0,A1,A2,A3] ++ (Finert ++ Factive)
  --     = [B0,B1,B2,A0,A1,A2,A3] ++ (Finert ++ Factive)
  --     ~ [B0,B1,A0,A1] ++ Finert ++ ([B2,A2,A3] ++ Factive)         (RHS)
  refine (List.Perm.append_left _ hflat).trans ?_
  -- Now: ([B0,B1,B2] ++ [A0,A1,A2,A3]) ++ (Finert ++ Factive)
  --       .Perm
  --      ([B0,B1,A0,A1] ++ Finert) ++ ([B2,A2,A3] ++ Factive)
  -- Both have the same multiset of head elements; reduce to the
  -- combinatorial perm of the head.
  -- Strategy: reassociate everything into right-associated form, then
  -- swap [B2] with [A0, A1] and shift Finert through [B2, A2, A3].
  -- Concretely:
  --   [B0,B1,B2] ++ [A0,A1,A2,A3] ++ (Finert ++ Factive)
  --   = [B0,B1] ++ ([B2] ++ [A0,A1] ++ [A2,A3] ++ (Finert ++ Factive))
  --   ~ [B0,B1] ++ ([A0,A1] ++ [B2] ++ [A2,A3] ++ (Finert ++ Factive))   -- swap [B2] and [A0,A1]
  --   = [B0,B1] ++ [A0,A1] ++ ([B2] ++ [A2,A3] ++ (Finert ++ Factive))
  --   ~ [B0,B1] ++ [A0,A1] ++ (Finert ++ [B2] ++ [A2,A3] ++ Factive)     -- swap ([B2] ++ [A2,A3]) and Finert
  --   = [B0,B1,A0,A1] ++ Finert ++ ([B2,A2,A3] ++ Factive)
  -- Convert each step into a Perm.
  -- We expose every concatenation as right-associated explicitly via
  -- `List.append_assoc`-style rewrites.
  have step1 :
      (([B0, B1, B2] ++ [A0, A1, A2, A3]) ++ (Finert ++ Factive)).Perm
      ([B0, B1] ++ [A0, A1] ++ [B2] ++ [A2, A3] ++ (Finert ++ Factive)) := by
    apply List.Perm.append_right
    -- ([B0,B1,B2] ++ [A0,A1,A2,A3]).Perm ([B0,B1] ++ [A0,A1] ++ [B2] ++ [A2,A3])
    -- LHS = [B0, B1, B2, A0, A1, A2, A3]
    -- RHS = [B0, B1, A0, A1, B2, A2, A3]
    -- Differ by swap of B2 with A0, A1 (move B2 two positions right).
    show ([B0, B1, B2, A0, A1, A2, A3] : List _).Perm
         [B0, B1, A0, A1, B2, A2, A3]
    -- Expand head: B0 :: B1 :: rest
    apply List.Perm.cons
    apply List.Perm.cons
    -- Goal: [B2, A0, A1, A2, A3].Perm [A0, A1, B2, A2, A3]
    -- = (B2 :: [A0, A1] ++ [A2, A3]).Perm ([A0, A1] ++ B2 :: [A2, A3])
    -- which is List.perm_middle reversed.
    have hmid : (B2 :: ([A0, A1] ++ [A2, A3])).Perm
                ([A0, A1] ++ B2 :: [A2, A3]) := List.perm_middle.symm
    simpa using hmid
  -- step2: shift Finert through ([B2, A2, A3])
  have step2 :
      (([B0, B1] ++ [A0, A1] ++ [B2] ++ [A2, A3]) ++ (Finert ++ Factive)).Perm
      (([B0, B1] ++ [A0, A1] ++ Finert) ++ ([B2] ++ [A2, A3] ++ Factive)) := by
    -- Both sides have [B0,B1,A0,A1,B2,A2,A3] ++ Finert ++ Factive elements.
    -- We need to move Finert from after [...,A2,A3] to after [B0,B1,A0,A1].
    -- Reassociate first.
    -- LHS reassoc: [B0,B1] ++ [A0,A1] ++ [B2] ++ [A2,A3] ++ Finert ++ Factive
    -- RHS reassoc: [B0,B1] ++ [A0,A1] ++ Finert ++ [B2] ++ [A2,A3] ++ Factive
    -- The difference: ([B2] ++ [A2,A3]) ++ Finert ~ Finert ++ ([B2] ++ [A2,A3]).
    -- This is a 2-block swap = perm_append_comm.
    -- Use `simp only [List.append_assoc]` to right-associate, then apply
    -- `Perm.append_left` repeatedly to peel off [B0,B1] and [A0,A1],
    -- then swap.
    have : (([B2] ++ [A2, A3]) ++ Finert).Perm
           (Finert ++ ([B2] ++ [A2, A3])) := List.perm_append_comm
    -- Lift through prepend [B0,B1] ++ [A0,A1] and append Factive.
    have hprep : (([B0, B1] ++ [A0, A1] ++ (([B2] ++ [A2, A3]) ++ Finert)) ++
                  Factive).Perm
                 (([B0, B1] ++ [A0, A1] ++ (Finert ++ ([B2] ++ [A2, A3]))) ++
                  Factive) :=
      (List.Perm.append_left ([B0, B1] ++ [A0, A1]) this).append_right _
    -- Massage with associativity to match the goal.
    simpa [List.append_assoc] using hprep
  -- Combine step1, step2 and finish.
  refine step1.trans (step2.trans ?_)
  -- Final: (([B0,B1] ++ [A0,A1] ++ Finert) ++ ([B2] ++ [A2,A3] ++ Factive))
  --        = ([B0,B1,A0,A1] ++ Finert) ++ ([B2,A2,A3] ++ Factive)
  -- This is `rfl` modulo right-associativity of ++.
  rfl

/-! ## Axiom audit anchors -/

#print axioms one_sub_boolLC_poly_eq_boolFactorPoly
#print axioms one_sub_adjLC_poly_eq_cadjFactorPoly
#print axioms one_sub_transSkelLC_poly_eq_cadjFactorPoly
#print axioms adjFactors_mapped_form
#print axioms transSkelFactorsForState_mapped_form
#print axioms transSkelFactorsFlat_mapped_form
#print axioms touchedListPoly_explicit_form
#print axioms inert_active_explicit_form
#print axioms touchedListPoly_perm_partition

end BridgeAKappaTwoIdentityThreeStructural

end PallLean.Paper93.Paper283
