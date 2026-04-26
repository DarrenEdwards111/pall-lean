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
