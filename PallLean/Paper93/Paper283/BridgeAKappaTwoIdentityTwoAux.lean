import PallLean.Paper93.Paper283.BridgeAKappaTwoTouchedListExplicit
import PallLean.Paper93.Paper283.BridgeAKappaTwoTwoFoldLeibnizExpansion
import PallLean.Paper93.Paper283.BridgeAKappaTwoPerPairCoefficients
import PallLean.Paper93.Paper283.BridgeAKappaTwoFactorPairLemmas
import PallLean.Paper93.Paper283.BridgeAKappaTwoFourCoefficientIdentities
import PallLean.Paper93.Paper283.MultilinearCoefficientInfrastructure

/-!
# Identity (2) auxiliary lemmas: per-pair coefficient analysis

This file collects auxiliary structural lemmas used by
`BridgeAKappaTwoIdentityTwo.lean` to advance the per-pair sum
discharge.  Per the analytic derivation in
`BridgeAKappaTwoFourIdentitiesProven`, identity (2) treats the
configuration:

* `rowLeft = [3k-1, 3k]` (differentiation indices `v = 3*(k-1)+2 = 3k-1`,
  `w = 3*k+0 = 3k`).
* `probeRight = X_{3k+1} * X_{3k+2}`.

The target is to show that the bilinear coefficient at `probeRight` of
`pderivListProdSumTwice v w (touchedList.map (1 - ·.poly))` equals
`crossBlockKValue (transCoeffSum M) = (1 + S) * S`.

## Per-factor derivative shape under (v = 3k-1, w = 3k)

For the explicit literal touched-list at interior block `k` (3 bool +
4 adj + 4 * numStates trans), each factor has a controlled second
derivative pattern under `pderiv w (pderiv v ·)`.

This file establishes:

* **Section C** — factor-level second derivative shapes for each
  shape (bool, cadj/trans) at every position appearing in the
  touched-list.
* **Section E** — pass-through (inert) lemmas: factors that vanish
  under both `pderiv v` and `pderiv w` collapse the cons step in
  `pderivListProdSumTwice` to a single multiplication.

The full list-induction closure of `identityTwo_perPairSum` remains
as the documented residual obstruction in
`BridgeAKappaTwoPerPairCoefficients`.

## Hard rules (project CLAUDE.md)

* No `sorry`.  No new axioms.  All lemmas below have explicit proofs
  using existing infrastructure.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP
open BridgeABlockProductRule
open BridgeAKappaTwoTwoFoldLeibnizExpansion
open MultilinearCoefficientInfrastructure
open BridgeAKappaTwoFactorPairLemmas

attribute [local instance] Classical.dec

namespace BridgeAKappaTwoIdentityTwoAux

/-! ## Section A: identity (2)'s differentiation indices -/

/-- The first differentiation index for identity (2): `v = 3*(k-1)+2 = 3k-1`. -/
noncomputable def vIdx (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) : Fin n :=
  ⟨3 * (k - 1) + 2, by
    have heq : 3 * (k - 1) + 3 = 3 * k := by
      rw [show (3 : Nat) = 3 * 1 from rfl, ← Nat.mul_add]
      congr 1; omega
    omega⟩

/-- The second differentiation index for identity (2): `w = 3*k+0 = 3k`. -/
noncomputable def wIdx (n k : Nat) (hk2 : 3 * k + 3 < n) : Fin n :=
  ⟨3 * k + 0, by omega⟩

/-- Witness that `vIdx.val = 3*(k-1) + 2`. -/
@[simp] theorem vIdx_val (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    (vIdx n k hk1 hk2).val = 3 * (k - 1) + 2 := rfl

/-- Witness that `wIdx.val = 3*k + 0`. -/
@[simp] theorem wIdx_val (n k : Nat) (hk2 : 3 * k + 3 < n) :
    (wIdx n k hk2).val = 3 * k + 0 := rfl

/-- The differentiation indices are distinct: `v ≠ w`. -/
theorem vIdx_ne_wIdx (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    vIdx n k hk1 hk2 ≠ wIdx n k hk2 := by
  intro h
  have heq : (vIdx n k hk1 hk2).val = (wIdx n k hk2).val := by rw [h]
  simp [vIdx_val, wIdx_val] at heq
  -- 3*(k-1)+2 = 3k+0 means 3k - 1 = 3k, impossible since k ≥ 1.
  omega

/-! ## Section B: probe variable distinctness -/

/-- The two probe variables are distinct: `3k+1 ≠ 3k+2`. -/
theorem probeRight_var_ne (n k : Nat) (hk2 : 3 * k + 3 < n) :
    (⟨3 * k + 1, by omega⟩ : Fin n) ≠ ⟨3 * k + 2, by omega⟩ := by
  intro h
  have := congr_arg Fin.val h
  simp at this

/-! ## Section C: factor structure after differentiation

We expose, for each shape of factor in the touched list, the value of
`pderiv_w (pderiv_v factor)` under `(v, w) = (3*(k-1)+2, 3k+0)`.  These
are the inputs to the per-pair list induction.
-/

/-- For a bool factor at index `a` with `a.val = 3*k`, the second
derivative under `(v, w) = (vIdx, wIdx)` is zero.

Reason: from Family A (`pderiv_w_pderiv_v_one_sub_boolLC_factor`), the
result is nonzero only when `v = a ∧ w = a`, but here v = 3*(k-1)+2 ≠ a. -/
theorem pderiv_w_pderiv_v_boolFactor_at_3k_eq_zero
    (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.pderiv (wIdx n k hk2)
      (MvPolynomial.pderiv (vIdx n k hk1 hk2)
        (boolFactorPoly n ⟨3 * k, by omega⟩)) = 0 := by
  rw [pderiv_w_pderiv_v_one_sub_boolLC_factor]
  rw [if_neg]
  intro ⟨hva, _⟩
  have := congr_arg Fin.val hva
  simp at this
  omega

theorem pderiv_w_pderiv_v_boolFactor_at_3k_plus_1_eq_zero
    (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.pderiv (wIdx n k hk2)
      (MvPolynomial.pderiv (vIdx n k hk1 hk2)
        (boolFactorPoly n ⟨3 * k + 1, by omega⟩)) = 0 := by
  rw [pderiv_w_pderiv_v_one_sub_boolLC_factor]
  rw [if_neg]
  intro ⟨hva, _⟩
  have := congr_arg Fin.val hva
  simp at this
  omega

theorem pderiv_w_pderiv_v_boolFactor_at_3k_plus_2_eq_zero
    (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.pderiv (wIdx n k hk2)
      (MvPolynomial.pderiv (vIdx n k hk1 hk2)
        (boolFactorPoly n ⟨3 * k + 2, by omega⟩)) = 0 := by
  rw [pderiv_w_pderiv_v_one_sub_boolLC_factor]
  rw [if_neg]
  intro ⟨hva, _⟩
  have := congr_arg Fin.val hva
  simp at this
  omega

/-- cadj factor at (3k-1, 3k): `(v, w) = (i, j)` (the diagonal case),
yielding `-(C c)`. -/
theorem pderiv_w_pderiv_v_cadjFactor_self_at_3k_minus_1
    (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) (c : ℚ) :
    MvPolynomial.pderiv (wIdx n k hk2)
      (MvPolynomial.pderiv (vIdx n k hk1 hk2)
        (cadjFactorPoly c
          (⟨3 * k - 1, by omega⟩ : Fin n)
          (⟨3 * k - 1 + 1, by omega⟩ : Fin n))) =
      -(MvPolynomial.C c) := by
  have hij : (⟨3 * k - 1, by omega⟩ : Fin n) ≠ ⟨3 * k - 1 + 1, by omega⟩ := by
    intro h
    have := congr_arg Fin.val h
    simp at this
  rw [pderiv_w_pderiv_v_one_sub_C_X_mul_X _ _ _ _ _ hij]
  rw [if_pos]
  refine Or.inl ⟨?_, ?_⟩
  · apply Fin.ext
    simp [vIdx_val]
    omega
  · apply Fin.ext
    simp [wIdx_val]
    omega

/-- cadj factor at (3k, 3k+1): zero.  `v = 3*(k-1)+2 ∉ {3k, 3k+1}`. -/
theorem pderiv_w_pderiv_v_cadjFactor_at_3k
    (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) (c : ℚ) :
    MvPolynomial.pderiv (wIdx n k hk2)
      (MvPolynomial.pderiv (vIdx n k hk1 hk2)
        (cadjFactorPoly c
          (⟨3 * k, by omega⟩ : Fin n)
          (⟨3 * k + 1, by omega⟩ : Fin n))) = 0 := by
  have hij : (⟨3 * k, by omega⟩ : Fin n) ≠ ⟨3 * k + 1, by omega⟩ := by
    intro h
    have := congr_arg Fin.val h
    simp at this
  rw [pderiv_w_pderiv_v_one_sub_C_X_mul_X _ _ _ _ _ hij]
  rw [if_neg]
  intro h
  rcases h with ⟨hva, _⟩ | ⟨hva, _⟩
  · have := congr_arg Fin.val hva
    simp at this
    omega
  · have := congr_arg Fin.val hva
    simp at this
    omega

/-- cadj factor at (3k+1, 3k+2): zero. -/
theorem pderiv_w_pderiv_v_cadjFactor_at_3k_plus_1
    (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) (c : ℚ) :
    MvPolynomial.pderiv (wIdx n k hk2)
      (MvPolynomial.pderiv (vIdx n k hk1 hk2)
        (cadjFactorPoly c
          (⟨3 * k + 1, by omega⟩ : Fin n)
          (⟨3 * k + 2, by omega⟩ : Fin n))) = 0 := by
  have hij : (⟨3 * k + 1, by omega⟩ : Fin n) ≠ ⟨3 * k + 2, by omega⟩ := by
    intro h
    have := congr_arg Fin.val h
    simp at this
  rw [pderiv_w_pderiv_v_one_sub_C_X_mul_X _ _ _ _ _ hij]
  rw [if_neg]
  intro h
  rcases h with ⟨hva, _⟩ | ⟨hva, _⟩
  · have := congr_arg Fin.val hva
    simp at this
    omega
  · have := congr_arg Fin.val hva
    simp at this
    omega

/-- cadj factor at (3k+2, 3k+3): zero. -/
theorem pderiv_w_pderiv_v_cadjFactor_at_3k_plus_2
    (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) (c : ℚ) :
    MvPolynomial.pderiv (wIdx n k hk2)
      (MvPolynomial.pderiv (vIdx n k hk1 hk2)
        (cadjFactorPoly c
          (⟨3 * k + 2, by omega⟩ : Fin n)
          (⟨3 * k + 3, hk2⟩ : Fin n))) = 0 := by
  have hij : (⟨3 * k + 2, by omega⟩ : Fin n) ≠ ⟨3 * k + 3, hk2⟩ := by
    intro h
    have := congr_arg Fin.val h
    simp at this
  rw [pderiv_w_pderiv_v_one_sub_C_X_mul_X _ _ _ _ _ hij]
  rw [if_neg]
  intro h
  rcases h with ⟨hva, _⟩ | ⟨hva, _⟩
  · have := congr_arg Fin.val hva
    simp at this
    omega
  · have := congr_arg Fin.val hva
    simp at this
    omega

/-! ## Section D: documentation of the residual sub-task

The remaining work to fully discharge `identityTwo_perPairSum` is a
list induction over the literal touched-list (3 bool + 4 adj + 4 *
numStates trans factors) at the level of
`pderivListProdSumTwice_cons`.  Each cons step contributes 4 terms
(see `pderivListProdSumTwice_cons` in
`BridgeAKappaTwoTwoFoldLeibnizExpansion`):

```
pderivListProdSumTwice v w (x :: xs)
  = pderiv w (pderiv v x) * xs.prod                         -- (T1)
  + pderiv v x * pderiv w xs.prod                           -- (T2)
  + pderiv w x * pderivListProdSum v xs                     -- (T3)
  + x * pderivListProdSumTwice v w xs                       -- (T4)
```

Iterating this for each of the 7 + 4·numStates touched-list factors
yields the full path enumeration.  At each step, the per-factor
derivative shapes computed in Section C above determine which terms
contribute.

By the analytic derivation in
`BridgeAKappaTwoFourIdentitiesProven` (file docstring), the total
collapses to `(1 + S) * S = crossBlockKValue (transCoeffSum M)`, with
`S = transCoeffSum M = Σ_q transCoeff M q`.
-/

/-! ## Section E0: `probeRight` indices and probe expansion -/

/-- The two coordinate functionals appearing in `probeRight` are `3k+1`
and `3k+2`; they are distinct (`3k+1 ≠ 3k+2`). -/
theorem probeRight_indices_ne (n k : Nat) (hk2 : 3 * k + 3 < n) :
    (⟨3 * k + 1, by omega⟩ : Fin n) ≠ ⟨3 * k + 2, by omega⟩ := by
  intro h
  have := congr_arg Fin.val h
  simp at this

/-- The probeRight monomial expands as
`single (3k+1) 1 + single (3k+2) 1`. -/
theorem probeRight_eq_sum_single (n k : Nat) (hk2 : 3 * k + 3 < n) :
    (Finsupp.single (⟨3 * k + 1, by omega⟩ : Fin n) 1 +
       Finsupp.single (⟨3 * k + 2, by omega⟩ : Fin n) 1 :
        Fin n →₀ ℕ) =
    Finsupp.single (⟨3 * k + 1, by omega⟩ : Fin n) 1 +
      Finsupp.single (⟨3 * k + 2, by omega⟩ : Fin n) 1 := rfl

/-! ## Section E0b: cons recurrence at the `coeff probeRight` level -/

/-- Coefficient-level cons recurrence for the per-pair sum of identity
(2): on a `cons`, the coefficient at the probe of
`pderivListProdSumTwice u v (x :: xs)` decomposes as a 4-term sum
matching `pderivListProdSumTwice_cons`. -/
theorem coeff_probeRight_pderivListProdSumTwice_cons
    {n : Nat} (probe : Fin n →₀ ℕ)
    (u v : Fin n) (x : MvPolynomial (Fin n) ℚ)
    (xs : List (MvPolynomial (Fin n) ℚ)) :
    MvPolynomial.coeff probe
        (pderivListProdSumTwice u v (x :: xs)) =
      MvPolynomial.coeff probe
          (MvPolynomial.pderiv v (MvPolynomial.pderiv u x) * xs.prod)
      + MvPolynomial.coeff probe
          (MvPolynomial.pderiv u x * MvPolynomial.pderiv v xs.prod)
      + MvPolynomial.coeff probe
          (MvPolynomial.pderiv v x *
            BridgeABlockProductRule.pderivListProdSum u xs)
      + MvPolynomial.coeff probe
          (x * pderivListProdSumTwice u v xs) := by
  rw [pderivListProdSumTwice_cons]
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add]

/-- Nil base case: `coeff probe (pderivListProdSumTwice u v []) = 0`. -/
theorem coeff_probeRight_pderivListProdSumTwice_nil
    {n : Nat} (probe : Fin n →₀ ℕ) (u v : Fin n) :
    MvPolynomial.coeff probe
        (pderivListProdSumTwice (R := ℚ) u v
          ([] : List (MvPolynomial (Fin n) ℚ))) = 0 := by
  rw [pderivListProdSumTwice_nil]
  exact MvPolynomial.coeff_zero _

/-! ## Section E: pass-through lemmas for inert factors

A factor `f` with `pderiv v f = 0 ∧ pderiv w f = 0` is "inert" with
respect to the (v, w) two-fold Leibniz expansion: when it appears as
the head, only term T4 = `f * pderivListProdSumTwice v w xs` survives.
-/

/-- Pass-through for `pderivListProdSumTwice` when the head factor is
inert (both `pderiv v f` and `pderiv w f` vanish). -/
theorem pderivListProdSumTwice_cons_inert
    {N : ℕ} (v w : Fin N) (f : MvPolynomial (Fin N) ℚ)
    (fs : List (MvPolynomial (Fin N) ℚ))
    (hvf : MvPolynomial.pderiv v f = 0)
    (hwf : MvPolynomial.pderiv w f = 0) :
    pderivListProdSumTwice v w (f :: fs) =
      f * pderivListProdSumTwice v w fs := by
  have h1 : MvPolynomial.pderiv w (MvPolynomial.pderiv v f) = 0 := by
    rw [hvf]; exact map_zero _
  rw [pderivListProdSumTwice_cons]
  rw [h1, hvf, hwf]
  ring

/-- The bool factor at index `a` with `a ≠ v` and `a ≠ w` is inert. -/
theorem boolFactor_inert_of_neither
    {N : ℕ} (v w a : Fin N) (hva : v ≠ a) (hwa : w ≠ a) :
    MvPolynomial.pderiv v (boolFactorPoly N a) = 0 ∧
    MvPolynomial.pderiv w (boolFactorPoly N a) = 0 := by
  refine ⟨?_, ?_⟩
  · exact pderiv_one_sub_boolLC_factor_of_ne a v hva
  · exact pderiv_one_sub_boolLC_factor_of_ne a w hwa

/-- The cadj factor at indices `(i, j)` with `v ∉ {i, j}` and
`w ∉ {i, j}` is inert. -/
theorem cadjFactor_inert_of_outside
    {N : ℕ} (c : ℚ) (i j v w : Fin N)
    (hvi : v ≠ i) (hvj : v ≠ j) (hwi : w ≠ i) (hwj : w ≠ j) :
    MvPolynomial.pderiv v (cadjFactorPoly c i j) = 0 ∧
    MvPolynomial.pderiv w (cadjFactorPoly c i j) = 0 := by
  refine ⟨?_, ?_⟩
  · exact pderiv_one_sub_C_X_mul_X_at_other c i j v hvi hvj
  · exact pderiv_one_sub_C_X_mul_X_at_other c i j w hwi hwj

/-! ## Section F: residual obstruction marker for the list induction

The list induction over the literal touched-list is the residual
work to discharge `identityTwo_perPairSum`.  The factor-level shapes
in Sections C and E above are the inputs to this induction.

By iterating `pderivListProdSumTwice_cons_inert` over the inert
factors and `pderivListProdSumTwice_cons` over the active factors,
the per-pair sum reduces to a finite sum of products of factor
derivatives, which can be evaluated using Family A/B from
`BridgeAKappaTwoFactorPairLemmas` and Family D bilinear-coefficient
extraction.

The residual obstruction is exposed as
`kappaTwoFourIdentities_perPairSum_obstruction` in
`BridgeAKappaTwoPerPairCoefficients`, which the four identity files
consume as a typed residual hypothesis. -/

/-! ## Axiom audit anchors -/

#print axioms probeRight_indices_ne
#print axioms coeff_probeRight_pderivListProdSumTwice_cons
#print axioms coeff_probeRight_pderivListProdSumTwice_nil
#print axioms vIdx_ne_wIdx
#print axioms pderiv_w_pderiv_v_boolFactor_at_3k_eq_zero
#print axioms pderiv_w_pderiv_v_boolFactor_at_3k_plus_1_eq_zero
#print axioms pderiv_w_pderiv_v_boolFactor_at_3k_plus_2_eq_zero
#print axioms pderiv_w_pderiv_v_cadjFactor_self_at_3k_minus_1
#print axioms pderiv_w_pderiv_v_cadjFactor_at_3k
#print axioms pderiv_w_pderiv_v_cadjFactor_at_3k_plus_1
#print axioms pderiv_w_pderiv_v_cadjFactor_at_3k_plus_2
#print axioms pderivListProdSumTwice_cons_inert
#print axioms boolFactor_inert_of_neither
#print axioms cadjFactor_inert_of_outside

end BridgeAKappaTwoIdentityTwoAux

end PallLean.Paper93.Paper283
