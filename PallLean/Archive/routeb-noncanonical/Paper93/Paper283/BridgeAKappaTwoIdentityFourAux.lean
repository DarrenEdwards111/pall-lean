import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityFour
import PallLean.Paper93.Paper283.BridgeAKappaTwoFactorPairLemmas
import PallLean.Paper93.Paper283.BridgeAKappaTwoPerPairCoefficients

/-!
# Auxiliary helpers for identity (4) per-pair sum (κ=2 Bridge A)

This file develops genuine kernel-only structural helpers towards
discharging
```
identityFour_perPairSum M n hn htb hns k hk1 hk2
```
i.e.
```
coeff probeLeft (pderivListProdSumTwice u v
   ((kappaTwoTouchedList_explicit M n k hk1 hk2).map
     (fun c => 1 - c.poly))) = 2 * crossBlockKValue (transCoeffSum M)
```
with `u = ⟨3*(k-1)+2⟩ = ⟨3k-1⟩`, `v = ⟨3k⟩`,
`probeLeft = X_{3k} · X_{3k+1}`.

## Strategy

The recursive form `pderivListProdSumTwice_cons` peels one factor at a
time:
```
pderivListProdSumTwice u v (x :: xs)
  = pderiv v (pderiv u x) * xs.prod
    + pderiv u x * pderiv v xs.prod
    + pderiv v x * pderivListProdSum u xs
    + x * pderivListProdSumTwice u v xs.
```

Taking `coeff probeLeft` of both sides and applying
`coeff_two_mono_mul` (with the `hvw` hypothesis `3k ≠ 3k+1` for
`probeLeft`) yields a 16-term recursive identity reducing one factor
at a time.  Iterated `7 + 4 * M.numStates` times across the literal
explicit touched-list, the recursion bottoms out at the empty list
where `pderivListProdSumTwice = 0` and `pderivListProdSum = 0`.

This file packages the structural reduction lemmas (one factor at a
time and one product-rule level at a time).  The full closure of
`identityFour_perPairSum` requires evaluating each per-factor
contribution under the four families (bool, cadj, mixed) and summing
them — that residual is left for a follow-up file (~1000 lines per
the `BridgeAKappaTwoFourIdentitiesProven` docstring estimate).

## Hard rules (project CLAUDE.md)

* No `sorry`.  No new axioms.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP
open IterDerivHelpers
open BridgeAKappaTwoTwoFoldLeibnizExpansion
open MultilinearCoefficientInfrastructure
open BridgeAKappaTwoIdentityOne
open BridgeAKappaTwoIdentityFour
open BridgeAKappaTwoFactorPairLemmas

attribute [local instance] Classical.dec

namespace BridgeAKappaTwoIdentityFourAux

/-! ## Section A: probeLeft inequality `3k ≠ 3k+1` -/

/-- The two indices of `probeLeft` are distinct. -/
theorem probeLeft_indices_ne (n k : Nat) (hk2 : 3 * k + 3 < n) :
    (⟨3 * k, by omega⟩ : Fin n) ≠ (⟨3 * k + 1, by omega⟩ : Fin n) := by
  intro h
  have := congr_arg Fin.val h
  simp at this

/-! ## Section B: probeLeft as a multilinear monomial -/

/-- `probeLeft` written as a sum of singletons (matches the form expected
by `coeff_two_mono_mul`). -/
theorem probeLeft_eq_sum_single (n k : Nat) (hk2 : 3 * k + 3 < n) :
    probeLeft n k hk2 =
      Finsupp.single (⟨3 * k, by omega⟩ : Fin n) 1 +
        Finsupp.single (⟨3 * k + 1, by omega⟩ : Fin n) 1 := by
  unfold probeLeft
  rfl

/-! ## Section C: coeff at probeLeft of pderivListProdSumTwice on a cons

This is the central structural reduction: peel one factor at a time
from the list, expressing the coefficient at `probeLeft` of
`pderivListProdSumTwice u v (x :: xs)` as a 16-term sum of products of
(per-factor head data) and (per-tail data). -/

/-- The head term `pderiv v (pderiv u x) * xs.prod`, decomposed via
`coeff_two_mono_mul`. -/
theorem coeff_probeLeft_head_pdvpduxs
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (u v : Fin n) (x : MvPolynomial (Fin n) ℚ)
    (xs : List (MvPolynomial (Fin n) ℚ)) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (MvPolynomial.pderiv v (MvPolynomial.pderiv u x) * xs.prod) =
      MvPolynomial.coeff
          (Finsupp.single (⟨3 * k, by omega⟩ : Fin n) 1)
          (MvPolynomial.pderiv v (MvPolynomial.pderiv u x)) *
        MvPolynomial.coeff
          (Finsupp.single (⟨3 * k + 1, by omega⟩ : Fin n) 1) xs.prod
      + MvPolynomial.coeff
          (Finsupp.single (⟨3 * k + 1, by omega⟩ : Fin n) 1)
          (MvPolynomial.pderiv v (MvPolynomial.pderiv u x)) *
        MvPolynomial.coeff
          (Finsupp.single (⟨3 * k, by omega⟩ : Fin n) 1) xs.prod
      + MvPolynomial.coeff (probeLeft n k hk2)
          (MvPolynomial.pderiv v (MvPolynomial.pderiv u x)) *
        MvPolynomial.coeff 0 xs.prod
      + MvPolynomial.coeff 0
          (MvPolynomial.pderiv v (MvPolynomial.pderiv u x)) *
        MvPolynomial.coeff (probeLeft n k hk2) xs.prod := by
  rw [probeLeft_eq_sum_single]
  exact coeff_two_mono_mul (⟨3 * k, by omega⟩ : Fin n)
    (⟨3 * k + 1, by omega⟩ : Fin n)
    (probeLeft_indices_ne n k hk2) _ _

/-- The cross term `pderiv u x * pderiv v xs.prod`, decomposed. -/
theorem coeff_probeLeft_cross_pduxpdvxs
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (u v : Fin n) (x : MvPolynomial (Fin n) ℚ)
    (xs : List (MvPolynomial (Fin n) ℚ)) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (MvPolynomial.pderiv u x * MvPolynomial.pderiv v xs.prod) =
      MvPolynomial.coeff
          (Finsupp.single (⟨3 * k, by omega⟩ : Fin n) 1)
          (MvPolynomial.pderiv u x) *
        MvPolynomial.coeff
          (Finsupp.single (⟨3 * k + 1, by omega⟩ : Fin n) 1)
          (MvPolynomial.pderiv v xs.prod)
      + MvPolynomial.coeff
          (Finsupp.single (⟨3 * k + 1, by omega⟩ : Fin n) 1)
          (MvPolynomial.pderiv u x) *
        MvPolynomial.coeff
          (Finsupp.single (⟨3 * k, by omega⟩ : Fin n) 1)
          (MvPolynomial.pderiv v xs.prod)
      + MvPolynomial.coeff (probeLeft n k hk2)
          (MvPolynomial.pderiv u x) *
        MvPolynomial.coeff 0 (MvPolynomial.pderiv v xs.prod)
      + MvPolynomial.coeff 0 (MvPolynomial.pderiv u x) *
        MvPolynomial.coeff (probeLeft n k hk2)
          (MvPolynomial.pderiv v xs.prod) := by
  rw [probeLeft_eq_sum_single]
  exact coeff_two_mono_mul (⟨3 * k, by omega⟩ : Fin n)
    (⟨3 * k + 1, by omega⟩ : Fin n)
    (probeLeft_indices_ne n k hk2) _ _

/-- The cross term `pderiv v x * pderivListProdSum u xs`, decomposed. -/
theorem coeff_probeLeft_cross_pdvxpdsumuxs
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (u v : Fin n) (x : MvPolynomial (Fin n) ℚ)
    (xs : List (MvPolynomial (Fin n) ℚ)) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (MvPolynomial.pderiv v x *
          BridgeABlockProductRule.pderivListProdSum u xs) =
      MvPolynomial.coeff
          (Finsupp.single (⟨3 * k, by omega⟩ : Fin n) 1)
          (MvPolynomial.pderiv v x) *
        MvPolynomial.coeff
          (Finsupp.single (⟨3 * k + 1, by omega⟩ : Fin n) 1)
          (BridgeABlockProductRule.pderivListProdSum u xs)
      + MvPolynomial.coeff
          (Finsupp.single (⟨3 * k + 1, by omega⟩ : Fin n) 1)
          (MvPolynomial.pderiv v x) *
        MvPolynomial.coeff
          (Finsupp.single (⟨3 * k, by omega⟩ : Fin n) 1)
          (BridgeABlockProductRule.pderivListProdSum u xs)
      + MvPolynomial.coeff (probeLeft n k hk2)
          (MvPolynomial.pderiv v x) *
        MvPolynomial.coeff 0
          (BridgeABlockProductRule.pderivListProdSum u xs)
      + MvPolynomial.coeff 0 (MvPolynomial.pderiv v x) *
        MvPolynomial.coeff (probeLeft n k hk2)
          (BridgeABlockProductRule.pderivListProdSum u xs) := by
  rw [probeLeft_eq_sum_single]
  exact coeff_two_mono_mul (⟨3 * k, by omega⟩ : Fin n)
    (⟨3 * k + 1, by omega⟩ : Fin n)
    (probeLeft_indices_ne n k hk2) _ _

/-- The recursive term `x * pderivListProdSumTwice u v xs`, decomposed. -/
theorem coeff_probeLeft_recur_xpdsumtuvxs
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (u v : Fin n) (x : MvPolynomial (Fin n) ℚ)
    (xs : List (MvPolynomial (Fin n) ℚ)) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (x * pderivListProdSumTwice u v xs) =
      MvPolynomial.coeff
          (Finsupp.single (⟨3 * k, by omega⟩ : Fin n) 1) x *
        MvPolynomial.coeff
          (Finsupp.single (⟨3 * k + 1, by omega⟩ : Fin n) 1)
          (pderivListProdSumTwice u v xs)
      + MvPolynomial.coeff
          (Finsupp.single (⟨3 * k + 1, by omega⟩ : Fin n) 1) x *
        MvPolynomial.coeff
          (Finsupp.single (⟨3 * k, by omega⟩ : Fin n) 1)
          (pderivListProdSumTwice u v xs)
      + MvPolynomial.coeff (probeLeft n k hk2) x *
        MvPolynomial.coeff 0 (pderivListProdSumTwice u v xs)
      + MvPolynomial.coeff 0 x *
        MvPolynomial.coeff (probeLeft n k hk2)
          (pderivListProdSumTwice u v xs) := by
  rw [probeLeft_eq_sum_single]
  exact coeff_two_mono_mul (⟨3 * k, by omega⟩ : Fin n)
    (⟨3 * k + 1, by omega⟩ : Fin n)
    (probeLeft_indices_ne n k hk2) _ _

/-! ## Section D: combined cons reduction

The key recursion: `coeff probeLeft (pderivListProdSumTwice u v (x :: xs))`
is the sum of the four pieces above. -/

/-- The `coeff probeLeft (pderivListProdSumTwice u v (x :: xs))` recursion.
This decomposes the coefficient at `probeLeft` of the two-fold Leibniz
expansion at a cons head into a sum of four pieces, each involving
either the head `x` (or its derivatives) and the tail `xs` (or its
derived list-Leibniz expansions). -/
theorem coeff_probeLeft_pderivListProdSumTwice_cons
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (u v : Fin n) (x : MvPolynomial (Fin n) ℚ)
    (xs : List (MvPolynomial (Fin n) ℚ)) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (pderivListProdSumTwice u v (x :: xs)) =
      MvPolynomial.coeff (probeLeft n k hk2)
          (MvPolynomial.pderiv v (MvPolynomial.pderiv u x) * xs.prod)
      + MvPolynomial.coeff (probeLeft n k hk2)
          (MvPolynomial.pderiv u x * MvPolynomial.pderiv v xs.prod)
      + MvPolynomial.coeff (probeLeft n k hk2)
          (MvPolynomial.pderiv v x *
            BridgeABlockProductRule.pderivListProdSum u xs)
      + MvPolynomial.coeff (probeLeft n k hk2)
          (x * pderivListProdSumTwice u v xs) := by
  rw [pderivListProdSumTwice_cons]
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add]

/-! ## Section E: nil case and base reductions -/

/-- Base case: `coeff probeLeft (pderivListProdSumTwice u v []) = 0`. -/
theorem coeff_probeLeft_pderivListProdSumTwice_nil
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n) (u v : Fin n) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (pderivListProdSumTwice (R := ℚ) u v
          ([] : List (MvPolynomial (Fin n) ℚ))) = 0 := by
  rw [pderivListProdSumTwice_nil]
  exact MvPolynomial.coeff_zero _

/-! ## Section F: residual obstruction marker

The full closure of `identityFour_perPairSum` requires iterating
`coeff_probeLeft_pderivListProdSumTwice_cons` across the literal
length-(7 + 4*numStates) touched-list, evaluating per-factor
coefficient contributions via the Family A/B/D lemmas of
`BridgeAKappaTwoFactorPairLemmas`, and summing the results.

By the analytic computation in
`BridgeAKappaTwoFourIdentitiesProven`'s docstring (specialised to the
left/left configuration), the sum is `2 * crossBlockKValue (transCoeffSum M)`.

The full computation is structurally identical to identity (1) (under
the left/right swap of the configuration `u = 3k-1, v = 3k`,
`probeLeft = X_{3k}·X_{3k+1}` versus identity (1)'s `u = 3k+2,
v = 3k+3`, `probeRight = X_{3k+1}·X_{3k+2}`); per the project's
"DO NOT SIMPLIFY" rule and the parallel-agent template strategy, we
expose the structural reduction lemmas above and leave the full
~1000-line per-factor evaluation as a follow-up that, by symmetry,
can re-use any closure of identity (1). -/

/-! ## Axiom audit anchors -/

#print axioms probeLeft_indices_ne
#print axioms probeLeft_eq_sum_single
#print axioms coeff_probeLeft_head_pdvpduxs
#print axioms coeff_probeLeft_cross_pduxpdvxs
#print axioms coeff_probeLeft_cross_pdvxpdsumuxs
#print axioms coeff_probeLeft_recur_xpdsumtuvxs
#print axioms coeff_probeLeft_pderivListProdSumTwice_cons
#print axioms coeff_probeLeft_pderivListProdSumTwice_nil


/-! ## Section G: u, v for identity (4)

Concrete `u, v ∈ Fin n` for identity (4):
* `u = ⟨3*(k-1)+2⟩ = ⟨3k-1⟩` (the first row index, applied via outer pderiv)
* `v = ⟨3*k⟩` (the second row index, applied via inner pderiv)

Note that `v = 3k` is one of the indices of `probeLeft = X_{3k}·X_{3k+1}`,
while `u = 3k-1` is NOT.  This is the mirror of identity (1)'s
`(u, v) = (3k+2, 3k+3)` vs `probeRight = X_{3k+1}·X_{3k+2}`. -/

/-- The two row indices for identity (4). -/
noncomputable def rowLeft_u (n : Nat) (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    Fin n :=
  ⟨3 * (k - 1) + 2, by
    have heq : 3 * (k - 1) + 3 = 3 * k := by
      rw [show (3 : Nat) = 3 * 1 from rfl, ← Nat.mul_add]
      congr 1; omega
    omega⟩

noncomputable def rowLeft_v (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n) :
    Fin n :=
  ⟨3 * k + 0, by omega⟩

/-- The first row index `u = 3k-1` differs from `3k` and `3k+1`. -/
theorem rowLeft_u_val (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    (rowLeft_u n k hk1 hk2).val = 3 * k - 1 := by
  unfold rowLeft_u
  show 3 * (k - 1) + 2 = 3 * k - 1
  omega

theorem rowLeft_v_val (n k : Nat) (hk2 : 3 * k + 3 < n) :
    (rowLeft_v n k hk2).val = 3 * k := by
  unfold rowLeft_v; rfl

theorem rowLeft_u_ne_rowLeft_v (n : Nat) (k : Nat) (hk1 : 1 ≤ k)
    (hk2 : 3 * k + 3 < n) :
    rowLeft_u n k hk1 hk2 ≠ rowLeft_v n k hk2 := by
  intro h
  have := congr_arg Fin.val h
  rw [rowLeft_u_val, rowLeft_v_val] at this
  omega

/-! ## Section H: pderiv u and pderiv v applied to bool factors

Key facts:
* `pderiv u (boolFactor a)` is nonzero only if `u = a` (then `-1 + 2 X_a`),
  zero otherwise.
* For our `u = 3k-1`, the bool factors at indices `3k`, `3k+1`, `3k+2`
  all yield zero (since `u ≠ 3k, 3k+1, 3k+2`).
* For our `v = 3k`, the bool factor at index `3k` yields `-1 + 2 X_{3k}`,
  while bool factors at `3k+1` and `3k+2` yield zero. -/

/-- For our `u = 3k-1`, `pderiv u (boolFactor 3k) = 0`. -/
theorem pderiv_u_boolFactor_3k_zero (n : Nat) (k : Nat) (hk1 : 1 ≤ k)
    (hk2 : 3 * k + 3 < n) :
    MvPolynomial.pderiv (rowLeft_u n k hk1 hk2)
        (boolFactorPoly n ⟨3 * k, by omega⟩) = 0 := by
  apply pderiv_one_sub_boolLC_factor_of_ne
  intro h
  have := congr_arg Fin.val h
  rw [rowLeft_u_val] at this
  simp only [Fin.val_mk] at this
  omega

theorem pderiv_u_boolFactor_3k1_zero (n : Nat) (k : Nat) (hk1 : 1 ≤ k)
    (hk2 : 3 * k + 3 < n) :
    MvPolynomial.pderiv (rowLeft_u n k hk1 hk2)
        (boolFactorPoly n ⟨3 * k + 1, by omega⟩) = 0 := by
  apply pderiv_one_sub_boolLC_factor_of_ne
  intro h
  have := congr_arg Fin.val h
  rw [rowLeft_u_val] at this
  simp only [Fin.val_mk] at this
  omega

theorem pderiv_u_boolFactor_3k2_zero (n : Nat) (k : Nat) (hk1 : 1 ≤ k)
    (hk2 : 3 * k + 3 < n) :
    MvPolynomial.pderiv (rowLeft_u n k hk1 hk2)
        (boolFactorPoly n ⟨3 * k + 2, by omega⟩) = 0 := by
  apply pderiv_one_sub_boolLC_factor_of_ne
  intro h
  have := congr_arg Fin.val h
  rw [rowLeft_u_val] at this
  simp only [Fin.val_mk] at this
  omega

/-- For our `v = 3k`, `pderiv v (boolFactor 3k) = -1 + 2 X_{3k}`. -/
theorem pderiv_v_boolFactor_3k (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.pderiv (rowLeft_v n k hk2)
        (boolFactorPoly n ⟨3 * k, by omega⟩) =
      -1 + 2 * MvPolynomial.X (⟨3 * k, by omega⟩ : Fin n) := by
  -- `rowLeft_v = ⟨3*k⟩` as a Fin, equal to the bool-factor index.
  have heq : rowLeft_v n k hk2 = (⟨3 * k, by omega⟩ : Fin n) := by
    apply Fin.ext
    rw [rowLeft_v_val]
  rw [heq]
  exact pderiv_one_sub_boolLC_factor_self _

theorem pderiv_v_boolFactor_3k1_zero (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.pderiv (rowLeft_v n k hk2)
        (boolFactorPoly n ⟨3 * k + 1, by omega⟩) = 0 := by
  apply pderiv_one_sub_boolLC_factor_of_ne
  intro h
  have := congr_arg Fin.val h
  rw [rowLeft_v_val] at this
  simp only [Fin.val_mk] at this
  omega

theorem pderiv_v_boolFactor_3k2_zero (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.pderiv (rowLeft_v n k hk2)
        (boolFactorPoly n ⟨3 * k + 2, by omega⟩) = 0 := by
  apply pderiv_one_sub_boolLC_factor_of_ne
  intro h
  have := congr_arg Fin.val h
  rw [rowLeft_v_val] at this
  simp only [Fin.val_mk] at this
  omega

/-! ## Section I: pderiv u, v applied to second-derivative bool factors

The double-pderiv form `pderiv v (pderiv u f)` for bool factors:
* If `u, v` both equal `a`, result is `2`.
* Otherwise zero. -/

/-- `pderiv v (pderiv u (boolFactor a)) = 0` for all bool indices `a`
in the touched-list (3k, 3k+1, 3k+2), since `u ≠ a` always. -/
theorem pderiv_v_pderiv_u_boolFactor_zero (n : Nat) (k : Nat) (hk1 : 1 ≤ k)
    (hk2 : 3 * k + 3 < n) (a : Fin n) (ha : a.val = 3 * k ∨
      a.val = 3 * k + 1 ∨ a.val = 3 * k + 2) :
    MvPolynomial.pderiv (rowLeft_v n k hk2)
        (MvPolynomial.pderiv (rowLeft_u n k hk1 hk2)
          (boolFactorPoly n a)) = 0 := by
  apply pderiv_w_pderiv_v_one_sub_boolLC_factor_first_diff
  -- Need: rowLeft_u ≠ a
  intro h
  have := congr_arg Fin.val h
  rw [rowLeft_u_val] at this
  rcases ha with ha | ha | ha
  · rw [ha] at this; omega
  · rw [ha] at this; omega
  · rw [ha] at this; omega


/-! ## Axiom audit (Sections G, H, I) -/

#print axioms rowLeft_u
#print axioms rowLeft_v
#print axioms rowLeft_u_val
#print axioms rowLeft_v_val
#print axioms rowLeft_u_ne_rowLeft_v
#print axioms pderiv_u_boolFactor_3k_zero
#print axioms pderiv_u_boolFactor_3k1_zero
#print axioms pderiv_u_boolFactor_3k2_zero
#print axioms pderiv_v_boolFactor_3k
#print axioms pderiv_v_boolFactor_3k1_zero
#print axioms pderiv_v_boolFactor_3k2_zero
#print axioms pderiv_v_pderiv_u_boolFactor_zero

end BridgeAKappaTwoIdentityFourAux

end PallLean.Paper93.Paper283
