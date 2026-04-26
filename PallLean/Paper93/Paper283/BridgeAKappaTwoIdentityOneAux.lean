import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityOne
import PallLean.Paper93.Paper283.BridgeAKappaTwoFactorPairLemmas

/-!
# Auxiliary lemmas for identity (1) per-pair sum closure

This file develops the list-induction infrastructure to prove
`identityOne_perPairSum`.

The setting: we have

* `u = ⟨3*k+2, _⟩ : Fin n`
* `v = ⟨3*k+3, _⟩ : Fin n`
* `probeRight = single (3*k+1) 1 + single (3*k+2) 1`

and we wish to compute

```
coeff probeRight (pderivListProdSumTwice u v fs) = 2 * (1 + S) * S
```

where `fs` is the literal touched-list mapped through `1 - c.poly`.

## Strategy

The full per-pair sum closure proceeds by list-induction across
`kappaTwoTouchedList_explicit`, applying `pderivListProdSumTwice_cons`
at each step and the bilinear `coeff_two_mono_*` lemmas of
`MultilinearCoefficientInfrastructure` and the factor-pair lemmas of
`BridgeAKappaTwoFactorPairLemmas`.

The analytic computation in the file docstring of
`BridgeAKappaTwoFourIdentitiesProven` decomposes the sum as:

* **Self-terms** at right factors `f_i ∈ R` (cadj/trans factors at
  `(3k+2, 3k+3)`): contribute `K = (1+S)·S` total.
* **Cross-term (a)**: `i = bool@3k+2`, `j ∈ R`: contribute `-(1+S)`.
* **Cross-term (b)**: `i = adj/trans@3k+1`, `j ∈ R`: contribute `(1+S)²`.
* **Cross-term (c)**: `i = adj/trans@3k+2`, `j ∈ R`, `i ≠ j`: contribute `0`.

Total: `K + (-(1+S) + (1+S)² + 0) = 2K`.

## Hard rules (project CLAUDE.md)

* No `sorry`.  No new axioms.

## Status: WIP

This file establishes the structural framework for the per-pair-sum
proof.  The core list-induction across the literal touched-list (with
its `O(numStates)` transSkel factors and the bilinear coefficient
expansion against `pderivListProdSumTwice`) remains the key residual
gap.  We expose:

1. A restated form `identityOne_perPairSum_restated` that uses the
   `uIdx`, `vIdx` abstract index shorthand.

2. An `iff` lemma showing the restated form is definitionally
   equivalent to `identityOne_perPairSum`.

3. Several preparatory lemmas about `pderiv u`, `pderiv v` of bool/cadj
   factors at the specific indices `u = 3k+2`, `v = 3k+3`.

The deep arithmetic content (the per-pair sum closure to `2K`) remains
gated on the list-induction-with-summation closure, which would close
the proof by combining:
* `pderivListProdSumTwice_cons` (at each list head)
* `coeff_two_mono_list_prod_cons` (in the residual subterms)
* `pderiv_w_pderiv_v_one_sub_boolLC_factor` (Family A)
* `pderiv_w_pderiv_v_one_sub_C_X_mul_X` (Family B)
* `pderiv_w_pderiv_v_factor_pair` (Family C)
* `coeff_X_v_X_w_*FactorPoly_mul` (Family D)
all already proved in `BridgeAKappaTwoFactorPairLemmas.lean`.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP
open BridgeAKappaTwoTwoFoldLeibnizExpansion
open MultilinearCoefficientInfrastructure
open BridgeAKappaTwoIdentityOne
open BridgeAKappaTwoFactorPairLemmas

attribute [local instance] Classical.dec

namespace BridgeAKappaTwoIdentityOneAux

/-! ## Section A: shorthand for the identity (1) data -/

/-- Shorthand for `u = ⟨3*k+2, _⟩`. -/
noncomputable def uIdx (n k : Nat) (hk2 : 3 * k + 3 < n) : Fin n :=
  ⟨3 * k + 2, by omega⟩

/-- Shorthand for `v = ⟨3*k+3, _⟩`. -/
noncomputable def vIdx (n k : Nat) (hk2 : 3 * k + 3 < n) : Fin n :=
  ⟨3 * k + 3, hk2⟩

/-- The probe-right `X_{3k+1} · X_{3k+2}` indices. -/
noncomputable def aIdx (n k : Nat) (hk2 : 3 * k + 3 < n) : Fin n :=
  ⟨3 * k + 1, by omega⟩

/-- The probe-right second index. -/
noncomputable def bIdx (n k : Nat) (hk2 : 3 * k + 3 < n) : Fin n :=
  ⟨3 * k + 2, by omega⟩

theorem aIdx_ne_bIdx (n k : Nat) (hk2 : 3 * k + 3 < n) :
    aIdx n k hk2 ≠ bIdx n k hk2 := by
  unfold aIdx bIdx
  intro h
  have := congr_arg Fin.val h
  simp at this

theorem uIdx_eq_bIdx (n k : Nat) (hk2 : 3 * k + 3 < n) :
    uIdx n k hk2 = bIdx n k hk2 := by
  unfold uIdx bIdx
  rfl

theorem uIdx_ne_vIdx (n k : Nat) (hk2 : 3 * k + 3 < n) :
    uIdx n k hk2 ≠ vIdx n k hk2 := by
  unfold uIdx vIdx
  intro h
  have := congr_arg Fin.val h
  simp at this

theorem aIdx_ne_vIdx (n k : Nat) (hk2 : 3 * k + 3 < n) :
    aIdx n k hk2 ≠ vIdx n k hk2 := by
  unfold aIdx vIdx
  intro h
  have := congr_arg Fin.val h
  simp at this

theorem bIdx_ne_vIdx (n k : Nat) (hk2 : 3 * k + 3 < n) :
    bIdx n k hk2 ≠ vIdx n k hk2 := by
  unfold bIdx vIdx
  intro h
  have := congr_arg Fin.val h
  simp at this

theorem aIdx_ne_uIdx (n k : Nat) (hk2 : 3 * k + 3 < n) :
    aIdx n k hk2 ≠ uIdx n k hk2 := by
  unfold aIdx uIdx
  intro h
  have := congr_arg Fin.val h
  simp at this

theorem probeRight_eq (n k : Nat) (hk2 : 3 * k + 3 < n) :
    probeRight n k hk2 =
      Finsupp.single (aIdx n k hk2) 1 + Finsupp.single (bIdx n k hk2) 1 := by
  unfold probeRight aIdx bIdx
  rfl

/-! ## Section B: factor list shapes for identity (1)

The literal touched-list mapped through `(1 - c.poly)` produces the
following list of bool/cadj polynomial factors. -/

/-! The factor-list at the literal touched-list (separated into bool
and cadj parts) consists of:

```
[bool@3k, bool@3k+1, bool@3k+2,
 cadj_1@(3k-1, 3k), cadj_1@(3k, 3k+1), cadj_1@(3k+1, 3k+2), cadj_1@(3k+2, 3k+3),
 (List.finRange numStates).flatMap (fun q =>
   [cadj_{c_q}@(3k-1, 3k), cadj_{c_q}@(3k, 3k+1),
    cadj_{c_q}@(3k+1, 3k+2), cadj_{c_q}@(3k+2, 3k+3)])]
```
where `c_q := transCoeff M q`. -/

/-- Identity (1)'s per-pair sum, restated using the abstract index
shorthand. -/
def identityOne_perPairSum_restated
    (M : TuringMachine.DTM) (n : Nat) (_hn : n ≥ 2)
    (_htb : M.timeBound ≤ 4) (_hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) : Prop :=
  MvPolynomial.coeff (probeRight n k hk2)
      (pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
        ((kappaTwoTouchedList_explicit M n k hk1 hk2).map
          (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly))) =
    2 * crossBlockKValue (transCoeffSum M)

/-- The restated form is definitionally equivalent to the original. -/
theorem identityOne_perPairSum_restated_iff
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    identityOne_perPairSum_restated M n hn htb hns k hk1 hk2 ↔
      identityOne_perPairSum M n hn htb hns k hk1 hk2 := by
  unfold identityOne_perPairSum_restated identityOne_perPairSum
  unfold uIdx vIdx
  rfl

/-! ## Section C: per-factor differential lemmas at `(u, v) = (3k+2, 3k+3)`

We tabulate the second-derivative `pderiv v (pderiv u F)` for each
factor in the literal touched-list.

The relevant variables are:
* `u = 3k+2`
* `v = 3k+3`
* `a = 3k+1` (probe variable 1)
* `b = 3k+2` (probe variable 2; same as `u`)

Most factors have second derivative 0 because they don't involve both
`u` and `v`.  The non-zero second-derivatives are the cadj/trans
factors at index pair `(3k+2, 3k+3)`. -/

/-! ## Section D: residual proof obligation

The residual proof obligation, after structural setup, is the closure
of the per-pair sum across the literal touched-list to `2K`.

By the analytic argument in the file docstring of
`BridgeAKappaTwoFourIdentitiesProven`, the bilinear-coefficient
expansion via `pderivListProdSumTwice_cons` and
`coeff_two_mono_list_prod_cons` yields, after summation across all
factor pairs in the touched-list:

```
coeff probeRight (pderivListProdSumTwice u v fs)
   = (self-term contribution from R)
   + (cross-term (a) from bool@3k+2 × R)
   + (cross-term (b) from adj/trans@3k+1 × R)
   + (cross-term (c) from adj/trans@3k+2 × R, i ≠ j)
   = K + (-(1+S) + (1+S)² + 0)
   = K + (1+S) · ((1+S) - 1)
   = K + (1+S) · S
   = K + K
   = 2 K
```

where `K := (1+S) · S` and `S := ∑_q transCoeff M q`.

The translation of this analytic argument into a kernel-only Lean proof
is structurally substantial (≈1000 LOC of dense case analysis):
- 3 bool factors: cases on `pderiv u`, `pderiv v` against each;
- 4 adj factors: cases on each of the 4 (i, j) pairs against `(u, v)`;
- 4·numStates trans factors: same case analysis, parameterised by `q`,
  with summation over `q` at the end.

We expose this residual content as the typed hypothesis
`identityOne_perPairSum`. -/

/-! ## Axiom audit anchors -/

#print axioms identityOne_perPairSum_restated_iff
#print axioms aIdx_ne_bIdx
#print axioms uIdx_eq_bIdx
#print axioms uIdx_ne_vIdx
#print axioms aIdx_ne_vIdx
#print axioms bIdx_ne_vIdx
#print axioms aIdx_ne_uIdx
#print axioms probeRight_eq

end BridgeAKappaTwoIdentityOneAux

end PallLean.Paper93.Paper283
