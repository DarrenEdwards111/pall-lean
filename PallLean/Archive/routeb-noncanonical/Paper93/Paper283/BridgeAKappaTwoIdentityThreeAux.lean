import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityThree
import PallLean.Paper93.Paper283.BridgeAKappaTwoFactorPairLemmas

/-!
# Auxiliary lemmas for identity (3) per-pair sum closure

This file develops the list-induction infrastructure to discharge
`identityThree_perPairSum`.

## Setting

For identity (3) we have:
* `u = ⟨3*k+2, _⟩ : Fin n` (first derivative coord)
* `v = ⟨3*k+3, _⟩ : Fin n` (second derivative coord)
* `probeLeft = single (3*k) 1 + single (3*k+1) 1` (target monomial)

and we wish to compute

```
coeff probeLeft (pderivListProdSumTwice u v fs) = (1 + S) * S = K
```

where `fs` is the literal touched-list mapped through `1 - c.poly`.

## Analytic decomposition: identity (3) is a *self-term-only* identity

Unlike identity (1) (probeRight × rowRight), identity (3) has the
crucial feature that **all cross-term contributions vanish**: the
probe `{3k, 3k+1}` and the differentiation indices `{3k+2, 3k+3}`
are disjoint, so any cross-term `(∂_u f_i)(∂_v f_j) · ∏ rest`
contributes a polynomial whose lowest-degree relevant monomial
already carries an `X_{3k+2}` (from `∂_u f_i`) plus
an `X_{3k+3}` factor (from `∂_v f_j`), neither of which can be
cancelled by the multilinear residual product `∏ rest` to recover
`X_{3k} · X_{3k+1}`.  Concretely:

* **Case (a)**: `f_i = bool@3k+2`, `f_j ∈ R` (factors carrying
  `X_{3k+3}`).  `(∂_u f_i)(∂_v f_j) = (2X_{3k+2}-1)(-c_j X_{3k+2})`,
  contains `X_{3k+2}` factor.  Coeff at `X_{3k}·X_{3k+1}` is `0`
  because the residual product cannot supply a negative-exponent
  factor.
* **Case (b)**: `f_i = adj/trans@3k+1`, `f_j ∈ R`.  Product is
  `c_i c_j X_{3k+1} X_{3k+2}`.  Residual product cannot supply
  `X_{3k} / X_{3k+2}`.  Contribution: `0`.
* **Case (c)**: `f_i ∈ R \ {f_j}` (so `f_i = adj/trans@3k+2` with
  `i ≠ j`).  Product is `c_i c_j X_{3k+2} X_{3k+3}`.  Residual cannot
  supply `X_{3k} X_{3k+1} / (X_{3k+2} X_{3k+3})`.  Contribution: `0`.

Hence the entire identity (3) value comes from the **self-term**
`Σ_{i ∈ R} (∂_u ∂_v f_i) · ∏_{ℓ ≠ i} f_ℓ`:

* `∂_u ∂_v f_i = -c_i` for each `i ∈ R`.
* `coeff(X_{3k}·X_{3k+1}, ∏ rest) = -(1 + S) + 1 = -S`, where:
  * `-(1+S)` comes from the `1 - c'·X_{3k}·X_{3k+1}` factors
    (i.e., `adj@3k` with `c' = 1` and `trans@3k` for each `q` with
    `c' = transCoeff M q`, summing `(1 + S)`).
  * `+1` comes from the bool@3k × bool@3k+1 cross-talk term in the
    bilinear coefficient (each contributes `coeff(X_·, ·) = -1`,
    cross product `(-1)(-1) = +1`).

Total self-term: `Σ_{i ∈ R} (-c_i) · (-S) = S · (1 + S) = K`.

Per the "honest partial progress beats 1000-line case analysis"
directive (file docstring of `BridgeAKappaTwoFourIdentitiesProven`),
this file builds the structural framework for the per-pair sum
closure and exposes the residual obstructions as named
sub-hypotheses, mirroring the `BridgeAKappaTwoIdentityOneAux`
pattern.

## Hard rules (project CLAUDE.md)

* No `sorry`.  No new axioms.

## Status: WIP

The file builds the analytic framework and a restated form for
`identityThree_perPairSum`.  The list-induction over the literal
touched-list (≈ `7 + 4·numStates` factors) remains the residual gap.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP
open BridgeAKappaTwoTwoFoldLeibnizExpansion
open MultilinearCoefficientInfrastructure
open BridgeAKappaTwoIdentityOne
open BridgeAKappaTwoIdentityFour
open BridgeAKappaTwoIdentityThree
open BridgeAKappaTwoFactorPairLemmas

attribute [local instance] Classical.dec

namespace BridgeAKappaTwoIdentityThreeAux

/-! ## Section A: shorthand for the identity (3) data -/

/-- Shorthand for `u = ⟨3*k+2, _⟩` (first derivative coord). -/
noncomputable def uIdx (n k : Nat) (hk2 : 3 * k + 3 < n) : Fin n :=
  ⟨3 * k + 2, by omega⟩

/-- Shorthand for `v = ⟨3*k+3, _⟩` (second derivative coord). -/
noncomputable def vIdx (n k : Nat) (hk2 : 3 * k + 3 < n) : Fin n :=
  ⟨3 * k + 3, hk2⟩

/-- The probe-left index `3k` (first probe coord). -/
noncomputable def aIdx (n k : Nat) (hk2 : 3 * k + 3 < n) : Fin n :=
  ⟨3 * k, by omega⟩

/-- The probe-left index `3k+1` (second probe coord). -/
noncomputable def bIdx (n k : Nat) (hk2 : 3 * k + 3 < n) : Fin n :=
  ⟨3 * k + 1, by omega⟩

/-! ## Section B: distinctness facts for the four indices `{3k, 3k+1, 3k+2, 3k+3}` -/

theorem aIdx_ne_bIdx (n k : Nat) (hk2 : 3 * k + 3 < n) :
    aIdx n k hk2 ≠ bIdx n k hk2 := by
  unfold aIdx bIdx
  intro h
  have := congr_arg Fin.val h
  simp at this

theorem aIdx_ne_uIdx (n k : Nat) (hk2 : 3 * k + 3 < n) :
    aIdx n k hk2 ≠ uIdx n k hk2 := by
  unfold aIdx uIdx
  intro h
  have := congr_arg Fin.val h
  simp at this

theorem aIdx_ne_vIdx (n k : Nat) (hk2 : 3 * k + 3 < n) :
    aIdx n k hk2 ≠ vIdx n k hk2 := by
  unfold aIdx vIdx
  intro h
  have := congr_arg Fin.val h
  simp at this

theorem bIdx_ne_uIdx (n k : Nat) (hk2 : 3 * k + 3 < n) :
    bIdx n k hk2 ≠ uIdx n k hk2 := by
  unfold bIdx uIdx
  intro h
  have := congr_arg Fin.val h
  simp at this

theorem bIdx_ne_vIdx (n k : Nat) (hk2 : 3 * k + 3 < n) :
    bIdx n k hk2 ≠ vIdx n k hk2 := by
  unfold bIdx vIdx
  intro h
  have := congr_arg Fin.val h
  simp at this

theorem uIdx_ne_vIdx (n k : Nat) (hk2 : 3 * k + 3 < n) :
    uIdx n k hk2 ≠ vIdx n k hk2 := by
  unfold uIdx vIdx
  intro h
  have := congr_arg Fin.val h
  simp at this

/-- The four indices `{3k, 3k+1, 3k+2, 3k+3}` are pairwise distinct. -/
theorem four_indices_pairwise_distinct (n k : Nat) (hk2 : 3 * k + 3 < n) :
    aIdx n k hk2 ≠ bIdx n k hk2 ∧
    aIdx n k hk2 ≠ uIdx n k hk2 ∧
    aIdx n k hk2 ≠ vIdx n k hk2 ∧
    bIdx n k hk2 ≠ uIdx n k hk2 ∧
    bIdx n k hk2 ≠ vIdx n k hk2 ∧
    uIdx n k hk2 ≠ vIdx n k hk2 :=
  ⟨aIdx_ne_bIdx n k hk2,
   aIdx_ne_uIdx n k hk2,
   aIdx_ne_vIdx n k hk2,
   bIdx_ne_uIdx n k hk2,
   bIdx_ne_vIdx n k hk2,
   uIdx_ne_vIdx n k hk2⟩

/-- The probe-left equals `single aIdx 1 + single bIdx 1`. -/
theorem probeLeft_eq (n k : Nat) (hk2 : 3 * k + 3 < n) :
    probeLeft n k hk2 =
      Finsupp.single (aIdx n k hk2) 1 + Finsupp.single (bIdx n k hk2) 1 := by
  unfold probeLeft aIdx bIdx
  rfl

/-! ## Section C: structural framework for the per-pair sum

We expose the analytic-skeleton claim as an explicit theorem
statement, which is the residual content of `identityThree_perPairSum`.
The full proof requires the `O(numStates)`-deep list induction
across the literal touched-list, which we document as the closing-step
requirement. -/

/-- Identity (3)'s per-pair sum, restated using the abstract index
shorthand `(uIdx, vIdx)` and the explicit `probeLeft`. -/
def identityThree_perPairSum_restated
    (M : TuringMachine.DTM) (n : Nat) (_hn : n ≥ 2)
    (_htb : M.timeBound ≤ 4) (_hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) : Prop :=
  MvPolynomial.coeff (probeLeft n k hk2)
      (pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
        ((kappaTwoTouchedList_explicit M n k hk1 hk2).map
          (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly))) =
    crossBlockKValue (transCoeffSum M)

/-- The restated form is identical to the original. -/
theorem identityThree_perPairSum_restated_iff
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    identityThree_perPairSum_restated M n hn htb hns k hk1 hk2 ↔
      identityThree_perPairSum M n hn htb hns k hk1 hk2 := by
  unfold identityThree_perPairSum_restated identityThree_perPairSum
  unfold uIdx vIdx
  rfl

/-! ## Section D: documentation of the analytic-skeleton path for identity (3)

The full per-pair sum closure for identity (3) proceeds by
list-induction across `kappaTwoTouchedList_explicit`, applying
`pderivListProdSumTwice_cons` at each step and the bilinear
`coeff_two_mono_*` lemmas of `MultilinearCoefficientInfrastructure`
together with the factor-pair lemmas of
`BridgeAKappaTwoFactorPairLemmas`.

The computation is heavily case-dependent on the head factor; here
we tabulate **per-factor contribution** to the per-pair sum.

For identity (3) (probeLeft × rowRight), with row indices
`(u, v) = (3k+2, 3k+3)` and probe indices `(a, b) = (3k, 3k+1)`:

### Boolean factors

* `bool@3k`: `∂_u (bool@3k) = 0` (since `3k ≠ 3k+2`).  Bool factor has
  bilinear coeff `0` (Family D `coeff_X_v_X_w_boolFactorPoly`) and
  constant coeff `1` (`coeff_zero_boolFactorPoly`).  Self-term: `0`.
  Cross-term: contributes via the `+1` cross-talk term in
  `coeff(probeLeft, ∏ rest)` calculation, paired with bool@3k+1.
* `bool@3k+1`: similar to bool@3k, contributes via cross-talk pair.
* `bool@3k+2`: `∂_u (bool@3k+2) = 2 X_{3k+2} - 1` (Family A
  `pderiv_one_sub_boolLC_factor_self`).  But `(2 X_{3k+2} - 1) ·
  (∂_v f_j) · ∏ rest` has `X_{3k+2}` factor which cannot be cancelled
  to give `X_{3k} X_{3k+1}`.  Contribution: `0`.

### Adjacency / transition factors

* `adj@3k-1` (carries `X_{3k-1}, X_{3k}`): `∂_u = ∂_v = 0` (no overlap
  with `{3k+2, 3k+3}`).  Bilinear coeff `coeff(X_{3k}·X_{3k+1}, ·)`:
  `0` (since `{3k-1, 3k} ≠ {3k, 3k+1}` as multilinear monomial).
  Constant coeff `1` (`coeff_zero_cadjFactorPoly`).  Contribution: `0`.
* `adj@3k` (carries `X_{3k}, X_{3k+1}`): bilinear coeff at probe is
  `-1` (matches as multilinear monomial).  No derivative effect.
  Cross-term contribution: paired with derivative factors, gives
  `-1 · (∂_u · ∂_v sub-product coefficient)`.  Self-term: `0`.
  Direct contribution to bilinear `coeff(probeLeft, rest)`: `-1`.
* `adj@3k+1` (carries `X_{3k+1}, X_{3k+2}`): `∂_u (adj@3k+1) =
  -X_{3k+1}` (Family B `pderiv_one_sub_C_X_mul_X_at_snd`).
  In a cross-term `(∂_u f_i)(∂_v f_j)`, we get `(-X_{3k+1})·
  (-c_j X_{3k+2}) = c_j X_{3k+1} X_{3k+2}` — but `X_{3k+2}` factor
  cannot be cancelled to give probe.  Contribution: `0`.
* `adj@3k+2` (carries `X_{3k+2}, X_{3k+3}`): `∂_u ∂_v (adj@3k+2) =
  -1` (Family B `pderiv_w_pderiv_v_one_sub_C_X_mul_X_ij`).  Self-term
  contribution: `(-1) · coeff(X_{3k}·X_{3k+1}, ∏ rest where adj@3k+2
  is removed)`.

  Cross-term contributions involving `i = adj@3k+2`: as case (c) above,
  vanish.  As case where `j = adj@3k+2` and `i ≠ adj@3k+2`: `(∂_u f_i)
  · (-X_{3k+2})`, only nonzero contribution requires `∂_u f_i` with
  `X_{3k+1}` (so `i = adj/trans@3k+1`), giving `c_i X_{3k+1} X_{3k+2}` —
  `X_{3k+2}` cannot be cancelled.  All cross-term contributions: `0`.

* `trans@3k-1` (carries `X_{3k-1}, X_{3k}` with coeff `c_q`): same as
  `adj@3k-1`, contribution `0`.
* `trans@3k`: same as `adj@3k`, contributes `-c_q` to the bilinear
  `coeff(probeLeft, ∏)` (one per `q`).
* `trans@3k+1`: same as `adj@3k+1`, contribution `0`.
* `trans@3k+2`: same as `adj@3k+2`, self-term `(-c_q) · coeff(probeLeft,
  rest)` (one per `q`).

### Total assembly

* **Cross-term sum**: all contributions are `0` (cases (a), (b), (c)
  above).
* **Self-term sum**: `Σ_{i ∈ R} (-c_i) · coeff(X_{3k}·X_{3k+1}, rest_i)`
  where `R = {adj@3k+2} ∪ {trans@3k+2_q : q : Fin numStates}` and
  `rest_i` is the touched-list with `i` removed.

  For each `i ∈ R`, `coeff(X_{3k}·X_{3k+1}, rest_i)`:
  * Adjacency/transition factor `1 - c'·X_{3k}·X_{3k+1}` (i.e.,
    `adj@3k` with `c' = 1`, `trans@3k_q` for each `q` with `c' = c_q`):
    each contributes `-c'` to the bilinear coeff, summing `-(1 + S)`.
  * Bool@3k × bool@3k+1 cross-talk: each bool factor has linear coeff
    `-1` at its index variable, cross product `(-1)(-1) = +1`.
  * Other factors contribute `0`.

  Total: `coeff(X_{3k}·X_{3k+1}, rest_i) = -(1 + S) + 1 = -S` (same
  for all `i ∈ R`).

* **Total**: `Σ_{i ∈ R} (-c_i) · (-S) = S · (1 + S) = K`.

This matches the expected closed form `crossBlockKValue (transCoeffSum M) = K`.

## Status of formalisation

The closing of the per-pair-sum at the kernel level still requires
list-induction over the literal touched-list in
`pderivListProdSumTwice`.  We expose the structural sub-claims as
named hypotheses, allowing further refinement without touching the
already-closed reductions in `BridgeAKappaTwoIdentityThree`. -/

/-! ## Section E: structural sub-hypotheses (analytical skeleton)

We package the **analytical skeleton claim** for identity (3) as a
single Prop; this Prop is mathematically equivalent to
`identityThree_perPairSum`, but expressed in the shorthand of this
file. -/

/-- The analytic-skeleton claim for identity (3): cross-term
contributions vanish, self-term contributions sum to `K`. -/
def identityThree_analytic_skeleton_claim
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) : Prop :=
  identityThree_perPairSum_restated M n hn htb hns k hk1 hk2

theorem identityThree_analytic_skeleton_iff_perPairSum
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    identityThree_analytic_skeleton_claim M n hn htb hns k hk1 hk2 ↔
      identityThree_perPairSum M n hn htb hns k hk1 hk2 := by
  unfold identityThree_analytic_skeleton_claim
  exact identityThree_perPairSum_restated_iff M n hn htb hns k hk1 hk2

/-! ## Section F: identity-(3)-specific facts about row/probe disjointness

The key analytic property of identity (3) is that the row indices
`{3k+2, 3k+3}` are **disjoint** from the probe indices `{3k, 3k+1}`.
This disjointness underlies all the cross-term-vanishing arguments. -/

/-- Row indices and probe indices are disjoint for identity (3). -/
theorem rowRight_probeLeft_disjoint
    (n k : Nat) (hk2 : 3 * k + 3 < n) :
    aIdx n k hk2 ≠ uIdx n k hk2 ∧
    aIdx n k hk2 ≠ vIdx n k hk2 ∧
    bIdx n k hk2 ≠ uIdx n k hk2 ∧
    bIdx n k hk2 ≠ vIdx n k hk2 :=
  ⟨aIdx_ne_uIdx n k hk2,
   aIdx_ne_vIdx n k hk2,
   bIdx_ne_uIdx n k hk2,
   bIdx_ne_vIdx n k hk2⟩

/-! ## Section G: kappa-2 touched-list structural facts

The following lemmas record the **literal length** of the touched
list for an interior block — `7 + 4·numStates` factors.  This is
the inductive parameter for the list induction. -/

/-- The number of boolean factors in the touched list at an interior
block is `3`. -/
theorem touchedList_boolFactors_length (n k : Nat) (hk1 : 1 ≤ k)
    (hk2 : 3 * k + 3 < n) :
    (kappaTwoTouchedList_boolFactors n k hk1 hk2).length = 3 := by
  unfold kappaTwoTouchedList_boolFactors
  rfl

/-- The number of adjacency factors in the touched list at an interior
block is `4`. -/
theorem touchedList_adjFactors_length (n k : Nat) (hk1 : 1 ≤ k)
    (hk2 : 3 * k + 3 < n) :
    (kappaTwoTouchedList_adjFactors n k hk1 hk2).length = 4 := by
  unfold kappaTwoTouchedList_adjFactors
  rfl

/-- The number of transition-skeleton factors per state in the touched
list at an interior block is `4`. -/
theorem touchedList_transSkelFactorsForState_length
    (M : TuringMachine.DTM) (n : Nat) (q : Fin M.numStates)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    (kappaTwoTouchedList_transSkelFactorsForState M n q k hk1 hk2).length
      = 4 := by
  unfold kappaTwoTouchedList_transSkelFactorsForState
  rfl

/-- The number of transition-skeleton factors (flattened across states)
in the touched list at an interior block is `4 · numStates`. -/
theorem touchedList_transSkelFactorsFlat_length
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    (kappaTwoTouchedList_transSkelFactorsFlat M n k hk1 hk2).length
      = 4 * M.numStates := by
  unfold kappaTwoTouchedList_transSkelFactorsFlat
  rw [List.length_flatMap]
  -- Σ (q : Fin numStates), 4 = 4 * numStates
  have h : (List.finRange M.numStates).map
      (fun q => (kappaTwoTouchedList_transSkelFactorsForState
                  M n q k hk1 hk2).length)
       =
      List.replicate M.numStates 4 := by
    rw [show List.replicate M.numStates (4 : Nat) =
          (List.finRange M.numStates).map (fun _ => 4) from ?_]
    · apply List.map_congr_left
      intro q _
      exact touchedList_transSkelFactorsForState_length M n q k hk1 hk2
    · rw [List.map_const']
      rw [List.length_finRange]
  rw [h]
  rw [List.sum_replicate]
  -- numStates • 4 = numStates * 4 = 4 * numStates
  rw [smul_eq_mul]
  ring

/-- The total length of the touched list at an interior block is
`7 + 4 · numStates`. -/
theorem touchedList_explicit_length
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    (kappaTwoTouchedList_explicit M n k hk1 hk2).length
      = 7 + 4 * M.numStates := by
  unfold kappaTwoTouchedList_explicit
  rw [List.length_append, List.length_append]
  rw [touchedList_boolFactors_length n k hk1 hk2]
  rw [touchedList_adjFactors_length n k hk1 hk2]
  rw [touchedList_transSkelFactorsFlat_length M n k hk1 hk2]

/-! ## Section H: stray-`X_u` annihilation lemmas

These lemmas formalise the **cross-term-vanishing** argument from
Section D.  The key analytical fact is that any polynomial of the
form `X_u · r` has its bilinear coefficient at `X_a · X_b`
identically zero whenever `u ∉ {a, b}`: multiplying by `X_u`
forces every monomial of `X_u · r` to carry a positive `u`-exponent,
which cannot match the multilinear monomial `X_a · X_b` (which has
zero `u`-exponent).

Combined with `pderiv_one_sub_C_X_mul_X_at_*` (Family B) and
`pderiv_one_sub_boolLC_factor_self` (Family A), these lemmas
discharge the cross-term contributions to `pderivListProdSumTwice`
expanded at `probeLeft = X_{3k} · X_{3k+1}` with row indices
`(u, v) = (3k+2, 3k+3)`.
-/

/-- **Stray `X_u` annihilation, generic**: if `u ∉ {a, b}` (i.e.,
`u ≠ a` and `u ≠ b`), then the bilinear coefficient of `X_u · p`
at the multilinear monomial `X_a · X_b` is `0` for any polynomial
`p`. -/
theorem coeff_X_a_X_b_X_u_mul_zero {N : ℕ}
    (a b u : Fin N) (p : MvPolynomial (Fin N) ℚ)
    (hua : u ≠ a) (hub : u ≠ b) :
    MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
        (MvPolynomial.X u * p) = 0 := by
  classical
  rw [MvPolynomial.coeff_X_mul' (Finsupp.single a 1 + Finsupp.single b 1) u p]
  rw [if_neg]
  -- Goal: u ∉ (single a 1 + single b 1).support
  intro hmem
  rw [Finsupp.mem_support_iff] at hmem
  apply hmem
  rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
  rw [if_neg hua.symm, if_neg hub.symm]
  rfl

/-- **Stray `X_u` annihilation, post-multiplied form**: if `u ∉ {a, b}`,
then the bilinear coefficient of `p · X_u · q` at `X_a · X_b` is `0`. -/
theorem coeff_X_a_X_b_p_X_u_q_zero {N : ℕ}
    (a b u : Fin N) (p q : MvPolynomial (Fin N) ℚ)
    (hua : u ≠ a) (hub : u ≠ b) :
    MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
        (p * MvPolynomial.X u * q) = 0 := by
  -- p * X u * q = X u * (p * q)
  have heq :
      (p * MvPolynomial.X u * q : MvPolynomial (Fin N) ℚ) =
      MvPolynomial.X u * (p * q) := by
    ring
  rw [heq]
  exact coeff_X_a_X_b_X_u_mul_zero a b u (p * q) hua hub

/-- **Stray `X_u` annihilation with rational coefficient**: if `u ∉ {a, b}`,
then the bilinear coefficient of `C c · X_u · p` at `X_a · X_b` is `0`. -/
theorem coeff_X_a_X_b_C_c_X_u_mul_zero {N : ℕ}
    (a b u : Fin N) (c : ℚ) (p : MvPolynomial (Fin N) ℚ)
    (hua : u ≠ a) (hub : u ≠ b) :
    MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
        (MvPolynomial.C c * MvPolynomial.X u * p) = 0 := by
  have heq :
      (MvPolynomial.C c * MvPolynomial.X u * p : MvPolynomial (Fin N) ℚ) =
      MvPolynomial.X u * (MvPolynomial.C c * p) := by
    ring
  rw [heq]
  exact coeff_X_a_X_b_X_u_mul_zero a b u (MvPolynomial.C c * p) hua hub

/-- **Stray `X_u²` annihilation**: if `u ∉ {a, b}`, then the bilinear
coefficient of `X_u² · p` at `X_a · X_b` is `0`. -/
theorem coeff_X_a_X_b_X_u_sq_mul_zero {N : ℕ}
    (a b u : Fin N) (p : MvPolynomial (Fin N) ℚ)
    (hua : u ≠ a) (hub : u ≠ b) :
    MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
        (MvPolynomial.X u * MvPolynomial.X u * p) = 0 := by
  -- X u * X u * p = X u * (X u * p)
  have heq :
      (MvPolynomial.X u * MvPolynomial.X u * p : MvPolynomial (Fin N) ℚ) =
      MvPolynomial.X u * (MvPolynomial.X u * p) := by
    ring
  rw [heq]
  exact coeff_X_a_X_b_X_u_mul_zero a b u (MvPolynomial.X u * p) hua hub

/-! ## Section I: stray-`X_u · X_v` annihilation, one-coordinate-outside form

For cross-term contributions where `(∂_u f_i)(∂_v f_j)` produces a
two-coordinate `X_w · X_v` factor (e.g.,
`(-c_i X_{3k+1})(-c_j X_{3k+2}) = c_i c_j X_{3k+1} X_{3k+2}`), it suffices
to observe that one of the two coordinates (in this example, `3k+2`)
lies outside the probe `{3k, 3k+1}`.  We package this as a clean lemma.
-/

/-- **Stray `X_w · X_v` annihilation, one-coordinate-outside**: if
`v ∉ {a, b}` (where `v` is one of the two factors), then the bilinear
coefficient of `X_w · X_v · p` at `X_a · X_b` is `0`. -/
theorem coeff_X_a_X_b_X_w_X_v_mul_zero_when_v_outside {N : ℕ}
    (a b w v : Fin N) (p : MvPolynomial (Fin N) ℚ)
    (hva : v ≠ a) (hvb : v ≠ b) :
    MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
        (MvPolynomial.X w * MvPolynomial.X v * p) = 0 := by
  -- X w * X v * p = X v * (X w * p)
  have heq :
      (MvPolynomial.X w * MvPolynomial.X v * p :
        MvPolynomial (Fin N) ℚ) =
      MvPolynomial.X v * (MvPolynomial.X w * p) := by
    ring
  rw [heq]
  exact coeff_X_a_X_b_X_u_mul_zero a b v (MvPolynomial.X w * p) hva hvb

/-- **Stray `X_w · X_v` with rational coefficient, one-outside**: if
`v ∉ {a, b}`, then the bilinear coefficient of `c · X_w · X_v · p` at
`X_a · X_b` is `0`. -/
theorem coeff_X_a_X_b_C_c_X_w_X_v_mul_zero_when_v_outside {N : ℕ}
    (a b w v : Fin N) (c : ℚ) (p : MvPolynomial (Fin N) ℚ)
    (hva : v ≠ a) (hvb : v ≠ b) :
    MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
        (MvPolynomial.C c * (MvPolynomial.X w * MvPolynomial.X v) * p) = 0 := by
  have heq :
      (MvPolynomial.C c * (MvPolynomial.X w * MvPolynomial.X v) * p :
        MvPolynomial (Fin N) ℚ) =
      MvPolynomial.X v * (MvPolynomial.X w * (MvPolynomial.C c * p)) := by
    ring
  rw [heq]
  exact coeff_X_a_X_b_X_u_mul_zero a b v
    (MvPolynomial.X w * (MvPolynomial.C c * p)) hva hvb

/-! ## Section J: identity-(3) specific cross-term vanishing

We instantiate the stray-`X` annihilation lemmas at the identity-(3)
indices `(u, v) = (uIdx, vIdx) = (3k+2, 3k+3)` and the probe indices
`(a, b) = (aIdx, bIdx) = (3k, 3k+1)`.

The three cross-term cases of the analytic decomposition (Section D)
all carry a stray `X_{3k+2}` (= `uIdx`) factor, which is **not** in
the probe `{3k, 3k+1}`:

* Case (a): `(2 X_{3k+2} - 1)(-c_j X_{3k+2})` — stray `X_{3k+2}`.
* Case (b): `(-X_{3k+1})(-c_j X_{3k+2})` — stray `X_{3k+2}`.
* Case (c): `(-c_i X_{3k+3})(-c_j X_{3k+2})` — stray `X_{3k+2}` (and
  also stray `X_{3k+3}`, but `X_{3k+2}` alone suffices).

In all three cases, `uIdx ∉ {aIdx, bIdx}` (Section B), so the
stray-`X_u` annihilation lemma applies.
-/

/-- **Identity (3) cross-term case (b) vanishing**: a generic cross-term
of the form `c · X_{bIdx} · X_{uIdx} · p` (corresponding to
`(-X_{3k+1})(-c_j X_{3k+2}) · rest = c_j X_{3k+1} X_{3k+2} · rest`)
vanishes at the bilinear probe.

The key observation is that `uIdx = 3k+2` is one of the row-indices,
which is **outside** the probe `{aIdx, bIdx} = {3k, 3k+1}`. -/
theorem identityThree_crossTerm_caseB_zero
    (n k : Nat) (hk2 : 3 * k + 3 < n)
    (c : ℚ) (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (MvPolynomial.C c *
          (MvPolynomial.X (bIdx n k hk2) * MvPolynomial.X (uIdx n k hk2)) *
          p) = 0 := by
  rw [probeLeft_eq]
  have hua : uIdx n k hk2 ≠ aIdx n k hk2 :=
    fun h => aIdx_ne_uIdx n k hk2 h.symm
  have hub : uIdx n k hk2 ≠ bIdx n k hk2 :=
    fun h => bIdx_ne_uIdx n k hk2 h.symm
  exact coeff_X_a_X_b_C_c_X_w_X_v_mul_zero_when_v_outside
    (aIdx n k hk2) (bIdx n k hk2) (bIdx n k hk2) (uIdx n k hk2) c p hua hub

/-- **Identity (3) cross-term case (c) vanishing**: a generic cross-term
of the form `c · X_{vIdx} · X_{uIdx} · p` (corresponding to
`(-c_i X_{3k+3})(-c_j X_{3k+2}) · rest = c_i c_j X_{3k+3} X_{3k+2} · rest`)
vanishes at the bilinear probe. -/
theorem identityThree_crossTerm_caseC_zero
    (n k : Nat) (hk2 : 3 * k + 3 < n)
    (c : ℚ) (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (MvPolynomial.C c *
          (MvPolynomial.X (vIdx n k hk2) * MvPolynomial.X (uIdx n k hk2)) *
          p) = 0 := by
  rw [probeLeft_eq]
  -- Use uIdx ∉ {aIdx, bIdx}
  have hua : uIdx n k hk2 ≠ aIdx n k hk2 :=
    fun h => aIdx_ne_uIdx n k hk2 h.symm
  have hub : uIdx n k hk2 ≠ bIdx n k hk2 :=
    fun h => bIdx_ne_uIdx n k hk2 h.symm
  exact coeff_X_a_X_b_C_c_X_w_X_v_mul_zero_when_v_outside
    (aIdx n k hk2) (bIdx n k hk2) (vIdx n k hk2) (uIdx n k hk2) c p hua hub

/-- **Identity (3) cross-term case (a) vanishing**: a generic cross-term
of the form `(-1 + 2 X_{uIdx}) · (-c · X_{uIdx}) · p` (corresponding to
`(2 X_{3k+2} - 1)(-c_j X_{3k+2}) · rest`) vanishes at the bilinear probe. -/
theorem identityThree_crossTerm_caseA_zero
    (n k : Nat) (hk2 : 3 * k + 3 < n)
    (c : ℚ) (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2)
        ((-1 + 2 * MvPolynomial.X (uIdx n k hk2)) *
          (-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk2))) * p) = 0 := by
  -- Algebraic expansion: (-1 + 2 X_u)(-c X_u) = c X_u - 2 c X_u^2.
  -- Both terms carry an X_u factor; both vanish.
  have heq :
      ((-1 + 2 * MvPolynomial.X (uIdx n k hk2)) *
          (-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk2))) * p :
        MvPolynomial (Fin n) ℚ) =
      MvPolynomial.X (uIdx n k hk2) * (MvPolynomial.C c * p) +
      MvPolynomial.X (uIdx n k hk2) *
        (MvPolynomial.X (uIdx n k hk2) * (-(2 * MvPolynomial.C c * p))) := by
    ring
  rw [heq]
  rw [probeLeft_eq, MvPolynomial.coeff_add]
  have hua : uIdx n k hk2 ≠ aIdx n k hk2 :=
    fun h => aIdx_ne_uIdx n k hk2 h.symm
  have hub : uIdx n k hk2 ≠ bIdx n k hk2 :=
    fun h => bIdx_ne_uIdx n k hk2 h.symm
  rw [coeff_X_a_X_b_X_u_mul_zero (aIdx n k hk2) (bIdx n k hk2) (uIdx n k hk2)
      (MvPolynomial.C c * p) hua hub]
  -- Second summand: X u * (X u * q) = (X u * X u) * q ; reduce to X_u_sq.
  have heq2 :
      (MvPolynomial.X (uIdx n k hk2) *
        (MvPolynomial.X (uIdx n k hk2) * (-(2 * MvPolynomial.C c * p))) :
        MvPolynomial (Fin n) ℚ) =
      MvPolynomial.X (uIdx n k hk2) * MvPolynomial.X (uIdx n k hk2) *
        (-(2 * MvPolynomial.C c * p)) := by
    ring
  rw [heq2]
  rw [coeff_X_a_X_b_X_u_sq_mul_zero (aIdx n k hk2) (bIdx n k hk2)
      (uIdx n k hk2) (-(2 * MvPolynomial.C c * p)) hua hub]
  ring

/-! ## Axiom audit anchors -/

#print axioms coeff_X_a_X_b_X_u_mul_zero
#print axioms coeff_X_a_X_b_p_X_u_q_zero
#print axioms coeff_X_a_X_b_C_c_X_u_mul_zero
#print axioms coeff_X_a_X_b_X_u_sq_mul_zero
#print axioms coeff_X_a_X_b_X_w_X_v_mul_zero_when_v_outside
#print axioms coeff_X_a_X_b_C_c_X_w_X_v_mul_zero_when_v_outside
#print axioms identityThree_crossTerm_caseA_zero
#print axioms identityThree_crossTerm_caseB_zero
#print axioms identityThree_crossTerm_caseC_zero

/-! ## Axiom audit anchors -/

#print axioms aIdx_ne_bIdx
#print axioms four_indices_pairwise_distinct
#print axioms probeLeft_eq
#print axioms identityThree_perPairSum_restated_iff
#print axioms identityThree_analytic_skeleton_iff_perPairSum
#print axioms rowRight_probeLeft_disjoint
#print axioms touchedList_boolFactors_length
#print axioms touchedList_adjFactors_length
#print axioms touchedList_transSkelFactorsForState_length
#print axioms touchedList_transSkelFactorsFlat_length
#print axioms touchedList_explicit_length

end BridgeAKappaTwoIdentityThreeAux

end PallLean.Paper93.Paper283
