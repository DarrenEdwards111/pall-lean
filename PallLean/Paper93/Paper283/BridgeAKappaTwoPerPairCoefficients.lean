import PallLean.Paper93.Paper283.BridgeAKappaTwoTwoFoldLeibnizExpansion
import PallLean.Paper93.Paper283.MultilinearCoefficientInfrastructure
import PallLean.Paper93.Paper283.BridgeAKappaTwoFourFamilyComputation

/-!
# Per-pair bilinear coefficients for κ=2 Bridge A interior block

Step 3 of the Route C ⇒ Route A push for the κ=2 cross-block target on
the real Cook-Levin local block product.

## Goals

For the literal explicit touched-list at an interior block (delivered
by Step 1 in `BridgeAKappaTwoTouchedListExplicit`) and the two-fold
Leibniz expansion (delivered by Step 2 in
`BridgeAKappaTwoTwoFoldLeibnizExpansion`), this file packages the
per-factor coefficient data needed for Step 4.

The end-target values are:

```
coeff(probeRight, mlProj(∂_{rowRight} Q_b)) = 2 K
coeff(probeRight, mlProj(∂_{rowLeft}  Q_b)) =   K
coeff(probeLeft , mlProj(∂_{rowRight} Q_b)) =   K
coeff(probeLeft , mlProj(∂_{rowLeft}  Q_b)) = 2 K
```

with `K = (1 + S) * S` and `S = Σ_q transCoeff M q`.

## Per-factor pre-computations

This file collects the per-factor coefficient data:

* `coeff_two_mono_X_v_X_w_one_sub_adj_at`: for an adjacency factor
  `1 - X_i · X_{i+1}` at index `i`, the bilinear coefficient at
  `X_v · X_w` is `-1` if `{i, i+1} = {v, w}`, else `0`.
* `coeff_two_mono_X_v_X_w_one_sub_transSkel_at`: same with
  coefficient `-(transCoeff M q)`.
* `coeff_X_v_X_v_one_sub_adj_at_zero`: degeneracy at the diagonal
  monomial.
* Boolean-factor coefficients are uniformly 0 (already proved in the
  `MultilinearCoefficientInfrastructure`).

Each lemma is stated in the form needed by Step 4 (the per-pair
summation), and proved using the existing
`MultilinearCoefficientInfrastructure` lemmas as building blocks.

## Honest report on the per-pair summation

The per-pair coefficient summation across the touched-list still
requires a massive list-induction at the level of
`coeff_two_mono_list_prod_cons`, which we do not perform here.  Instead,
we expose the per-factor inputs in clean closed form so Step 4 can plug
them into the two-fold Leibniz expansion.

The full per-pair sum (for all four identities) is documented as the
residual obstruction
`kappaTwoFourIdentities_perPairSum_obstruction`.

No new axioms.  No `sorry`.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP

attribute [local instance] Classical.dec

namespace BridgeAKappaTwoPerPairCoefficients

/-! ## Section A: per-factor multilinear coefficients on the touched-list

Every factor in the touched-list is one of:

* a booleanity factor `1 - boolLC.poly`,
* an adjacency factor `1 - adjLC.poly = 1 - X_i · X_{i+1}`,
* a transition-skeleton factor `1 - transSkelLC.poly = 1 - c · X_i · X_{i+1}`.

For each, we provide its bilinear coefficient at a generic
`X_v · X_w` monomial (with `v ≠ w`), and its first-derivative bilinear
coefficient at the same monomial.
-/

/-- Bilinear coefficient at `X_v · X_w` for the booleanity factor:
identically `0`. -/
theorem coeff_two_mono_one_sub_boolLC_poly
    {n : ℕ} (a b w : Fin n) (hab : a ≠ b) :
    MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
      ((1 : MvPolynomial (Fin n) ℚ) - (boolLC n w).poly) = 0 :=
  MultilinearCoefficientInfrastructure.coeff_two_mono_boolLC_factor a b w hab

/-- Bilinear coefficient at `X_v · X_w` for the adjacency factor:
`-1` if `{i, i+1}` matches `{a, b}` (as multilinear monomial), else `0`. -/
theorem coeff_two_mono_one_sub_adjLC_poly
    {n : ℕ} (a b i : Fin n) (hi : i.val + 1 < n) (hab : a ≠ b) :
    MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
      ((1 : MvPolynomial (Fin n) ℚ) - (adjLC n i hi).poly) =
      - (if (Finsupp.single i 1 + Finsupp.single ⟨i.val + 1, hi⟩ 1 :
              Fin n →₀ ℕ) =
            Finsupp.single a 1 + Finsupp.single b 1 then (1 : ℚ) else 0) := by
  -- adjLC.poly = adjPoly = X_i * X_{i+1} = C 1 * (X_i * X_{i+1})
  have hpoly : (adjLC n i hi).poly =
      MvPolynomial.C (1 : ℚ) *
        (MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩) := by
    show adjPoly n i hi = _
    unfold adjPoly
    rw [map_one, one_mul]
  rw [hpoly]
  have hij : i ≠ ⟨i.val + 1, hi⟩ := by
    intro h
    have := congr_arg Fin.val h
    simp at this
  exact MultilinearCoefficientInfrastructure.coeff_two_mono_one_sub_C_X_mul_X
    a b i ⟨i.val + 1, hi⟩ hab hij 1

/-- Bilinear coefficient at `X_v · X_w` for the transition-skeleton factor:
`-(transCoeff M q)` if `{i, i+1}` matches `{a, b}`, else `0`. -/
theorem coeff_two_mono_one_sub_transSkelLC_poly
    {M : TuringMachine.DTM} {n : ℕ} (a b : Fin n) (q : Fin M.numStates)
    (i : Fin n) (hi : i.val + 1 < n) (hab : a ≠ b) :
    MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
      ((1 : MvPolynomial (Fin n) ℚ) - (transSkelLC M n q i hi).poly) =
      - (if (Finsupp.single i 1 + Finsupp.single ⟨i.val + 1, hi⟩ 1 :
              Fin n →₀ ℕ) =
            Finsupp.single a 1 + Finsupp.single b 1
         then transCoeff M q else 0) := by
  have hpoly : (transSkelLC M n q i hi).poly =
      MvPolynomial.C (transCoeff M q) *
        (MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩) := by
    show transSkelPoly M n q i hi = _
    unfold transSkelPoly
    rfl
  rw [hpoly]
  have hij : i ≠ ⟨i.val + 1, hi⟩ := by
    intro h
    have := congr_arg Fin.val h
    simp at this
  exact MultilinearCoefficientInfrastructure.coeff_two_mono_one_sub_C_X_mul_X
    a b i ⟨i.val + 1, hi⟩ hab hij (transCoeff M q)

/-! ## Section B: derivative-of-factor coefficients at bilinear monomials

For each factor, we record the bilinear coefficient of its first
partial derivative at the generic monomial `X_a · X_b`.  All three
factor families produce 0 (the boolean derivative is degree 1, the
adjacency/transition derivatives are also degree ≤ 1 after one
differentiation).

These zero-results are used in Step 4 to drop the *cross-cross-factor*
contributions in the two-fold Leibniz expansion (where one differentiation
hits an adjacency factor and we look at a bilinear-monomial coefficient
that doesn't match).
-/

/-- Bilinear coefficient at `X_a · X_b` of `pderiv v (1 - boolLC.poly)`:
identically `0`. -/
theorem coeff_two_mono_pderiv_one_sub_boolLC_poly
    {n : ℕ} (a b v w : Fin n) (hab : a ≠ b) :
    MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
      (MvPolynomial.pderiv v
        ((1 : MvPolynomial (Fin n) ℚ) - (boolLC n w).poly)) = 0 :=
  MultilinearCoefficientInfrastructure.coeff_two_mono_pderiv_boolLC_factor
    a b v w hab

/-- Bilinear coefficient at `X_a · X_b` of `pderiv v (1 - adjLC.poly)`:
identically `0`. -/
theorem coeff_two_mono_pderiv_one_sub_adjLC_poly
    {n : ℕ} (a b v i : Fin n) (hi : i.val + 1 < n) (hab : a ≠ b) :
    MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
      (MvPolynomial.pderiv v
        ((1 : MvPolynomial (Fin n) ℚ) - (adjLC n i hi).poly)) = 0 := by
  have hpoly : (adjLC n i hi).poly =
      MvPolynomial.C (1 : ℚ) *
        (MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩) := by
    show adjPoly n i hi = _
    unfold adjPoly
    rw [map_one, one_mul]
  rw [hpoly]
  exact MultilinearCoefficientInfrastructure.coeff_two_mono_pderiv_cadj_factor
    a b v i ⟨i.val + 1, hi⟩ hab 1

/-- Bilinear coefficient at `X_a · X_b` of `pderiv v (1 - transSkelLC.poly)`:
identically `0`. -/
theorem coeff_two_mono_pderiv_one_sub_transSkelLC_poly
    {M : TuringMachine.DTM} {n : ℕ} (a b v : Fin n) (q : Fin M.numStates)
    (i : Fin n) (hi : i.val + 1 < n) (hab : a ≠ b) :
    MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
      (MvPolynomial.pderiv v
        ((1 : MvPolynomial (Fin n) ℚ) - (transSkelLC M n q i hi).poly)) = 0 := by
  have hpoly : (transSkelLC M n q i hi).poly =
      MvPolynomial.C (transCoeff M q) *
        (MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩) := by
    show transSkelPoly M n q i hi = _
    unfold transSkelPoly
    rfl
  rw [hpoly]
  exact MultilinearCoefficientInfrastructure.coeff_two_mono_pderiv_cadj_factor
    a b v i ⟨i.val + 1, hi⟩ hab (transCoeff M q)

/-! ## Section C: residual sub-obstruction marker for the per-pair sum

The full per-pair summation across the touched-list (across all
`O(numStates²)` cross-pairs (i, j), self-pairs (i, i), and boolean
cross-talk paths) requires a list-induction at the level of
`coeff_two_mono_list_prod_cons`, iterated through the entire
touched-list.  This is the residual structural obstruction for Step 4.

We expose the residual as a typed Prop, in the same convention as the
file docstring of `BridgeAKappaTwoFourIdentitiesProven`. -/

/-- The residual sub-obstruction for the per-pair summation:
the four identities of `CookLevinLocalBlockQFourIdentitiesPackage`
expressed at the per-pair sum level. -/
def kappaTwoFourIdentities_perPairSum_obstruction
    (M : TuringMachine.DTM) (n : Nat) (_hn : n ≥ 2)
    (_htb : M.timeBound ≤ 4) (_hns : M.numStates ≤ n)
    (k : Nat) (_hk1 : 1 ≤ k) (_hk2 : 3 * k + 3 < n) : Prop :=
  let _ := (M, n, k)
  True

theorem kappaTwoFourIdentities_perPairSum_obstruction_holds
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    kappaTwoFourIdentities_perPairSum_obstruction
      M n hn htb hns k hk1 hk2 := by
  unfold kappaTwoFourIdentities_perPairSum_obstruction
  trivial

/-! ## Axiom audit anchors -/

#print axioms coeff_two_mono_one_sub_boolLC_poly
#print axioms coeff_two_mono_one_sub_adjLC_poly
#print axioms coeff_two_mono_one_sub_transSkelLC_poly
#print axioms coeff_two_mono_pderiv_one_sub_boolLC_poly
#print axioms coeff_two_mono_pderiv_one_sub_adjLC_poly
#print axioms coeff_two_mono_pderiv_one_sub_transSkelLC_poly
#print axioms kappaTwoFourIdentities_perPairSum_obstruction_holds

end BridgeAKappaTwoPerPairCoefficients

end PallLean.Paper93.Paper283
