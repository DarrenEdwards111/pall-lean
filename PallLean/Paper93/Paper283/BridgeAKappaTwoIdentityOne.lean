import PallLean.Paper93.Paper283.BridgeAKappaTwoTouchedListExplicit
import PallLean.Paper93.Paper283.BridgeAKappaTwoTwoFoldLeibnizExpansion
import PallLean.Paper93.Paper283.BridgeAKappaTwoPerPairCoefficients
import PallLean.Paper93.Paper283.BridgeAKappaTwoFactorPairLemmas
import PallLean.Paper93.Paper283.BridgeAKappaTwoFourCoefficientIdentities
import PallLean.Paper93.Paper283.MultilinearCoefficientInfrastructure
import PallLean.IterDerivHelpers

/-!
# Identity (1) for the κ=2 Bridge A four monomial-coefficient identities

This file states identity (1) of the typed package
`CookLevinLocalBlockQFourIdentitiesPackage`:
```
coeff(probeRight, mlProj(iterDerivList rowRight Q_b)) = 2K
```
with `rowRight = [3k+2, 3k+3]`, `probeRight = X_{3k+1}·X_{3k+2}`, and
`K = (1 + S)·S` for `S = Σ_q transCoeff M q`.

## Strategy

We reduce identity (1) through the existing infrastructure
(`BridgeAKappaTwoTouchedListExplicit`,
`BridgeAKappaTwoTwoFoldLeibnizExpansion`,
`BridgeAKappaTwoPerPairCoefficients`,
`BridgeAKappaTwoFactorPairLemmas`,
`MultilinearCoefficientInfrastructure`) to a single concrete residual
hypothesis: the value of the per-pair sum across the touched list.

Concretely, identity (1) follows from:

1. `iterDerivList [a, b] Q = pderiv b (pderiv a Q)` — chain unfold via
   `iterDerivList_cons` and `iterDerivList_nil`.
2. `coeff probe (mlProj p) = coeff probe p` for multilinear `probe` —
   `coeff_two_mono_mlProj_eq` from `MultilinearCoefficientInfrastructure`.
3. `Q_b = (touched_list).map(fun c => 1 - c.poly).prod` — definition of
   `cookLevinLocalBlockQ`.
4. `cookLevinConstraintsTouchingBlock T b = kappaTwoTouchedList_explicit M n k _ _`
   for an interior block — `cookLevinConstraintsTouchingBlock_at_interior_block`.
5. `pderiv b (pderiv a (list.prod)) = pderivListProdSumTwice a b list` —
   `pderiv_pderiv_list_prod`.

Steps 1–5 are all available kernel-only.  The remaining content is the
**per-pair coefficient sum** across the literal touched-list, which
according to the per-pair coefficient infrastructure equals
`2 * crossBlockKValue (Σ_q transCoeff M q) = 2 * (1 + S) * S` by the
analytic computation (file docstring of
`BridgeAKappaTwoFourIdentitiesProven`).

We expose the per-pair sum equality as the residual hypothesis
`identityOne_perPairSum`.  The theorem `kappaTwoIdentityOne` then closes
identity (1) directly under this hypothesis.

This file is the exact analogue of `BridgeAKappaTwoFourIdentitiesProven`
specialised to identity (1).  It does *not* close identity (1)
unconditionally — the per-pair sum closure remains the single
residual obstruction documented in
`kappaTwoFourIdentities_perPairSum_obstruction`.

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

attribute [local instance] Classical.dec

namespace BridgeAKappaTwoIdentityOne

/-! ## Section A: probe and row data for identity (1) -/

/-- The right-cross row `[3k+2, 3k+3]` as a `List (Fin n)`.  This is the
literal list used by the package field `h00`. -/
noncomputable def rowRight (n k : Nat) (hk2 : 3 * k + 3 < n) :
    List (Fin n) :=
  [(⟨3 * k + 2, by omega⟩ : Fin n),
   (⟨3 * k + 3, hk2⟩ : Fin n)]

/-- The right cross-block probe `X_{3k+1} · X_{3k+2}` as a finsupp. -/
noncomputable def probeRight (n k : Nat) (hk2 : 3 * k + 3 < n) :
    Fin n →₀ Nat :=
  Finsupp.single ⟨3 * k + 1, by omega⟩ 1 +
    Finsupp.single ⟨3 * k + 2, by omega⟩ 1

/-! ## Section B: structural reduction lemma for the LHS

We pull the LHS of identity (1) through the available infrastructure
into the form
`coeff probeRight (pderivListProdSumTwice u v (touchedFactors))`. -/

/-- Reduction step (1): the iterated derivative `iterDerivList [a, b]` is
two consecutive `pderiv` applications. -/
theorem iterDerivList_rowRight
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (Q : MvPolynomial (Fin n) ℚ) :
    iterDerivList (rowRight n k hk2) Q =
      pderiv (⟨3 * k + 3, hk2⟩ : Fin n)
        (pderiv (⟨3 * k + 2, by omega⟩ : Fin n) Q) := by
  unfold rowRight
  rw [iterDerivList_cons]
  rw [iterDerivList_single]

/-- Reduction step (2): coefficient at `probeRight` passes through `mlProj`. -/
theorem coeff_probeRight_mlProj
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeRight n k hk2) (mlProj p) =
      MvPolynomial.coeff (probeRight n k hk2) p := by
  unfold probeRight
  apply coeff_two_mono_mlProj_eq
  -- 3k+1 ≠ 3k+2: both as Fin n with values 3k+1, 3k+2.
  intro h
  have := congr_arg Fin.val h
  simp at this

/-- Reduction step (3+5): unfolding `cookLevinLocalBlockQ` to its literal
touched-list product, plus the two-fold Leibniz expansion of the
double `pderiv`. -/
theorem pderiv_pderiv_cookLevinLocalBlockQ_at_rowRight
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    pderiv (⟨3 * k + 3, hk2⟩ : Fin n)
      (pderiv (⟨3 * k + 2, by omega⟩ : Fin n)
        (cookLevinLocalBlockQ M n hn htb hns
          ⟨k, by rw [cook_levin_numBlocks]; omega⟩)) =
      pderivListProdSumTwice
        (⟨3 * k + 2, by omega⟩ : Fin n)
        (⟨3 * k + 3, hk2⟩ : Fin n)
        ((kappaTwoTouchedList_explicit M n k hk1 hk2).map
          (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly)) :=
  pderiv_pderiv_cookLevinLocalBlockQ_at_interior_block
    M n hn htb hns k hk1 hk2 _ _

/-- The LHS of identity (1), reduced to a coefficient at the recursive
two-fold Leibniz expansion over the literal touched-list. -/
theorem identityOne_LHS_reduction
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (probeRight n k hk2)
        (mlProj (iterDerivList (rowRight n k hk2)
          (cookLevinLocalBlockQ M n hn htb hns
            ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
      MvPolynomial.coeff (probeRight n k hk2)
        (pderivListProdSumTwice
          (⟨3 * k + 2, by omega⟩ : Fin n)
          (⟨3 * k + 3, hk2⟩ : Fin n)
          ((kappaTwoTouchedList_explicit M n k hk1 hk2).map
            (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly))) := by
  rw [iterDerivList_rowRight]
  rw [coeff_probeRight_mlProj]
  rw [pderiv_pderiv_cookLevinLocalBlockQ_at_rowRight
        M n hn htb hns k hk1 hk2]

/-! ## Section C: the residual per-pair-sum hypothesis

The remaining content of identity (1) is the closed-form value of the
coefficient at `probeRight` of the recursive two-fold Leibniz
expansion `pderivListProdSumTwice u v (touchedFactors)`.  By the
analytic computation (file docstring of
`BridgeAKappaTwoFourIdentitiesProven`), this equals
`2 * (1 + S) * S = 2 * crossBlockKValue S` where
`S = Σ_q transCoeff M q`.

We expose this as a typed hypothesis in the theorem statement of
`kappaTwoIdentityOne`.  The hypothesis exactly captures the residual
list-induction-with-summation work that
`kappaTwoFourIdentities_perPairSum_obstruction_holds` documents in
`BridgeAKappaTwoPerPairCoefficients`. -/

/-- The closed-form rational invariant `S = Σ_q transCoeff M q`. -/
noncomputable def transCoeffSum (M : TuringMachine.DTM) : ℚ :=
  ∑ q : Fin M.numStates, transCoeff M q

/-- Identity (1)'s per-pair sum hypothesis: the coefficient at
`probeRight` of `pderivListProdSumTwice` over the literal touched-list
equals `2 · K = 2 · (1 + S) · S`. -/
def identityOne_perPairSum
    (M : TuringMachine.DTM) (n : Nat) (_hn : n ≥ 2)
    (_htb : M.timeBound ≤ 4) (_hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) : Prop :=
  MvPolynomial.coeff (probeRight n k hk2)
      (pderivListProdSumTwice
        (⟨3 * k + 2, by omega⟩ : Fin n)
        (⟨3 * k + 3, hk2⟩ : Fin n)
        ((kappaTwoTouchedList_explicit M n k hk1 hk2).map
          (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly))) =
    2 * crossBlockKValue (transCoeffSum M)

/-! ## Section D: identity (1) under the residual hypothesis -/

/-- **Identity (1) for the κ = 2 four-identity package**.

Given the residual per-pair-sum hypothesis (the value of the
coefficient at `probeRight` of `pderivListProdSumTwice`), we obtain
the package field `h00`:
```
coeff(probeRight, mlProj(iterDerivList rowRight Q_b)) = 2 K.
```

This is the exact statement form of the
`CookLevinLocalBlockQFourIdentitiesPackage.h00` field, with
`probe 0 = probeRight n k hk2` and `K = crossBlockKValue (transCoeffSum M)`. -/
theorem kappaTwoIdentityOne
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (hpps : identityOne_perPairSum M n hn htb hns k hk1 hk2) :
    MvPolynomial.coeff (probeRight n k hk2)
        (mlProj (iterDerivList (rowRight n k hk2)
          (cookLevinLocalBlockQ M n hn htb hns
            ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
      2 * crossBlockKValue (transCoeffSum M) := by
  rw [identityOne_LHS_reduction M n hn htb hns k hk1 hk2]
  exact hpps

/-! ## Section E: bridging to the package's `h00` form

The package field `h00` is stated with the literal list
`[⟨3*k+2,_⟩, ⟨3*k+3, hk2⟩]` and the literal monomial
`probe 0 = single (3k+1) 1 + single (3k+2) 1`.  Both forms agree
definitionally with our `rowRight n k hk2` and `probeRight n k hk2`. -/

/-- Identity (1) in the exact `h00` shape of
`CookLevinLocalBlockQFourIdentitiesPackage`. -/
theorem kappaTwoIdentityOne_in_package_form
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (hpps : identityOne_perPairSum M n hn htb hns k hk1 hk2) :
    MvPolynomial.coeff (probeRight n k hk2)
        (mlProj (iterDerivList
          [(⟨3 * k + 2, by omega⟩ : Fin n),
           (⟨3 * k + 3, hk2⟩ : Fin n)]
          (cookLevinLocalBlockQ M n hn htb hns
            ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
      2 * crossBlockKValue (transCoeffSum M) :=
  kappaTwoIdentityOne M n hn htb hns k hk1 hk2 hpps

/-! ## Section F: status report on identity (1)

What this file delivers (kernel-only, no `sorry`, no new axioms):

* Step (A): `iterDerivList [a, b] = pderiv b ∘ pderiv a` — closed.
* Step (B): `coeff probe (mlProj p) = coeff probe p` for multilinear
  `probe` — closed via `coeff_two_mono_mlProj_eq`.
* Step (C): `pderiv b (pderiv a Q_b) = pderivListProdSumTwice` over the
  literal touched-list — closed via
  `pderiv_pderiv_cookLevinLocalBlockQ_at_interior_block`.
* Step (D): `kappaTwoIdentityOne` — the LHS of identity (1) reduced
  to a single residual hypothesis `identityOne_perPairSum` recording
  the closed-form value of the per-pair-sum coefficient.

What remains (residual sub-obstruction):

* `identityOne_perPairSum` itself — the per-pair-sum closure across
  the literal touched-list.  By the analytic computation in
  `BridgeAKappaTwoFourIdentitiesProven`, this equals
  `2 · (1 + S) · S = 2 · crossBlockKValue S` where
  `S = Σ_q transCoeff M q`.  A kernel-only proof would proceed by
  list-induction across `kappaTwoTouchedList_explicit`, applying
  `coeff_two_mono_list_prod_cons` and the per-pair coefficient lemmas
  of `BridgeAKappaTwoPerPairCoefficients` and
  `BridgeAKappaTwoFactorPairLemmas`. -/

/-! ## Axiom audit anchors -/

#print axioms iterDerivList_rowRight
#print axioms coeff_probeRight_mlProj
#print axioms pderiv_pderiv_cookLevinLocalBlockQ_at_rowRight
#print axioms identityOne_LHS_reduction
#print axioms kappaTwoIdentityOne
#print axioms kappaTwoIdentityOne_in_package_form

end BridgeAKappaTwoIdentityOne

end PallLean.Paper93.Paper283
