import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityOne

/-!
# Identity (4) for the κ=2 Bridge A four monomial-coefficient identities

This file is the symmetric counterpart of
`BridgeAKappaTwoIdentityOne.lean`.  Where identity (1) treats
`(probeRight, rowRight) → 2K`, identity (4) treats
`(probeLeft, rowLeft) → 2K` — the symmetric configuration with both
the probe and the row swapped to the left-boundary.

```
rowLeft  = [3k-1, 3k]
probeLeft = X_{3k} · X_{3k+1}
identity (4): coeff(probeLeft, mlProj(iterDerivList rowLeft Q_b)) = 2K.
```

The proof structure mirrors identity (1) exactly: pull through
`iterDerivList`, `mlProj`, the literal touched-list expansion, and the
two-fold Leibniz expansion, then close on a residual per-pair-sum
hypothesis whose value is `2 · crossBlockKValue (Σ_q transCoeff M q)`.

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

attribute [local instance] Classical.dec

namespace BridgeAKappaTwoIdentityFour

/-! ## Section A: probe and row data for identity (4) -/

/-- The left-cross row `[3k-1, 3k]` as a `List (Fin n)`.  This is the
literal list used by the package field `h11`. -/
noncomputable def rowLeft (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    List (Fin n) :=
  [(⟨3 * (k - 1) + 2, by
      have heq : 3 * (k - 1) + 3 = 3 * k := by
        rw [show (3 : Nat) = 3 * 1 from rfl, ← Nat.mul_add]
        congr 1; omega
      omega⟩ : Fin n),
   (⟨3 * k + 0, by omega⟩ : Fin n)]

/-- The left cross-block probe `X_{3k} · X_{3k+1}` as a finsupp. -/
noncomputable def probeLeft (n k : Nat) (hk2 : 3 * k + 3 < n) :
    Fin n →₀ Nat :=
  Finsupp.single ⟨3 * k, by omega⟩ 1 +
    Finsupp.single ⟨3 * k + 1, by omega⟩ 1

/-! ## Section B: structural reduction lemmas -/

/-- Reduction step (1): the iterated derivative `iterDerivList rowLeft`
is two consecutive `pderiv` applications. -/
theorem iterDerivList_rowLeft
    (n : Nat) (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (Q : MvPolynomial (Fin n) ℚ) :
    iterDerivList (rowLeft n k hk1 hk2) Q =
      pderiv (⟨3 * k + 0, by omega⟩ : Fin n)
        (pderiv (⟨3 * (k - 1) + 2, by
          have heq : 3 * (k - 1) + 3 = 3 * k := by
            rw [show (3 : Nat) = 3 * 1 from rfl, ← Nat.mul_add]
            congr 1; omega
          omega⟩ : Fin n) Q) := by
  unfold rowLeft
  rw [iterDerivList_cons]
  rw [iterDerivList_single]

/-- Reduction step (2): coefficient at `probeLeft` passes through `mlProj`. -/
theorem coeff_probeLeft_mlProj
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2) (mlProj p) =
      MvPolynomial.coeff (probeLeft n k hk2) p := by
  unfold probeLeft
  apply coeff_two_mono_mlProj_eq
  -- 3k ≠ 3k+1
  intro h
  have := congr_arg Fin.val h
  simp at this

/-- Reduction step (3+5): unfolding `cookLevinLocalBlockQ` and the
two-fold Leibniz expansion at `rowLeft`. -/
theorem pderiv_pderiv_cookLevinLocalBlockQ_at_rowLeft
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    pderiv (⟨3 * k + 0, by omega⟩ : Fin n)
      (pderiv (⟨3 * (k - 1) + 2, by
          have heq : 3 * (k - 1) + 3 = 3 * k := by
            rw [show (3 : Nat) = 3 * 1 from rfl, ← Nat.mul_add]
            congr 1; omega
          omega⟩ : Fin n)
        (cookLevinLocalBlockQ M n hn htb hns
          ⟨k, by rw [cook_levin_numBlocks]; omega⟩)) =
      pderivListProdSumTwice
        (⟨3 * (k - 1) + 2, by
          have heq : 3 * (k - 1) + 3 = 3 * k := by
            rw [show (3 : Nat) = 3 * 1 from rfl, ← Nat.mul_add]
            congr 1; omega
          omega⟩ : Fin n)
        (⟨3 * k + 0, by omega⟩ : Fin n)
        ((kappaTwoTouchedList_explicit M n k hk1 hk2).map
          (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly)) :=
  pderiv_pderiv_cookLevinLocalBlockQ_at_interior_block
    M n hn htb hns k hk1 hk2 _ _

/-- The LHS of identity (4), reduced to the recursive two-fold Leibniz
form. -/
theorem identityFour_LHS_reduction
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (mlProj (iterDerivList (rowLeft n k hk1 hk2)
          (cookLevinLocalBlockQ M n hn htb hns
            ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
      MvPolynomial.coeff (probeLeft n k hk2)
        (pderivListProdSumTwice
          (⟨3 * (k - 1) + 2, by
            have heq : 3 * (k - 1) + 3 = 3 * k := by
              rw [show (3 : Nat) = 3 * 1 from rfl, ← Nat.mul_add]
              congr 1; omega
            omega⟩ : Fin n)
          (⟨3 * k + 0, by omega⟩ : Fin n)
          ((kappaTwoTouchedList_explicit M n k hk1 hk2).map
            (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly))) := by
  rw [iterDerivList_rowLeft]
  rw [coeff_probeLeft_mlProj]
  rw [pderiv_pderiv_cookLevinLocalBlockQ_at_rowLeft
        M n hn htb hns k hk1 hk2]

/-! ## Section C: residual per-pair-sum hypothesis -/

/-- Identity (4)'s per-pair sum hypothesis: the coefficient at
`probeLeft` of `pderivListProdSumTwice` over the literal touched-list
equals `2 · K`. -/
def identityFour_perPairSum
    (M : TuringMachine.DTM) (n : Nat) (_hn : n ≥ 2)
    (_htb : M.timeBound ≤ 4) (_hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) : Prop :=
  MvPolynomial.coeff (probeLeft n k hk2)
      (pderivListProdSumTwice
        (⟨3 * (k - 1) + 2, by
          have heq : 3 * (k - 1) + 3 = 3 * k := by
            rw [show (3 : Nat) = 3 * 1 from rfl, ← Nat.mul_add]
            congr 1; omega
          omega⟩ : Fin n)
        (⟨3 * k + 0, by omega⟩ : Fin n)
        ((kappaTwoTouchedList_explicit M n k hk1 hk2).map
          (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly))) =
    2 * crossBlockKValue (transCoeffSum M)

/-! ## Section D: identity (4) under the residual hypothesis -/

/-- **Identity (4) for the κ = 2 four-identity package**.

Given the residual per-pair-sum hypothesis, we obtain the package
field `h11`:
```
coeff(probeLeft, mlProj(iterDerivList rowLeft Q_b)) = 2 K.
```
-/
theorem kappaTwoIdentityFour
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (hpps : identityFour_perPairSum M n hn htb hns k hk1 hk2) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (mlProj (iterDerivList (rowLeft n k hk1 hk2)
          (cookLevinLocalBlockQ M n hn htb hns
            ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
      2 * crossBlockKValue (transCoeffSum M) := by
  rw [identityFour_LHS_reduction M n hn htb hns k hk1 hk2]
  exact hpps

/-- Identity (4) in the exact `h11` shape of
`CookLevinLocalBlockQFourIdentitiesPackage`. -/
theorem kappaTwoIdentityFour_in_package_form
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (hpps : identityFour_perPairSum M n hn htb hns k hk1 hk2) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (mlProj (iterDerivList
          [(⟨3 * (k - 1) + 2, by
              have heq : 3 * (k - 1) + 3 = 3 * k := by
                rw [show (3 : Nat) = 3 * 1 from rfl, ← Nat.mul_add]
                congr 1; omega
              omega⟩ : Fin n),
           (⟨3 * k + 0, by omega⟩ : Fin n)]
          (cookLevinLocalBlockQ M n hn htb hns
            ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
      2 * crossBlockKValue (transCoeffSum M) :=
  kappaTwoIdentityFour M n hn htb hns k hk1 hk2 hpps

/-! ## Axiom audit anchors -/

#print axioms iterDerivList_rowLeft
#print axioms coeff_probeLeft_mlProj
#print axioms pderiv_pderiv_cookLevinLocalBlockQ_at_rowLeft
#print axioms identityFour_LHS_reduction
#print axioms kappaTwoIdentityFour
#print axioms kappaTwoIdentityFour_in_package_form

end BridgeAKappaTwoIdentityFour

end PallLean.Paper93.Paper283
