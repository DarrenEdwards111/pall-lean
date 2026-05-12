import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityOne
import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityFour

/-!
# Identity (3) for the κ=2 Bridge A four monomial-coefficient identities

```
identity (3): coeff(probeLeft, mlProj(iterDerivList rowRight Q_b)) = K.
```

This is the off-diagonal `(probe = left, row = right)` cross-block
configuration: probe at `X_{3k} · X_{3k+1}` paired with row
`[3k+2, 3k+3]`.

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

attribute [local instance] Classical.dec

namespace BridgeAKappaTwoIdentityThree

/-! ## Section A: identity (3) LHS reduction -/

/-- The LHS of identity (3), reduced to the recursive two-fold Leibniz
form. -/
theorem identityThree_LHS_reduction
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (mlProj (iterDerivList (rowRight n k hk2)
          (cookLevinLocalBlockQ M n hn htb hns
            ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
      MvPolynomial.coeff (probeLeft n k hk2)
        (pderivListProdSumTwice
          (⟨3 * k + 2, by omega⟩ : Fin n)
          (⟨3 * k + 3, hk2⟩ : Fin n)
          ((kappaTwoTouchedList_explicit M n k hk1 hk2).map
            (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly))) := by
  rw [iterDerivList_rowRight]
  rw [coeff_probeLeft_mlProj]
  rw [pderiv_pderiv_cookLevinLocalBlockQ_at_rowRight
        M n hn htb hns k hk1 hk2]

/-! ## Section B: residual per-pair-sum hypothesis -/

/-- Identity (3)'s per-pair sum hypothesis: the coefficient at
`probeLeft` of `pderivListProdSumTwice` over the `rowRight` differentials
of the literal touched-list equals `K`. -/
def identityThree_perPairSum
    (M : TuringMachine.DTM) (n : Nat) (_hn : n ≥ 2)
    (_htb : M.timeBound ≤ 4) (_hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) : Prop :=
  MvPolynomial.coeff (probeLeft n k hk2)
      (pderivListProdSumTwice
        (⟨3 * k + 2, by omega⟩ : Fin n)
        (⟨3 * k + 3, hk2⟩ : Fin n)
        ((kappaTwoTouchedList_explicit M n k hk1 hk2).map
          (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly))) =
    crossBlockKValue (transCoeffSum M)

/-! ## Section C: identity (3) under the residual hypothesis -/

/-- **Identity (3) for the κ = 2 four-identity package**. -/
theorem kappaTwoIdentityThree
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (hpps : identityThree_perPairSum M n hn htb hns k hk1 hk2) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (mlProj (iterDerivList (rowRight n k hk2)
          (cookLevinLocalBlockQ M n hn htb hns
            ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
      crossBlockKValue (transCoeffSum M) := by
  rw [identityThree_LHS_reduction M n hn htb hns k hk1 hk2]
  exact hpps

/-- Identity (3) in the exact `h10` shape of
`CookLevinLocalBlockQFourIdentitiesPackage`. -/
theorem kappaTwoIdentityThree_in_package_form
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (hpps : identityThree_perPairSum M n hn htb hns k hk1 hk2) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (mlProj (iterDerivList
          [(⟨3 * k + 2, by omega⟩ : Fin n),
           (⟨3 * k + 3, hk2⟩ : Fin n)]
          (cookLevinLocalBlockQ M n hn htb hns
            ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
      crossBlockKValue (transCoeffSum M) :=
  kappaTwoIdentityThree M n hn htb hns k hk1 hk2 hpps

/-! ## Axiom audit anchors -/

#print axioms identityThree_LHS_reduction
#print axioms kappaTwoIdentityThree
#print axioms kappaTwoIdentityThree_in_package_form

end BridgeAKappaTwoIdentityThree

end PallLean.Paper93.Paper283
