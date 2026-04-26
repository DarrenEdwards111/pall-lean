import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityOne
import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityFour

/-!
# Identity (2) for the κ=2 Bridge A four monomial-coefficient identities

```
identity (2): coeff(probeRight, mlProj(iterDerivList rowLeft Q_b)) = K.
```

This is the off-diagonal `(probe = right, row = left)` cross-block
configuration: probe at `X_{3k+1} · X_{3k+2}` paired with row
`[3k-1, 3k]`.

Same structural reduction as identities (1) and (4); the residual
per-pair-sum value is `crossBlockKValue (Σ_q transCoeff M q)` rather
than `2 ·` that quantity.

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

namespace BridgeAKappaTwoIdentityTwo

/-! ## Section A: identity (2) LHS reduction -/

/-- The LHS of identity (2), reduced to the recursive two-fold Leibniz
form. -/
theorem identityTwo_LHS_reduction
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (probeRight n k hk2)
        (mlProj (iterDerivList (rowLeft n k hk1 hk2)
          (cookLevinLocalBlockQ M n hn htb hns
            ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
      MvPolynomial.coeff (probeRight n k hk2)
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
  rw [coeff_probeRight_mlProj]
  rw [pderiv_pderiv_cookLevinLocalBlockQ_at_rowLeft
        M n hn htb hns k hk1 hk2]

/-! ## Section B: residual per-pair-sum hypothesis -/

/-- Identity (2)'s per-pair sum hypothesis: the coefficient at
`probeRight` of `pderivListProdSumTwice` over the `rowLeft` differentials
of the literal touched-list equals `K`. -/
def identityTwo_perPairSum
    (M : TuringMachine.DTM) (n : Nat) (_hn : n ≥ 2)
    (_htb : M.timeBound ≤ 4) (_hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) : Prop :=
  MvPolynomial.coeff (probeRight n k hk2)
      (pderivListProdSumTwice
        (⟨3 * (k - 1) + 2, by
          have heq : 3 * (k - 1) + 3 = 3 * k := by
            rw [show (3 : Nat) = 3 * 1 from rfl, ← Nat.mul_add]
            congr 1; omega
          omega⟩ : Fin n)
        (⟨3 * k + 0, by omega⟩ : Fin n)
        ((kappaTwoTouchedList_explicit M n k hk1 hk2).map
          (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly))) =
    crossBlockKValue (transCoeffSum M)

/-! ## Section C: identity (2) under the residual hypothesis -/

/-- **Identity (2) for the κ = 2 four-identity package** (in package form). -/
theorem kappaTwoIdentityTwo
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (hpps : identityTwo_perPairSum M n hn htb hns k hk1 hk2) :
    MvPolynomial.coeff (probeRight n k hk2)
        (mlProj (iterDerivList (rowLeft n k hk1 hk2)
          (cookLevinLocalBlockQ M n hn htb hns
            ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
      crossBlockKValue (transCoeffSum M) := by
  rw [identityTwo_LHS_reduction M n hn htb hns k hk1 hk2]
  exact hpps

/-- Identity (2) in the exact `h01` shape of
`CookLevinLocalBlockQFourIdentitiesPackage`. -/
theorem kappaTwoIdentityTwo_in_package_form
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (hpps : identityTwo_perPairSum M n hn htb hns k hk1 hk2) :
    MvPolynomial.coeff (probeRight n k hk2)
        (mlProj (iterDerivList
          [(⟨3 * (k - 1) + 2, by
              have heq : 3 * (k - 1) + 3 = 3 * k := by
                rw [show (3 : Nat) = 3 * 1 from rfl, ← Nat.mul_add]
                congr 1; omega
              omega⟩ : Fin n),
           (⟨3 * k + 0, by omega⟩ : Fin n)]
          (cookLevinLocalBlockQ M n hn htb hns
            ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
      crossBlockKValue (transCoeffSum M) :=
  kappaTwoIdentityTwo M n hn htb hns k hk1 hk2 hpps

/-! ## Axiom audit anchors -/

#print axioms identityTwo_LHS_reduction
#print axioms kappaTwoIdentityTwo
#print axioms kappaTwoIdentityTwo_in_package_form

end BridgeAKappaTwoIdentityTwo

end PallLean.Paper93.Paper283
