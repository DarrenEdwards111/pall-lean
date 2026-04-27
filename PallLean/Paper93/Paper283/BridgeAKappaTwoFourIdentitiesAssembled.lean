import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityOne
import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityOneResidualActive
import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityTwo
import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityTwoResidualActive
import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityThree
import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityThreeResidualActive
import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityFour
import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityFourResidualActive
import PallLean.Paper93.Paper283.BridgeAKappaTwoKPositive
import PallLean.Paper93.Paper283.BridgeAKappaTwoFourIdentitiesDischarged

/-!
# Assembly of the κ=2 four-identity package from closed per-pair sums

This is the final assembly file: using the closed identity (1), (2),
(3), and (4) theorems from the residual-active files, and the closed
positivity theorem for `K`, we build
a concrete `CookLevinLocalBlockQFourIdentitiesPackage` and feed it into
`cookLevinLocalBlockQ_rank_two_le_real_via_pkg`.

The per-pair-sum inputs/status are:
* `identityOne_perPairSum`     →  identity (1), closed downstream,
* `identityTwo_perPairSum`     →  identity (2), closed downstream,
* `identityThree_perPairSum`   →  identity (3), closed downstream,
* `identityFour_perPairSum`    →  identity (4), closed downstream,

with `K = crossBlockKValue (transCoeffSum M) = (1 + S) · S`,
`S = Σ_q transCoeff M q`.  Positivity of `K` reduces to positivity of
`S`, which holds for `numStates ≥ 1` (each `transCoeff M q ≥ 1`).

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
open BridgeAKappaTwoIdentityTwo
open BridgeAKappaTwoIdentityThree
open BridgeAKappaTwoIdentityFour

attribute [local instance] Classical.dec

/-! ## Section A: probe assembly -/

/-- The probe pair `Fin 2 → Fin n →₀ Nat` for the four-identity
package, with `probe 0 = X_{3k+1}·X_{3k+2}` and
`probe 1 = X_{3k}·X_{3k+1}`. -/
noncomputable def kappaTwoProbePair (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n) :
    Fin 2 → Fin n →₀ Nat :=
  fun r => match r with
  | ⟨0, _⟩ => probeRight n k hk2
  | ⟨1, _⟩ => probeLeft n k hk2

@[simp] theorem kappaTwoProbePair_zero (n k : Nat) (hk2 : 3 * k + 3 < n) :
    kappaTwoProbePair n k hk2 0 = probeRight n k hk2 := rfl

@[simp] theorem kappaTwoProbePair_one (n k : Nat) (hk2 : 3 * k + 3 < n) :
    kappaTwoProbePair n k hk2 1 = probeLeft n k hk2 := rfl

/-! ## Section B: package builder from the closed per-pair sums -/

/-- Given the closed per-pair sums, build a concrete
`CookLevinLocalBlockQFourIdentitiesPackage`. -/
noncomputable def kappaTwoFourIdentitiesPackage_from_perPairSums
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    CookLevinLocalBlockQFourIdentitiesPackage M n hn htb hns k hk1 hk2 :=
  cookLevinLocalBlockQFourIdentitiesPackage_of_witnesses
    M n hn htb hns k hk1 hk2
    (crossBlockKValue (transCoeffSum M))
    (crossBlockKValue_transCoeffSum_pos M)
    (kappaTwoProbePair n k hk2)
    (by
      simp only [kappaTwoProbePair_zero]
      exact BridgeAKappaTwoIdentityOne.kappaTwoIdentityOne_in_package_form
        M n hn htb hns k hk1 hk2
        (BridgeAKappaTwoIdentityOneResidualActive.identityOne_perPairSum
          M n hn htb hns k hk1 hk2))
    (by
      simp only [kappaTwoProbePair_zero]
      have heq :
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
        BridgeAKappaTwoIdentityTwo.kappaTwoIdentityTwo_in_package_form
          M n hn htb hns k hk1 hk2
          (BridgeAKappaTwoIdentityTwoResidualActive.identityTwo_perPairSum
            M n hn htb hns k hk1 hk2)
      -- The package's h01 has shape `... = K`, ours says `... = K`.
      exact heq)
    (by
      simp only [kappaTwoProbePair_one]
      exact BridgeAKappaTwoIdentityThree.kappaTwoIdentityThree_in_package_form
        M n hn htb hns k hk1 hk2
        (BridgeAKappaTwoIdentityThreeResidualActive.identityThree_perPairSum
          M n hn htb hns k hk1 hk2))
    (by
      simp only [kappaTwoProbePair_one]
      exact BridgeAKappaTwoIdentityFour.kappaTwoIdentityFour_in_package_form
        M n hn htb hns k hk1 hk2
        (BridgeAKappaTwoIdentityFourResidualActive.identityFour_perPairSum
          M n hn htb hns k hk1 hk2))

/-! ## Section C: end-to-end rank lower bound from the closed per-pair sums -/

/-- The κ = 2 cross-block rank lower bound on the real Cook-Levin
local block product. -/
theorem cookLevinLocalBlockQ_rank_two_le_real_from_perPairSums
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    (2 : Nat) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        2 2
        (cookLevinLocalBlockQ M n hn htb hns
          ⟨k, by rw [cook_levin_numBlocks]; omega⟩) :=
  cookLevinLocalBlockQ_rank_two_le_real_via_pkg
    M n hn htb hns k hk1 hk2
    (kappaTwoFourIdentitiesPackage_from_perPairSums
      M n hn htb hns k hk1 hk2)

/-! ## Section D: status report

What this file delivers (kernel-only, no `sorry`, no new axioms):

* `kappaTwoFourIdentitiesPackage_from_perPairSums`: a concrete
  `CookLevinLocalBlockQFourIdentitiesPackage` value from the closed
  identity (1), (2), (3), and (4) theorems and the closed `K > 0`
  theorem.

* `cookLevinLocalBlockQ_rank_two_le_real_from_perPairSums`: the κ = 2
  rank lower bound from the closed κ = 2 package. -/

/-! ## Axiom audit anchors -/

#print axioms kappaTwoProbePair
#print axioms kappaTwoFourIdentitiesPackage_from_perPairSums
#print axioms cookLevinLocalBlockQ_rank_two_le_real_from_perPairSums

end PallLean.Paper93.Paper283
