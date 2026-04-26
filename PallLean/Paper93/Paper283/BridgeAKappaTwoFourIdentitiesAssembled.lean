import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityOne
import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityTwo
import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityThree
import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityFour
import PallLean.Paper93.Paper283.BridgeAKappaTwoFourIdentitiesDischarged

/-!
# Assembly of the κ=2 four-identity package from the four per-pair sums

This is the final assembly file: given the four per-pair-sum
hypotheses (one per identity), we build a concrete
`CookLevinLocalBlockQFourIdentitiesPackage` and feed it into
`cookLevinLocalBlockQ_rank_two_le_real_via_pkg` to obtain the
unconditional `κ = 2` rank lower bound.

The four per-pair-sum hypotheses are:
* `identityOne_perPairSum`     →  identity (1) with value `2 K`,
* `identityTwo_perPairSum`     →  identity (2) with value `K`,
* `identityThree_perPairSum`   →  identity (3) with value `K`,
* `identityFour_perPairSum`    →  identity (4) with value `2 K`,

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

/-! ## Section B: package builder from the four per-pair-sum hypotheses -/

/-- Given the four per-pair-sum hypotheses and positivity of
`K = crossBlockKValue (transCoeffSum M)`, build a concrete
`CookLevinLocalBlockQFourIdentitiesPackage`. -/
noncomputable def kappaTwoFourIdentitiesPackage_from_perPairSums
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (hKpos : 0 < crossBlockKValue (transCoeffSum M))
    (hpps1 : identityOne_perPairSum M n hn htb hns k hk1 hk2)
    (hpps2 : identityTwo_perPairSum M n hn htb hns k hk1 hk2)
    (hpps3 : identityThree_perPairSum M n hn htb hns k hk1 hk2)
    (hpps4 : identityFour_perPairSum M n hn htb hns k hk1 hk2) :
    CookLevinLocalBlockQFourIdentitiesPackage M n hn htb hns k hk1 hk2 :=
  cookLevinLocalBlockQFourIdentitiesPackage_of_witnesses
    M n hn htb hns k hk1 hk2
    (crossBlockKValue (transCoeffSum M))
    hKpos
    (kappaTwoProbePair n k hk2)
    (by
      simp only [kappaTwoProbePair_zero]
      exact kappaTwoIdentityOne_in_package_form
        M n hn htb hns k hk1 hk2 hpps1)
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
        kappaTwoIdentityTwo_in_package_form
          M n hn htb hns k hk1 hk2 hpps2
      -- The package's h01 has shape `... = K`, ours says `... = K`.
      exact heq)
    (by
      simp only [kappaTwoProbePair_one]
      exact kappaTwoIdentityThree_in_package_form
        M n hn htb hns k hk1 hk2 hpps3)
    (by
      simp only [kappaTwoProbePair_one]
      exact kappaTwoIdentityFour_in_package_form
        M n hn htb hns k hk1 hk2 hpps4)

/-! ## Section C: end-to-end rank lower bound from the four per-pair-sums -/

/-- The κ = 2 cross-block rank lower bound on the real Cook-Levin
local block product, conditional on the four per-pair-sum hypotheses
and positivity of `K`. -/
theorem cookLevinLocalBlockQ_rank_two_le_real_from_perPairSums
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (hKpos : 0 < crossBlockKValue (transCoeffSum M))
    (hpps1 : identityOne_perPairSum M n hn htb hns k hk1 hk2)
    (hpps2 : identityTwo_perPairSum M n hn htb hns k hk1 hk2)
    (hpps3 : identityThree_perPairSum M n hn htb hns k hk1 hk2)
    (hpps4 : identityFour_perPairSum M n hn htb hns k hk1 hk2) :
    (2 : Nat) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        2 2
        (cookLevinLocalBlockQ M n hn htb hns
          ⟨k, by rw [cook_levin_numBlocks]; omega⟩) :=
  cookLevinLocalBlockQ_rank_two_le_real_via_pkg
    M n hn htb hns k hk1 hk2
    (kappaTwoFourIdentitiesPackage_from_perPairSums
      M n hn htb hns k hk1 hk2
      hKpos hpps1 hpps2 hpps3 hpps4)

/-! ## Section D: status report

What this file delivers (kernel-only, no `sorry`, no new axioms):

* `kappaTwoFourIdentitiesPackage_from_perPairSums`: a concrete
  `CookLevinLocalBlockQFourIdentitiesPackage` value from the four
  per-pair-sum hypotheses and `K > 0`.

* `cookLevinLocalBlockQ_rank_two_le_real_from_perPairSums`: the κ = 2
  rank lower bound conditional on those same hypotheses.

What remains (residual sub-obstruction):

* The four per-pair-sum hypotheses
  (`identityOne/Two/Three/Four_perPairSum`).  Each is the closed-form
  value of the coefficient at one of the two probes of
  `pderivListProdSumTwice` over the literal touched-list, against one
  of the two cross-block rows.  By the analytic computation
  (file docstring of `BridgeAKappaTwoFourIdentitiesProven`), the four
  values are `2K, K, K, 2K` respectively, with `K = (1+S)·S`.

* Positivity of `K = crossBlockKValue (transCoeffSum M)`.  This
  follows from `transCoeffSum M > 0`, which in turn follows from
  `numStates ≥ 1` and each `transCoeff M q ≥ 1`.

The residual obstructions are all of the form "compute a closed-form
coefficient by list induction"; they are concrete, finite-effort tasks
each requiring the per-pair-sum infrastructure of
`BridgeAKappaTwoPerPairCoefficients` plus a list-induction across
`kappaTwoTouchedList_explicit`. -/

/-! ## Axiom audit anchors -/

#print axioms kappaTwoProbePair
#print axioms kappaTwoFourIdentitiesPackage_from_perPairSums
#print axioms cookLevinLocalBlockQ_rank_two_le_real_from_perPairSums

end PallLean.Paper93.Paper283
