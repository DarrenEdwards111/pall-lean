import PallLean.Paper93.DeepMath.PathC.PiPlusRequestedUnconditionalDischarges

/-!
# Paper-scale block separation for adjacent Cook--Levin coordinates

The rest-list certificate reduces every adjacency/transition factor to a signed
cross atom under the hypothesis that the two endpoints live in distinct `Pi+`
blocks.  For the canonical paper-scale pairing, adjacent flat coordinates split
by parity: even-left adjacent pairs are inside one block, odd-left adjacent pairs
cross to the next block.  This file records the cross-block half as the next
usable unconditional bridge for rest constraints.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Paper283
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

namespace BoolPoly

/-- In the canonical paper-scale `Pi+` pairing, an adjacent pair whose left
endpoint is odd crosses from one block to the next. -/
theorem paperScale_coord_block_ne_succ_of_odd
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (i : Fin (2 ^ 804)) (hi : i.val + 1 < 2 ^ 804)
    (hodd : i.val % 2 = 1) :
    ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord i).1 ≠
      ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord
        ⟨i.val + 1, hi⟩).1 := by
  intro h
  simp [cookLevinPiPlusBlockCoordinateData_paperScale,
    cookLevinPiPlusBlockCoordinateDataOfPair, finPairBoolEquiv, finTwoEquiv] at h
  have hval := congrArg Fin.val h
  simp [finProdFinEquiv] at hval
  have hpow : 2 ^ 804 = 2 ^ 803 * 2 := by rw [pow_succ]
  have hbound : i.val / 2 < 2 ^ 803 := by
    apply Nat.div_lt_of_lt_mul
    omega
  have hbound_succ : (i.val + 1) / 2 < 2 ^ 803 := by
    apply Nat.div_lt_of_lt_mul
    omega
  have hval' : i.val / 2 = (i.val + 1) / 2 := by
    simpa [Nat.mod_eq_of_lt hbound, Nat.mod_eq_of_lt hbound_succ] using hval
  have hsucc_div : (i.val + 1) / 2 = i.val / 2 + 1 := by
    have hmod := Nat.mod_add_div i.val 2
    rw [hodd] at hmod
    omega
  omega

/-- Odd-left paper-scale rest constraints now have a fully discharged signed atom
row certificate, because the canonical pairing supplies the required endpoint
block separation. -/
theorem paperScale_oddRestConstraint_signedCrossAtomRowCertificate_unconditional
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (lc : LocalConstraint (2 ^ 804))
    (hlc : lc ∈ adjConstraintList (2 ^ 804) ++
      transSkelConstraintList M (2 ^ 804))
    (hoddWitness : ∀ (c : ℚ) (i : Fin (2 ^ 804)) (hi : i.val + 1 < 2 ^ 804),
      (1 : MvPolynomial (Fin (2 ^ 804)) ℚ) - lc.poly =
        satSignedCrossAtom M (2 ^ 804) paperScale_ge_two htb hns
          c i ⟨i.val + 1, hi⟩ → i.val % 2 = 1) :
    ∃ (c : ℚ) (i : Fin (2 ^ 804)) (hi : i.val + 1 < 2 ^ 804),
      (1 : MvPolynomial (Fin (2 ^ 804)) ℚ) - lc.poly =
        satSignedCrossAtom M (2 ^ 804) paperScale_ge_two htb hns
          c i ⟨i.val + 1, hi⟩ ∧
      PiPlusBooleanProjectedSignedCrossAtomRowCertificate
        M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
        c i ⟨i.val + 1, hi⟩ := by
  rcases paperScaleRequestedRestConstraintDischarge M htb hns lc hlc with
    ⟨c, i, hi, hfac, hcert⟩
  refine ⟨c, i, hi, hfac, ?_⟩
  exact hcert (paperScale_coord_block_ne_succ_of_odd M htb hns i hi
    (hoddWitness c i hi hfac))

/-! ## Axiom audit anchors -/

#print axioms paperScale_coord_block_ne_succ_of_odd
#print axioms paperScale_oddRestConstraint_signedCrossAtomRowCertificate_unconditional

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
