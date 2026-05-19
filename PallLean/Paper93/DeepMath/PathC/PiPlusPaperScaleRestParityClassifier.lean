import PallLean.Paper93.DeepMath.PathC.PiPlusPaperScaleBlockSeparation
import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedSameBlockCoordinateAtom

/-!
# Paper-scale rest-factor parity classifier

The canonical paper-scale `Pi+` coordinates pair adjacent flat variables by
parity.  Odd-left adjacent pairs are cross-block and use the signed cross-block
certificate.  Even-left adjacent pairs are the two Boolean sides of one block
and use the same-block `(1,1)` span certificate.
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

/-- In the canonical paper-scale pairing, an even-left adjacent pair has its left
endpoint on the false side of its `Pi+` block. -/
theorem paperScale_coord_side_false_of_even
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (i : Fin (2 ^ 804)) (heven : i.val % 2 = 0) :
    ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord i).2 = false := by
  simp [cookLevinPiPlusBlockCoordinateData_paperScale,
    cookLevinPiPlusBlockCoordinateDataOfPair, finPairBoolEquiv, finTwoEquiv,
    finProdFinEquiv]
  intro hmod
  have hval := congrArg Fin.val hmod
  simp [Fin.modNat, heven] at hval

/-- In the canonical paper-scale pairing, the successor of an even-left endpoint
is the true side of the same `Pi+` block. -/
theorem paperScale_coord_succ_side_true_of_even
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (i : Fin (2 ^ 804)) (hi : i.val + 1 < 2 ^ 804)
    (heven : i.val % 2 = 0) :
    ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord
      ⟨i.val + 1, hi⟩).2 = true := by
  have hsucc_mod : (i.val + 1) % 2 = 1 := by omega
  simp [cookLevinPiPlusBlockCoordinateData_paperScale,
    cookLevinPiPlusBlockCoordinateDataOfPair, finPairBoolEquiv, finTwoEquiv,
    finProdFinEquiv]
  apply Fin.ext
  simp [Fin.modNat, hsucc_mod]

/-- In the canonical paper-scale pairing, an even-left adjacent pair stays inside
one `Pi+` block. -/
theorem paperScale_coord_block_eq_succ_of_even
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (i : Fin (2 ^ 804)) (hi : i.val + 1 < 2 ^ 804)
    (heven : i.val % 2 = 0) :
    ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord i).1 =
      ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord
        ⟨i.val + 1, hi⟩).1 := by
  simp [cookLevinPiPlusBlockCoordinateData_paperScale,
    cookLevinPiPlusBlockCoordinateDataOfPair, finPairBoolEquiv, finTwoEquiv] 
  apply Fin.ext
  simp [finProdFinEquiv]
  have hsucc_div : (i.val + 1) / 2 = i.val / 2 := by
    have hmod := Nat.mod_add_div i.val 2
    rw [heven] at hmod
    omega
  rw [hsucc_div]

/-- Even-left adjacent endpoints are literally the false/true coordinates of the
same paper-scale `Pi+` block. -/
theorem paperScale_even_adjacent_eq_satBlockFalseTrue
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (i : Fin (2 ^ 804)) (hi : i.val + 1 < 2 ^ 804)
    (heven : i.val % 2 = 0) :
    let D := cookLevinPiPlusBlockCoordinateData_paperScale M htb hns
    i = satBlockFalse M (2 ^ 804) paperScale_ge_two htb hns D (D.coord i).1 ∧
    ⟨i.val + 1, hi⟩ =
      satBlockTrue M (2 ^ 804) paperScale_ge_two htb hns D (D.coord i).1 := by
  intro D
  constructor
  · apply D.coord.injective
    simp [satBlockFalse]
    apply Prod.ext
    · rfl
    · exact paperScale_coord_side_false_of_even M htb hns i heven
  · apply D.coord.injective
    simp [satBlockTrue]
    have hblock := paperScale_coord_block_eq_succ_of_even M htb hns i hi heven
    have hside := paperScale_coord_succ_side_true_of_even M htb hns i hi heven
    apply Prod.ext
    · exact hblock.symm
    · exact hside

/-- An even-left rest factor is the flat same-block signed atom for its canonical
`Pi+` block. -/
theorem paperScale_evenRestFactor_eq_satSignedSameBlockAtom
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (c : ℚ) (i : Fin (2 ^ 804)) (hi : i.val + 1 < 2 ^ 804)
    (heven : i.val % 2 = 0) :
    satSignedCrossAtom M (2 ^ 804) paperScale_ge_two htb hns
        c i ⟨i.val + 1, hi⟩ =
      satSignedSameBlockAtom M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
        c ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord i).1 := by
  rcases paperScale_even_adjacent_eq_satBlockFalseTrue M htb hns i hi heven with
    ⟨hfalse, htrue⟩
  unfold satSignedSameBlockAtom
  rw [← hfalse, ← htrue]

/-- Even-left paper-scale rest constraints now route to the flat same-block
`(1,1)` span certificate. -/
theorem paperScale_evenRestConstraint_signedSameBlockOneOneSpan_unconditional
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (lc : LocalConstraint (2 ^ 804))
    (hlc : lc ∈ adjConstraintList (2 ^ 804) ++
      transSkelConstraintList M (2 ^ 804))
    (hevenWitness : ∀ (c : ℚ) (i : Fin (2 ^ 804)) (hi : i.val + 1 < 2 ^ 804),
      (1 : MvPolynomial (Fin (2 ^ 804)) ℚ) - lc.poly =
        satSignedCrossAtom M (2 ^ 804) paperScale_ge_two htb hns
          c i ⟨i.val + 1, hi⟩ → i.val % 2 = 0) :
    ∃ (c : ℚ) (i : Fin (2 ^ 804)) (_hi : i.val + 1 < 2 ^ 804),
      (1 : MvPolynomial (Fin (2 ^ 804)) ℚ) - lc.poly =
        satSignedSameBlockAtom M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
          c ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord i).1 ∧
      PiPlusBooleanProjectedSignedSameBlockAtomOneOneSpanCertificate
        M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
        c ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord i).1 := by
  rcases paperScaleRequestedRestConstraintDischarge M htb hns lc hlc with
    ⟨c, i, hi, hfac, _hcert⟩
  refine ⟨c, i, hi, ?_, ?_⟩
  · rw [hfac]
    exact paperScale_evenRestFactor_eq_satSignedSameBlockAtom M htb hns c i hi
      (hevenWitness c i hi hfac)
  · exact piPlusBooleanProjectedSignedSameBlockAtomOneOneSpanCertificate_unconditional
      M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
      c ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord i).1

/-- Parity classifier for a paper-scale rest constraint, expressed at the factor
level.  The odd branch is the old cross-block `(1,0)` certificate; the even
branch is the same-block `(1,1)` span certificate. -/
theorem paperScale_restConstraint_parityClassifier
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (lc : LocalConstraint (2 ^ 804))
    (hlc : lc ∈ adjConstraintList (2 ^ 804) ++
      transSkelConstraintList M (2 ^ 804)) :
    (∃ (c : ℚ) (i : Fin (2 ^ 804)) (hi : i.val + 1 < 2 ^ 804),
      (1 : MvPolynomial (Fin (2 ^ 804)) ℚ) - lc.poly =
        satSignedCrossAtom M (2 ^ 804) paperScale_ge_two htb hns
          c i ⟨i.val + 1, hi⟩ ∧ i.val % 2 = 1 ∧
      PiPlusBooleanProjectedSignedCrossAtomRowCertificate
        M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
        c i ⟨i.val + 1, hi⟩) ∨
    (∃ (c : ℚ) (i : Fin (2 ^ 804)) (_hi : i.val + 1 < 2 ^ 804),
      (1 : MvPolynomial (Fin (2 ^ 804)) ℚ) - lc.poly =
        satSignedSameBlockAtom M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
          c ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord i).1 ∧
      i.val % 2 = 0 ∧
      PiPlusBooleanProjectedSignedSameBlockAtomOneOneSpanCertificate
        M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
        c ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord i).1) := by
  rcases paperScaleRequestedRestConstraintDischarge M htb hns lc hlc with
    ⟨c, i, hi, hfac, hcross⟩
  have hpar : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
  rcases hpar with heven | hodd
  · right
    refine ⟨c, i, hi, ?_, heven, ?_⟩
    · rw [hfac]
      exact paperScale_evenRestFactor_eq_satSignedSameBlockAtom M htb hns c i hi heven
    · exact piPlusBooleanProjectedSignedSameBlockAtomOneOneSpanCertificate_unconditional
        M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
        c ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord i).1
  · left
    refine ⟨c, i, hi, hfac, hodd, ?_⟩
    exact hcross (paperScale_coord_block_ne_succ_of_odd M htb hns i hi hodd)

/-! ## Axiom audit anchors -/

#print axioms paperScale_coord_side_false_of_even
#print axioms paperScale_coord_succ_side_true_of_even
#print axioms paperScale_coord_block_eq_succ_of_even
#print axioms paperScale_even_adjacent_eq_satBlockFalseTrue
#print axioms paperScale_evenRestFactor_eq_satSignedSameBlockAtom
#print axioms paperScale_evenRestConstraint_signedSameBlockOneOneSpan_unconditional
#print axioms paperScale_restConstraint_parityClassifier

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
