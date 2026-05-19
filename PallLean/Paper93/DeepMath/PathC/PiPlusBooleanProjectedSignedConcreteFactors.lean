import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedSignedCoordinateAtoms

/-!
# Concrete Cook--Levin factors as signed Pi+ coordinate atoms

The signed SAT-coordinate atom package is now unconditional for distinct Pi+
blocks.  This file connects the concrete Cook--Levin adjacency and transition
skeleton factors to that package: each exposed factor `1 - c * Xᵢ Xⱼ` is exactly
`satSignedCrossAtom`, with `c = 1` for adjacency and `c = transCoeff M q` for
transition skeleton constraints.
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

/-- The concrete adjacency factor is the signed SAT-coordinate atom with
coefficient `1`. -/
theorem adjacencyFactor_eq_satSignedCrossAtom
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i : Fin n) (hi : i.val + 1 < n) :
    (1 : MvPolynomial (Fin n) ℚ) - (adjLC n i hi).poly =
      satSignedCrossAtom M n hn2 htb hns 1 i ⟨i.val + 1, hi⟩ := by
  unfold satSignedCrossAtom adjLC adjPoly
  simp

/-- The concrete transition-skeleton factor is the signed SAT-coordinate atom
with coefficient `transCoeff M q`. -/
theorem transitionFactor_eq_satSignedCrossAtom
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (q : Fin M.numStates) (i : Fin n) (hi : i.val + 1 < n) :
    (1 : MvPolynomial (Fin n) ℚ) -
        (transSkelLC M n q i hi).poly =
      satSignedCrossAtom M n hn2 htb hns (transCoeff M q) i ⟨i.val + 1, hi⟩ := by
  unfold satSignedCrossAtom transSkelLC transSkelPoly
  simp [smul_eq_C_mul]
  rfl

/-- The concrete adjacency factor has the unconditional signed-atom row
certificate whenever the consecutive endpoints are in distinct Pi+ blocks. -/
theorem adjacencyFactor_signedCrossAtomRowCertificate_unconditional
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : Fin n) (hi : i.val + 1 < n)
    (hab : (D.coord i).1 ≠ (D.coord ⟨i.val + 1, hi⟩).1) :
    PiPlusBooleanProjectedSignedCrossAtomRowCertificate
      M n hn2 htb hns D 1 i ⟨i.val + 1, hi⟩ :=
  piPlusBooleanProjectedSignedCrossAtomRowCertificate_unconditional
    M n hn2 htb hns D 1 i ⟨i.val + 1, hi⟩ hab

/-- The concrete transition-skeleton factor has the unconditional signed-atom row
certificate whenever the consecutive endpoints are in distinct Pi+ blocks. -/
theorem transitionFactor_signedCrossAtomRowCertificate_unconditional
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (q : Fin M.numStates) (i : Fin n) (hi : i.val + 1 < n)
    (hab : (D.coord i).1 ≠ (D.coord ⟨i.val + 1, hi⟩).1) :
    PiPlusBooleanProjectedSignedCrossAtomRowCertificate
      M n hn2 htb hns D (transCoeff M q) i ⟨i.val + 1, hi⟩ :=
  piPlusBooleanProjectedSignedCrossAtomRowCertificate_unconditional
    M n hn2 htb hns D (transCoeff M q) i ⟨i.val + 1, hi⟩ hab

/-- Any concrete rest constraint in cadjacent form is a signed SAT-coordinate
atom factor. -/
theorem restConstraintFactor_eq_satSignedCrossAtom_of_cadj
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (lc : LocalConstraint n) (c : ℚ) (i : Fin n) (hi : i.val + 1 < n)
    (hpoly : lc.poly = MvPolynomial.C c *
      (MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩)) :
    (1 : MvPolynomial (Fin n) ℚ) - lc.poly =
      satSignedCrossAtom M n hn2 htb hns c i ⟨i.val + 1, hi⟩ := by
  unfold satSignedCrossAtom
  rw [hpoly, smul_eq_C_mul]
  rfl

/-- Every rest-list constraint exposes a signed SAT-coordinate atom factor.
The block-distinctness condition is left as the exact local hypothesis needed by
`Pi+` row transport. -/
theorem restConstraint_signedCrossAtomRowCertificate_of_mem
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (lc : LocalConstraint n)
    (hlc : lc ∈ adjConstraintList n ++ transSkelConstraintList M n) :
    ∃ (c : ℚ) (i : Fin n) (hi : i.val + 1 < n),
      (1 : MvPolynomial (Fin n) ℚ) - lc.poly =
        satSignedCrossAtom M n hn2 htb hns c i ⟨i.val + 1, hi⟩ ∧
      ((D.coord i).1 ≠ (D.coord ⟨i.val + 1, hi⟩).1 →
        PiPlusBooleanProjectedSignedCrossAtomRowCertificate
          M n hn2 htb hns D c i ⟨i.val + 1, hi⟩) := by
  rcases rest_constraint_cadj_form M n lc hlc with ⟨c, i, hi, hpoly⟩
  refine ⟨c, i, hi, ?_, ?_⟩
  · exact restConstraintFactor_eq_satSignedCrossAtom_of_cadj
      M n hn2 htb hns lc c i hi hpoly
  · intro hab
    exact piPlusBooleanProjectedSignedCrossAtomRowCertificate_unconditional
      M n hn2 htb hns D c i ⟨i.val + 1, hi⟩ hab

/-- Paper-scale rest-list constraint packaging into signed SAT-coordinate atoms. -/
theorem paperScale_restConstraint_signedCrossAtomRowCertificate_of_mem
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (lc : LocalConstraint (2 ^ 804))
    (hlc : lc ∈ adjConstraintList (2 ^ 804) ++
      transSkelConstraintList M (2 ^ 804)) :
    ∃ (c : ℚ) (i : Fin (2 ^ 804)) (hi : i.val + 1 < 2 ^ 804),
      (1 : MvPolynomial (Fin (2 ^ 804)) ℚ) - lc.poly =
        satSignedCrossAtom M (2 ^ 804) paperScale_ge_two htb hns
          c i ⟨i.val + 1, hi⟩ ∧
      (((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord i).1 ≠
        ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord
          ⟨i.val + 1, hi⟩).1 →
        PiPlusBooleanProjectedSignedCrossAtomRowCertificate
          M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
          c i ⟨i.val + 1, hi⟩) :=
  restConstraint_signedCrossAtomRowCertificate_of_mem
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) lc hlc

/-- Paper-scale concrete adjacency factor row certificate. -/
theorem paperScale_adjacencyFactor_signedCrossAtomRowCertificate_unconditional
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (i : Fin (2 ^ 804)) (hi : i.val + 1 < 2 ^ 804)
    (hab : ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord i).1 ≠
      ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord
        ⟨i.val + 1, hi⟩).1) :
    PiPlusBooleanProjectedSignedCrossAtomRowCertificate
      M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
      1 i ⟨i.val + 1, hi⟩ :=
  adjacencyFactor_signedCrossAtomRowCertificate_unconditional
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) i hi hab

/-- Paper-scale concrete transition-skeleton factor row certificate. -/
theorem paperScale_transitionFactor_signedCrossAtomRowCertificate_unconditional
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (q : Fin M.numStates) (i : Fin (2 ^ 804)) (hi : i.val + 1 < 2 ^ 804)
    (hab : ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord i).1 ≠
      ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord
        ⟨i.val + 1, hi⟩).1) :
    PiPlusBooleanProjectedSignedCrossAtomRowCertificate
      M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
      (transCoeff M q) i ⟨i.val + 1, hi⟩ :=
  transitionFactor_signedCrossAtomRowCertificate_unconditional
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) q i hi hab

/-! ## Axiom audit anchors -/

#print axioms adjacencyFactor_eq_satSignedCrossAtom
#print axioms transitionFactor_eq_satSignedCrossAtom
#print axioms adjacencyFactor_signedCrossAtomRowCertificate_unconditional
#print axioms transitionFactor_signedCrossAtomRowCertificate_unconditional
#print axioms restConstraintFactor_eq_satSignedCrossAtom_of_cadj
#print axioms restConstraint_signedCrossAtomRowCertificate_of_mem
#print axioms paperScale_restConstraint_signedCrossAtomRowCertificate_of_mem
#print axioms paperScale_adjacencyFactor_signedCrossAtomRowCertificate_unconditional
#print axioms paperScale_transitionFactor_signedCrossAtomRowCertificate_unconditional

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
