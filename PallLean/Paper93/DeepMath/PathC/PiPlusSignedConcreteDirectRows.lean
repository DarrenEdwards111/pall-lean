import PallLean.Paper93.DeepMath.PathC.PiPlusRequestedUnconditionalDischarges

/-!
# Direct signed-cross rows for concrete adjacency and transition factors

The direct coordinate-conjugation theorem for `satSignedCrossAtom` is now the
shared algebraic engine for concrete Cook--Levin adjacency and transition-left
skeleton factors.  This file exposes that routing explicitly: the concrete
factors are first rewritten to `satSignedCrossAtom`, then the row certificate is
obtained from `signedCrossAtomCoordinateConjugation_direct` plus the isolated
`mlProj`/rename compatibility.

The last section packages the honest case-split surface for atomic Cook--Levin
factor rows.  It deliberately stops at the atomic/factor level: multiplying
these rows into the full factored product is still the Leibniz/product assembly
socket, not something to assert for free.
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

/-- Flat concrete adjacency factor row certificate. -/
def PiPlusBooleanProjectedAdjacencyAtomRowCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : Fin n) (hi : i.val + 1 < n) : Prop :=
  (D.coord i).1 ≠ (D.coord ⟨i.val + 1, hi⟩).1 ∧
  (piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
      (zeroProfileBooleanNormalize
        (piPlusSATBlockAlgEquiv M n hn2 htb hns D
          (((1 : MvPolynomial (Fin n) ℚ) - (adjLC n i hi).poly) :
            SATDeciderGaugeSpace M n hn2 htb hns))) =
    mlProj
      ((1 : SATDeciderGaugeSpace M n hn2 htb hns) *
        SPDP.iterDerivList
          ([] : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
          ((((1 : MvPolynomial (Fin n) ℚ) - (adjLC n i hi).poly) :
            SATDeciderGaugeSpace M n hn2 htb hns)))

/-- Flat concrete transition-left/skeleton factor row certificate. -/
def PiPlusBooleanProjectedTransitionAtomRowCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (q : Fin M.numStates) (i : Fin n) (hi : i.val + 1 < n) : Prop :=
  (D.coord i).1 ≠ (D.coord ⟨i.val + 1, hi⟩).1 ∧
  (piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
      (zeroProfileBooleanNormalize
        (piPlusSATBlockAlgEquiv M n hn2 htb hns D
          ((((1 : MvPolynomial (Fin n) ℚ) -
            (transSkelLC M n q i hi).poly)) :
            SATDeciderGaugeSpace M n hn2 htb hns))) =
    mlProj
      ((1 : SATDeciderGaugeSpace M n hn2 htb hns) *
        SPDP.iterDerivList
          ([] : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
          ((((1 : MvPolynomial (Fin n) ℚ) -
            (transSkelLC M n q i hi).poly) :
            SATDeciderGaugeSpace M n hn2 htb hns)))

/-- The signed-cross row certificate can be obtained through the direct
coordinate-conjugation theorem. -/
theorem piPlusBooleanProjectedSignedCrossAtomRowCertificate_from_directConjugation
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M n hn2 htb hns).numVars)
    (hab : (D.coord a).1 ≠ (D.coord b).1) :
    PiPlusBooleanProjectedSignedCrossAtomRowCertificate
      M n hn2 htb hns D c a b :=
  piPlusBooleanProjectedSignedCrossAtomRowCertificate_of_coordinateConjugation
    M n hn2 htb hns D c a b hab
    (signedCrossAtomCoordinateConjugation_direct M n hn2 htb hns D c a b)
    (signedCrossAtomMlProjRenameCompatibility_unconditional
      M n hn2 htb hns D c a b hab)

/-- Concrete adjacency factor rows are direct signed-cross rows with coefficient
`1`. -/
theorem piPlusBooleanProjectedAdjacencyAtomRowCertificate_unconditional
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : Fin n) (hi : i.val + 1 < n)
    (hab : (D.coord i).1 ≠ (D.coord ⟨i.val + 1, hi⟩).1) :
    PiPlusBooleanProjectedAdjacencyAtomRowCertificate
      M n hn2 htb hns D i hi := by
  refine ⟨hab, ?_⟩
  have hsigned :=
    piPlusBooleanProjectedSignedCrossAtomRowCertificate_from_directConjugation
      M n hn2 htb hns D 1 i ⟨i.val + 1, hi⟩ hab
  rcases hsigned with ⟨_hdist, hrow⟩
  simpa [adjacencyFactor_eq_satSignedCrossAtom M n hn2 htb hns i hi]
    using hrow

/-- Concrete transition-left/skeleton factor rows are direct signed-cross rows
with coefficient `transCoeff M q`. -/
theorem piPlusBooleanProjectedTransitionAtomRowCertificate_unconditional
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (q : Fin M.numStates) (i : Fin n) (hi : i.val + 1 < n)
    (hab : (D.coord i).1 ≠ (D.coord ⟨i.val + 1, hi⟩).1) :
    PiPlusBooleanProjectedTransitionAtomRowCertificate
      M n hn2 htb hns D q i hi := by
  refine ⟨hab, ?_⟩
  have hsigned :=
    piPlusBooleanProjectedSignedCrossAtomRowCertificate_from_directConjugation
      M n hn2 htb hns D (transCoeff M q) i ⟨i.val + 1, hi⟩ hab
  rcases hsigned with ⟨_hdist, hrow⟩
  simpa [transitionFactor_eq_satSignedCrossAtom M n hn2 htb hns q i hi]
    using hrow

/-- Atomic Cook--Levin factors whose Boolean-projected row certificates have
been discharged.  Booleanity is represented by the mixed block atom; adjacency
and transition-left/skeleton factors are represented by signed cross atoms. -/
inductive CookLevinAtomicFactorRowCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) :
    MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ → Prop
  | booleanity
      (i : D.blockIndex)
      (hcert : PiPlusBooleanProjectedMixedAtomRowCertificate
        M n hn2 htb hns D i) :
      CookLevinAtomicFactorRowCertificate M n hn2 htb hns D
        ((X (satBlockFalse M n hn2 htb hns D i)) *
          (X (satBlockTrue M n hn2 htb hns D i)))
  | adjacency
      (i : Fin n) (hi : i.val + 1 < n)
      (hab : (D.coord i).1 ≠ (D.coord ⟨i.val + 1, hi⟩).1)
      (hcert : PiPlusBooleanProjectedAdjacencyAtomRowCertificate
        M n hn2 htb hns D i hi) :
      CookLevinAtomicFactorRowCertificate M n hn2 htb hns D
        ((1 : MvPolynomial (Fin n) ℚ) - (adjLC n i hi).poly)
  | transition
      (q : Fin M.numStates) (i : Fin n) (hi : i.val + 1 < n)
      (hab : (D.coord i).1 ≠ (D.coord ⟨i.val + 1, hi⟩).1)
      (hcert : PiPlusBooleanProjectedTransitionAtomRowCertificate
        M n hn2 htb hns D q i hi) :
      CookLevinAtomicFactorRowCertificate M n hn2 htb hns D
        ((1 : MvPolynomial (Fin n) ℚ) - (transSkelLC M n q i hi).poly)

/-- Booleanity atomic factors are discharged by the mixed Booleanity theorem. -/
theorem cookLevinAtomicBooleanityRowCertificate_unconditional
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : D.blockIndex) :
    CookLevinAtomicFactorRowCertificate M n hn2 htb hns D
      ((X (satBlockFalse M n hn2 htb hns D i)) *
        (X (satBlockTrue M n hn2 htb hns D i))) :=
  CookLevinAtomicFactorRowCertificate.booleanity i
    (piPlusBooleanProjectedMixedAtomRowCertificate_unconditional
      M n hn2 htb hns D i)

/-- Adjacency atomic factors are discharged by the direct signed-cross theorem. -/
theorem cookLevinAtomicAdjacencyRowCertificate_unconditional
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : Fin n) (hi : i.val + 1 < n)
    (hab : (D.coord i).1 ≠ (D.coord ⟨i.val + 1, hi⟩).1) :
    CookLevinAtomicFactorRowCertificate M n hn2 htb hns D
      ((1 : MvPolynomial (Fin n) ℚ) - (adjLC n i hi).poly) :=
  CookLevinAtomicFactorRowCertificate.adjacency i hi hab
    (piPlusBooleanProjectedAdjacencyAtomRowCertificate_unconditional
      M n hn2 htb hns D i hi hab)

/-- Transition-left/skeleton atomic factors are discharged by the direct
signed-cross theorem. -/
theorem cookLevinAtomicTransitionRowCertificate_unconditional
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (q : Fin M.numStates) (i : Fin n) (hi : i.val + 1 < n)
    (hab : (D.coord i).1 ≠ (D.coord ⟨i.val + 1, hi⟩).1) :
    CookLevinAtomicFactorRowCertificate M n hn2 htb hns D
      ((1 : MvPolynomial (Fin n) ℚ) - (transSkelLC M n q i hi).poly) :=
  CookLevinAtomicFactorRowCertificate.transition q i hi hab
    (piPlusBooleanProjectedTransitionAtomRowCertificate_unconditional
      M n hn2 htb hns D q i hi hab)

/-- Rest constraints in cadjacent form have a direct signed-cross row whenever
the exposed endpoints lie in distinct `Pi+` blocks. -/
theorem cookLevinRestAtomicSignedRowCertificate_of_mem
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
    exact piPlusBooleanProjectedSignedCrossAtomRowCertificate_from_directConjugation
      M n hn2 htb hns D c i ⟨i.val + 1, hi⟩ hab

/-! ## Axiom audit anchors -/

#print axioms piPlusBooleanProjectedSignedCrossAtomRowCertificate_from_directConjugation
#print axioms piPlusBooleanProjectedAdjacencyAtomRowCertificate_unconditional
#print axioms piPlusBooleanProjectedTransitionAtomRowCertificate_unconditional
#print axioms cookLevinAtomicBooleanityRowCertificate_unconditional
#print axioms cookLevinAtomicAdjacencyRowCertificate_unconditional
#print axioms cookLevinAtomicTransitionRowCertificate_unconditional
#print axioms cookLevinRestAtomicSignedRowCertificate_of_mem

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
