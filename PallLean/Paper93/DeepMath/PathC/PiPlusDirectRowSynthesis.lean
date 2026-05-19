import PallLean.Paper93.DeepMath.PathC.PiPlusSignedConcreteDirectRows
import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanityAlignmentObstruction

/-!
# Direct row synthesis from the two closed local algebraic discharges

This file does not introduce a new payload shape.  It records the requested
actual derivations:

* adjacency rows are obtained from `signedCrossAtomCoordinateConjugation_direct`,
  because `1 - X_a X_b` is `satSignedCrossAtom` with coefficient `1`;
* transition-left/skeleton rows are obtained from the same direct signed-cross
  theorem with coefficient `transCoeff M q`;
* the attempted Booleanity leg of a top-level factored-row certificate is blocked
  by a concrete polynomial identity, not by a missing abstraction: the actual
  Cook--Levin Booleanity factor `1 - X_v(1-X_v)` is not the mixed block atom
  certified by the 52ae1750 discharge.
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

/-- Requested derivation (1): concrete adjacency rows are direct signed-cross
rows, using `signedCrossAtomCoordinateConjugation_direct` through
`piPlusBooleanProjectedSignedCrossAtomRowCertificate_from_directConjugation` and
`adjacencyFactor_eq_satSignedCrossAtom`. -/
theorem adjacencyRowCertificate_from_signedCrossAtomCoordinateConjugation_direct
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : Fin n) (hi : i.val + 1 < n)
    (hab : (D.coord i).1 ≠ (D.coord ⟨i.val + 1, hi⟩).1) :
    PiPlusBooleanProjectedAdjacencyAtomRowCertificate
      M n hn2 htb hns D i hi := by
  refine ⟨hab, ?_⟩
  have hsigned :
      PiPlusBooleanProjectedSignedCrossAtomRowCertificate
        M n hn2 htb hns D 1 i ⟨i.val + 1, hi⟩ :=
    piPlusBooleanProjectedSignedCrossAtomRowCertificate_from_directConjugation
      M n hn2 htb hns D 1 i ⟨i.val + 1, hi⟩ hab
  rcases hsigned with ⟨_hdist, hrow⟩
  simpa [adjacencyFactor_eq_satSignedCrossAtom M n hn2 htb hns i hi]
    using hrow

/-- Requested derivation (2): concrete transition-left/skeleton rows are direct
signed-cross rows with coefficient `transCoeff M q`. -/
theorem transitionRowCertificate_from_signedCrossAtomCoordinateConjugation_direct
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (q : Fin M.numStates) (i : Fin n) (hi : i.val + 1 < n)
    (hab : (D.coord i).1 ≠ (D.coord ⟨i.val + 1, hi⟩).1) :
    PiPlusBooleanProjectedTransitionAtomRowCertificate
      M n hn2 htb hns D q i hi := by
  refine ⟨hab, ?_⟩
  have hsigned :
      PiPlusBooleanProjectedSignedCrossAtomRowCertificate
        M n hn2 htb hns D (transCoeff M q) i ⟨i.val + 1, hi⟩ :=
    piPlusBooleanProjectedSignedCrossAtomRowCertificate_from_directConjugation
      M n hn2 htb hns D (transCoeff M q) i ⟨i.val + 1, hi⟩ hab
  rcases hsigned with ⟨_hdist, hrow⟩
  simpa [transitionFactor_eq_satSignedCrossAtom M n hn2 htb hns q i hi]
    using hrow

/-- The existing public adjacency theorem is exactly the requested direct
signed-cross derivation. -/
theorem piPlusBooleanProjectedAdjacencyAtomRowCertificate_unconditional_direct
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : Fin n) (hi : i.val + 1 < n)
    (hab : (D.coord i).1 ≠ (D.coord ⟨i.val + 1, hi⟩).1) :
    PiPlusBooleanProjectedAdjacencyAtomRowCertificate
      M n hn2 htb hns D i hi :=
  adjacencyRowCertificate_from_signedCrossAtomCoordinateConjugation_direct
    M n hn2 htb hns D i hi hab

/-- The existing public transition theorem is exactly the requested direct
signed-cross derivation. -/
theorem piPlusBooleanProjectedTransitionAtomRowCertificate_unconditional_direct
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (q : Fin M.numStates) (i : Fin n) (hi : i.val + 1 < n)
    (hab : (D.coord i).1 ≠ (D.coord ⟨i.val + 1, hi⟩).1) :
    PiPlusBooleanProjectedTransitionAtomRowCertificate
      M n hn2 htb hns D q i hi :=
  transitionRowCertificate_from_signedCrossAtomCoordinateConjugation_direct
    M n hn2 htb hns D q i hi hab

/-- Exact obstruction to requested derivation (3), Booleanity case.

The case split on `cookLevinConstraintType i` cannot produce a top-level
Cook--Levin factored row certificate from only the mixed Booleanity atom and the
signed-cross atom unless the Booleanity branch identifies the actual Booleanity
factor with the mixed block atom.  That required identity is false:

`1 - (boolLC n v).poly ≠ X_false * X_true`.

This is the concrete polynomial obstruction; adjacency and transition do close
from signed-cross as shown above. -/
theorem cookLevinFactoredRowCertificate_unconditional_booleanity_identity_obstruction
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin n) (i : D.blockIndex) :
    ((1 : MvPolynomial (Fin n) ℚ) - (boolLC n v).poly :
        SATDeciderGaugeSpace M n hn2 htb hns) ≠
      ((X (satBlockFalse M n hn2 htb hns D i)) *
        (X (satBlockTrue M n hn2 htb hns D i)) :
        SATDeciderGaugeSpace M n hn2 htb hns) :=
  boolLC_factor_ne_mixed_monomial M n hn2 htb hns D v i

/-! ## Axiom audit anchors -/

#print axioms adjacencyRowCertificate_from_signedCrossAtomCoordinateConjugation_direct
#print axioms transitionRowCertificate_from_signedCrossAtomCoordinateConjugation_direct
#print axioms piPlusBooleanProjectedAdjacencyAtomRowCertificate_unconditional_direct
#print axioms piPlusBooleanProjectedTransitionAtomRowCertificate_unconditional_direct
#print axioms cookLevinFactoredRowCertificate_unconditional_booleanity_identity_obstruction

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
