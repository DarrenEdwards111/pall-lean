import PallLean.Paper93.DeepMath.PathC.PiPlusFactoredRowAtomicSynthesis

/-!
# Constraint-list case split for factored Route-C assembly

The atomic row payload is closed, but the Cook--Levin factor list still needs an
honest bridge from list membership to those atoms.  The rest side is already in
cadjacent signed-cross form.  The Booleanity side is subtler: a raw Booleanity
factor `1 - X_v(1-X_v)` is not definitionally the mixed block atom
`X_false * X_true`; that alignment is a separate Booleanity-factor bridge.

This file splits the product-assembly frontier accordingly:

1. rest constraints are discharged directly by the signed-cross atom payload;
2. Booleanity constraints are reduced to a named Booleanity alignment socket;
3. those two list-level inputs imply the previous atomic-to-factored assembly
   reduction.
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

/-- A Booleanity-list factor is aligned with the mixed block atom certificate.

This is intentionally stated as the missing bridge rather than asserted: it is
where one must relate the exposed Cook--Levin factor `1 - X_v(1-X_v)` to the
paired Boolean ambient coordinates used by the mixed atom discharge. -/
def CookLevinBooleanityFactorMixedAlignment
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop :=
  ∀ lc : LocalConstraint n,
    lc ∈ boolConstraintList n →
      ∃ i : D.blockIndex,
        (1 : MvPolynomial (Fin n) ℚ) - lc.poly =
          ((X (satBlockFalse M n hn2 htb hns D i)) *
            (X (satBlockTrue M n hn2 htb hns D i)) :
            SATDeciderGaugeSpace M n hn2 htb hns) ∧
        PiPlusBooleanProjectedMixedAtomRowCertificate M n hn2 htb hns D i

/-- Rest-list factors are discharged by the direct signed-cross payload. -/
def CookLevinRestConstraintSignedCrossRows
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop :=
  ∀ lc : LocalConstraint n,
    lc ∈ adjConstraintList n ++ transSkelConstraintList M n →
      ∃ (c : ℚ) (i : Fin n) (hi : i.val + 1 < n),
        (1 : MvPolynomial (Fin n) ℚ) - lc.poly =
          satSignedCrossAtom M n hn2 htb hns c i ⟨i.val + 1, hi⟩ ∧
        ((D.coord i).1 ≠ (D.coord ⟨i.val + 1, hi⟩).1 →
          PiPlusBooleanProjectedSignedCrossAtomRowCertificate
            M n hn2 htb hns D c i ⟨i.val + 1, hi⟩)

/-- The rest-list signed-cross case split is unconditional. -/
theorem cookLevinRestConstraintSignedCrossRows_unconditional
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) :
    CookLevinRestConstraintSignedCrossRows M n hn2 htb hns D := by
  intro lc hlc
  exact cookLevinRestAtomicSignedRowCertificate_of_mem
    M n hn2 htb hns D lc hlc

/-- Full constraint-list atomic row inputs: Booleanity alignment plus rest
signed-cross rows. -/
structure CookLevinConstraintListAtomicRowInputs
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop where
  booleanity_alignment :
    CookLevinBooleanityFactorMixedAlignment M n hn2 htb hns D
  rest_signed : CookLevinRestConstraintSignedCrossRows M n hn2 htb hns D

/-- With Booleanity alignment, the full constraint-list atomic inputs are
available; the rest side is unconditional. -/
theorem cookLevinConstraintListAtomicRowInputs_of_booleanityAlignment
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (hbool : CookLevinBooleanityFactorMixedAlignment M n hn2 htb hns D) :
    CookLevinConstraintListAtomicRowInputs M n hn2 htb hns D where
  booleanity_alignment := hbool
  rest_signed := cookLevinRestConstraintSignedCrossRows_unconditional
    M n hn2 htb hns D

/-- Paper-scale Booleanity alignment socket. -/
abbrev PaperScaleCookLevinBooleanityFactorMixedAlignment
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  CookLevinBooleanityFactorMixedAlignment
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale full constraint-list atomic row inputs. -/
abbrev PaperScaleCookLevinConstraintListAtomicRowInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  CookLevinConstraintListAtomicRowInputs
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale constraint-list inputs from the Booleanity alignment socket. -/
theorem paperScale_constraintListAtomicRowInputs_of_booleanityAlignment
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hbool : PaperScaleCookLevinBooleanityFactorMixedAlignment M htb hns) :
    PaperScaleCookLevinConstraintListAtomicRowInputs M htb hns :=
  cookLevinConstraintListAtomicRowInputs_of_booleanityAlignment
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) hbool

/-- The next assembly reduction after the constraint-list split: list-level
atomic inputs imply the previous atomic-to-factored product assembly reduction. -/
structure PaperScaleCookLevinFactoredRowCertificateConstraintListAssemblyReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  assemble : PaperScaleCookLevinConstraintListAtomicRowInputs M htb hns →
    PaperScaleCookLevinFactoredRowCertificateAtomicAssemblyReduction M htb hns

/-- Booleanity alignment plus the constraint-list assembly reduction gives the
previous atomic assembly reduction. -/
theorem paperScale_atomicAssemblyReduction_of_constraintListAssemblyReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hbool : PaperScaleCookLevinBooleanityFactorMixedAlignment M htb hns)
    (hred : PaperScaleCookLevinFactoredRowCertificateConstraintListAssemblyReduction
      M htb hns) :
    PaperScaleCookLevinFactoredRowCertificateAtomicAssemblyReduction M htb hns :=
  hred.assemble
    (paperScale_constraintListAtomicRowInputs_of_booleanityAlignment
      M htb hns hbool)

/-- Consequently, Booleanity alignment plus the constraint-list assembly
reduction gives the factored compiled-row certificate. -/
theorem paperScale_factoredCompiledRowCertificate_of_booleanityAlignment_constraintListAssemblyReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hbool : PaperScaleCookLevinBooleanityFactorMixedAlignment M htb hns)
    (hred : PaperScaleCookLevinFactoredRowCertificateConstraintListAssemblyReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedFactoredCompiledRowCertificateOneZero
      M htb hns :=
  paperScale_factoredCompiledRowCertificate_of_atomicAssemblyReduction
    M htb hns
    (paperScale_atomicAssemblyReduction_of_constraintListAssemblyReduction
      M htb hns hbool hred)

/-! ## Axiom audit anchors -/

#print axioms cookLevinRestConstraintSignedCrossRows_unconditional
#print axioms cookLevinConstraintListAtomicRowInputs_of_booleanityAlignment
#print axioms paperScale_constraintListAtomicRowInputs_of_booleanityAlignment
#print axioms paperScale_atomicAssemblyReduction_of_constraintListAssemblyReduction
#print axioms paperScale_factoredCompiledRowCertificate_of_booleanityAlignment_constraintListAssemblyReduction

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
