import PallLean.Paper93.DeepMath.PathC.PiPlusFactoredConstraintCaseSplit

/-!
# Booleanity alignment obstruction and corrected socket

The first constraint-list split exposed a tempting but false alignment target:
identifying a Cook--Levin Booleanity factor `1 - X_v(1-X_v)` with the mixed
block monomial `X_false * X_true`.  This file records the obstruction
kernel-cleanly: the former has constant term `1`, the latter has constant term
`0`.

The corrected next target is therefore not equality to the mixed monomial, but a
Booleanity-factor row certificate in its own right.  The mixed Booleanity
discharge remains the local algebraic guide; it cannot replace the unary factor
by definitional equality.
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

/-- A mixed monomial has zero constant coefficient. -/
theorem constantCoeff_X_mul_X_zero {σ : Type*} [DecidableEq σ]
    (a b : σ) :
    MvPolynomial.constantCoeff
      ((MvPolynomial.X a * MvPolynomial.X b) : MvPolynomial σ ℚ) = 0 := by
  rw [map_mul, MvPolynomial.constantCoeff_X]
  simp

/-- A Cook--Levin Booleanity factor has constant coefficient `1`. -/
theorem constantCoeff_boolLC_factor_one (n : Nat) (v : Fin n) :
    MvPolynomial.constantCoeff
      ((1 : MvPolynomial (Fin n) ℚ) - (boolLC n v).poly) = 1 := by
  rw [MvPolynomial.constantCoeff_eq]
  exact cookLevinBooleanFactor_const_one n v

/-- The raw Cook--Levin Booleanity factor cannot be definitionally identified
with a mixed block monomial.  This is the precise obstruction to the too-strong
`CookLevinBooleanityFactorMixedAlignment` equality target. -/
theorem boolLC_factor_ne_mixed_monomial
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin n) (i : D.blockIndex) :
    ((1 : MvPolynomial (Fin n) ℚ) - (boolLC n v).poly :
        SATDeciderGaugeSpace M n hn2 htb hns) ≠
      ((X (satBlockFalse M n hn2 htb hns D i)) *
        (X (satBlockTrue M n hn2 htb hns D i)) :
        SATDeciderGaugeSpace M n hn2 htb hns) := by
  intro h
  have hc := congrArg MvPolynomial.constantCoeff h
  rw [constantCoeff_boolLC_factor_one n v] at hc
  have hright : MvPolynomial.constantCoeff
      ((X (satBlockFalse M n hn2 htb hns D i)) *
        (X (satBlockTrue M n hn2 htb hns D i)) :
        SATDeciderGaugeSpace M n hn2 htb hns) = 0 :=
    constantCoeff_X_mul_X_zero
      (satBlockFalse M n hn2 htb hns D i)
      (satBlockTrue M n hn2 htb hns D i)
  have h10 : (1 : ℚ) = 0 := hc.trans hright
  norm_num at h10

/-- Corrected Booleanity-factor row certificate socket.

Unlike the false mixed-monomial equality, this asks directly for a row
certificate for the actual Cook--Levin Booleanity factor. -/
def PiPlusBooleanProjectedBooleanityFactorRowCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin n) : Prop :=
  ∃ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length ≤ 1 ∧
      m.totalDegree ≤ 0 ∧
        m.vars ⊆ S.toFinset ∧
          isBlockAdmissible
            (cook_levin_compilation M n hn2 htb hns).partition S ∧
          (piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
            (zeroProfileBooleanNormalize
              (piPlusSATBlockAlgEquiv M n hn2 htb hns D
                (((1 : MvPolynomial (Fin n) ℚ) - (boolLC n v).poly) :
                  SATDeciderGaugeSpace M n hn2 htb hns))) =
            mlProj
              (m * SPDP.iterDerivList S
                ((((1 : MvPolynomial (Fin n) ℚ) - (boolLC n v).poly) :
                  SATDeciderGaugeSpace M n hn2 htb hns)))

/-- Corrected Booleanity-list row payload: every Booleanity constraint has a
row certificate for the actual factor `1 - lc.poly`. -/
def CookLevinBooleanityFactorRowPayload
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop :=
  ∀ v : Fin n,
    PiPlusBooleanProjectedBooleanityFactorRowCertificate
      M n hn2 htb hns D v

/-- Paper-scale corrected Booleanity-factor row payload. -/
abbrev PaperScaleCookLevinBooleanityFactorRowPayload
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  CookLevinBooleanityFactorRowPayload
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Corrected constraint-list inputs: Booleanity rows are requested for the real
Booleanity factors, while rest rows remain the already-proved signed-cross
payload. -/
structure CookLevinCorrectedConstraintListAtomicRowInputs
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop where
  booleanity_rows : CookLevinBooleanityFactorRowPayload M n hn2 htb hns D
  rest_signed : CookLevinRestConstraintSignedCrossRows M n hn2 htb hns D

/-- Once the corrected Booleanity rows are supplied, the corrected constraint
inputs are available; the rest side is still unconditional. -/
theorem correctedConstraintListAtomicRowInputs_of_booleanityRows
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (hbool : CookLevinBooleanityFactorRowPayload M n hn2 htb hns D) :
    CookLevinCorrectedConstraintListAtomicRowInputs M n hn2 htb hns D where
  booleanity_rows := hbool
  rest_signed := cookLevinRestConstraintSignedCrossRows_unconditional
    M n hn2 htb hns D

/-- Paper-scale corrected constraint-list inputs. -/
abbrev PaperScaleCookLevinCorrectedConstraintListAtomicRowInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  CookLevinCorrectedConstraintListAtomicRowInputs
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale corrected inputs from the corrected Booleanity row payload. -/
theorem paperScale_correctedConstraintListAtomicRowInputs_of_booleanityRows
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hbool : PaperScaleCookLevinBooleanityFactorRowPayload M htb hns) :
    PaperScaleCookLevinCorrectedConstraintListAtomicRowInputs M htb hns :=
  correctedConstraintListAtomicRowInputs_of_booleanityRows
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) hbool

/-! ## Axiom audit anchors -/

#print axioms constantCoeff_X_mul_X_zero
#print axioms constantCoeff_boolLC_factor_one
#print axioms boolLC_factor_ne_mixed_monomial
#print axioms correctedConstraintListAtomicRowInputs_of_booleanityRows
#print axioms paperScale_correctedConstraintListAtomicRowInputs_of_booleanityRows

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
