import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanityAlignmentObstruction

/-!
# Booleanity factors need post-pullback normalization

After the constant-coefficient obstruction, the next natural target was a row
certificate for the actual Booleanity factor `1 - X_v(1-X_v)`.  But in the
current Route-C row language the left side is

  `Pi⁺⁻¹ ( BooleanNormalize ( Pi⁺ factor ) )`

with no final multilinear projection after the inverse map.  For Booleanity
factors this is still too raw: the inverse half-Hadamard can reintroduce square
terms.  Thus the honest next seam is a *post-pullback normalization* bridge.

This file names that bridge and routes the corrected Booleanity payload through
it, without asserting the false raw certificate.
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

/-- Booleanity row certificate with a final multilinear projection after the
inverse half-Hadamard pullback.  This is the corrected surface for unary
Booleanity factors. -/
def PiPlusBooleanProjectedBooleanityFactorProjectedRowCertificate
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
          mlProj
            ((piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
              (zeroProfileBooleanNormalize
                (piPlusSATBlockAlgEquiv M n hn2 htb hns D
                  (((1 : MvPolynomial (Fin n) ℚ) - (boolLC n v).poly) :
                    SATDeciderGaugeSpace M n hn2 htb hns)))) =
            mlProj
              (m * SPDP.iterDerivList S
                ((((1 : MvPolynomial (Fin n) ℚ) - (boolLC n v).poly) :
                  SATDeciderGaugeSpace M n hn2 htb hns)))

/-- The post-pullback normalization bridge: projected Booleanity rows imply the
raw row certificate requested by the current assembly interface.  This is exactly
the seam that must be supplied if the downstream interface remains raw. -/
def PiPlusBooleanityPostPullbackNormalizationBridge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin n) : Prop :=
  PiPlusBooleanProjectedBooleanityFactorProjectedRowCertificate
    M n hn2 htb hns D v →
  PiPlusBooleanProjectedBooleanityFactorRowCertificate
    M n hn2 htb hns D v

/-- Booleanity payload on the projected/corrected surface. -/
def CookLevinBooleanityFactorProjectedRowPayload
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop :=
  ∀ v : Fin n,
    PiPlusBooleanProjectedBooleanityFactorProjectedRowCertificate
      M n hn2 htb hns D v

/-- List-level post-pullback normalization bridge. -/
def CookLevinBooleanityPostPullbackNormalizationBridge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop :=
  ∀ v : Fin n,
    PiPlusBooleanityPostPullbackNormalizationBridge M n hn2 htb hns D v

/-- Projected Booleanity rows plus post-pullback normalization recover the
previous corrected Booleanity payload. -/
theorem booleanityFactorRowPayload_of_projectedRows_postPullbackNormalization
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (hproj : CookLevinBooleanityFactorProjectedRowPayload M n hn2 htb hns D)
    (hbridge : CookLevinBooleanityPostPullbackNormalizationBridge
      M n hn2 htb hns D) :
    CookLevinBooleanityFactorRowPayload M n hn2 htb hns D := by
  intro v
  exact hbridge v (hproj v)

/-- Paper-scale projected Booleanity payload. -/
abbrev PaperScaleCookLevinBooleanityFactorProjectedRowPayload
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  CookLevinBooleanityFactorProjectedRowPayload
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale post-pullback normalization bridge. -/
abbrev PaperScaleCookLevinBooleanityPostPullbackNormalizationBridge
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  CookLevinBooleanityPostPullbackNormalizationBridge
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale previous Booleanity payload from the corrected projected surface
plus the post-pullback normalization bridge. -/
theorem paperScale_booleanityFactorRowPayload_of_projectedRows_postPullbackNormalization
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hproj : PaperScaleCookLevinBooleanityFactorProjectedRowPayload M htb hns)
    (hbridge : PaperScaleCookLevinBooleanityPostPullbackNormalizationBridge
      M htb hns) :
    PaperScaleCookLevinBooleanityFactorRowPayload M htb hns :=
  booleanityFactorRowPayload_of_projectedRows_postPullbackNormalization
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    hproj hbridge

/-- Paper-scale corrected constraint-list inputs from the projected Booleanity
surface plus post-pullback normalization. -/
theorem paperScale_correctedConstraintListAtomicRowInputs_of_projectedRows_postPullbackNormalization
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hproj : PaperScaleCookLevinBooleanityFactorProjectedRowPayload M htb hns)
    (hbridge : PaperScaleCookLevinBooleanityPostPullbackNormalizationBridge
      M htb hns) :
    PaperScaleCookLevinCorrectedConstraintListAtomicRowInputs M htb hns :=
  paperScale_correctedConstraintListAtomicRowInputs_of_booleanityRows
    M htb hns
    (paperScale_booleanityFactorRowPayload_of_projectedRows_postPullbackNormalization
      M htb hns hproj hbridge)

/-! ## Axiom audit anchors -/

#print axioms booleanityFactorRowPayload_of_projectedRows_postPullbackNormalization
#print axioms paperScale_booleanityFactorRowPayload_of_projectedRows_postPullbackNormalization
#print axioms paperScale_correctedConstraintListAtomicRowInputs_of_projectedRows_postPullbackNormalization

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
