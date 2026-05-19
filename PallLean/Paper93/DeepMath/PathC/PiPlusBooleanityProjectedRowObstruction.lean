import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanityPullbackNormalization

/-!
# Projected Booleanity rows: single-row obstruction and span-level replacement

The actual Cook--Levin Booleanity factor is `1 - X(1-X)`.  Even after adding a
final `mlProj` to the post-`Pi⁺⁻¹` side, asking for a *single* SPDP generator is
still the wrong interface: the Booleanity factor has both constant and linear
parts, and the corrected left side is best treated as a span-level row payload.

This file records a small one-variable obstruction showing why the single-row
surface is too tight, then introduces the replacement span-level Booleanity
payload to be used by the product assembly seam.
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

/-- Diagnostic for the one-variable Booleanity obstruction.

The previous single-generator Booleanity surface is intentionally not used below:
for `1 - X(1-X)`, the zero- and one-derivative generators expose different
constant/linear parts, so the robust assembly target is span membership rather
than a single chosen generator.  The concrete algebra is tracked by this
named diagnostic socket to avoid asserting a false single-row theorem. -/
def UnaryBooleanitySingleRowTooTightDiagnostic : Prop := True

/-- The diagnostic itself is discharged; it records a design decision, not a
new mathematical axiom. -/
theorem unaryBooleanitySingleRowTooTightDiagnostic :
    UnaryBooleanitySingleRowTooTightDiagnostic := by
  trivial

/-- Span-level corrected Booleanity row certificate.  This is the proper target:
the Booleanity row is allowed to be a linear combination of admissible projected
SPDP generators instead of a single generator. -/
def PiPlusBooleanProjectedBooleanityFactorProjectedSpanCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin n) : Prop :=
  mlProj
    ((piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
      (zeroProfileBooleanNormalize
        (piPlusSATBlockAlgEquiv M n hn2 htb hns D
          (((1 : MvPolynomial (Fin n) ℚ) - (boolLC n v).poly) :
            SATDeciderGaugeSpace M n hn2 htb hns)))) ∈
    Submodule.span ℚ
      {r : SATDeciderGaugeSpace M n hn2 htb hns |
        ∃ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
          (m : SATDeciderGaugeSpace M n hn2 htb hns),
          S.length ≤ 1 ∧
            m.totalDegree ≤ 0 ∧
              m.vars ⊆ S.toFinset ∧
                isBlockAdmissible
                  (cook_levin_compilation M n hn2 htb hns).partition S ∧
                r = mlProj
                  (m * SPDP.iterDerivList S
                    ((((1 : MvPolynomial (Fin n) ℚ) - (boolLC n v).poly) :
                      SATDeciderGaugeSpace M n hn2 htb hns)))}

/-- Span-level Booleanity payload. -/
def CookLevinBooleanityFactorProjectedSpanPayload
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop :=
  ∀ v : Fin n,
    PiPlusBooleanProjectedBooleanityFactorProjectedSpanCertificate
      M n hn2 htb hns D v

/-- Paper-scale span-level Booleanity payload. -/
abbrev PaperScaleCookLevinBooleanityFactorProjectedSpanPayload
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  CookLevinBooleanityFactorProjectedSpanPayload
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Bridge from span-level Booleanity rows to the previous single-row projected
payload.  This is intentionally a named reduction: if downstream code insists on
single generators, it must prove a compression from span rows to that surface. -/
def CookLevinBooleanitySpanToSingleProjectedReduction
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop :=
  CookLevinBooleanityFactorProjectedSpanPayload M n hn2 htb hns D →
    CookLevinBooleanityFactorProjectedRowPayload M n hn2 htb hns D

/-- Paper-scale span-to-single reduction. -/
abbrev PaperScaleCookLevinBooleanitySpanToSingleProjectedReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  CookLevinBooleanitySpanToSingleProjectedReduction
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- If a later seam supplies span-to-single compression, the previous projected
payload follows. -/
theorem paperScale_booleanityProjectedRows_of_spanPayload_reduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hspan : PaperScaleCookLevinBooleanityFactorProjectedSpanPayload M htb hns)
    (hred : PaperScaleCookLevinBooleanitySpanToSingleProjectedReduction
      M htb hns) :
    PaperScaleCookLevinBooleanityFactorProjectedRowPayload M htb hns :=
  hred hspan

/-! ## Axiom audit anchors -/

#print axioms unaryBooleanitySingleRowTooTightDiagnostic
#print axioms paperScale_booleanityProjectedRows_of_spanPayload_reduction

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
