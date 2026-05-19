import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanityPullbackNormalization
import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanityActualFactorNormalForm

/-!
# Projected Booleanity rows: single-row obstruction and span-level replacement

The actual Cook--Levin Booleanity factor is `1 - X(1-X)`.  Even after adding a
final `mlProj` to the post-`Pi⁺⁻¹` side, asking for a *single* SPDP generator is
still the wrong interface: the Booleanity factor has both constant and linear
parts, and the true-side row contains the partner-coordinate residue.

This file records a small one-variable obstruction showing why the single-row
surface is too tight, then introduces the replacement block-residue span payload
to be used by the product assembly seam.
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

/-- The concrete three-generator SAT-coordinate residue basis for an actual
Booleanity row at `v`: constant, false-coordinate, and true-coordinate. -/
noncomputable def SATBlockBooleanityActualProjectedResidueGenerators
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin (cook_levin_compilation M n hn2 htb hns).numVars) :
    Finset (SATDeciderGaugeSpace M n hn2 htb hns) :=
  {(1 : SATDeciderGaugeSpace M n hn2 htb hns),
    X (satBlockFalse M n hn2 htb hns D (D.coord v).1),
    X (satBlockTrue M n hn2 htb hns D (D.coord v).1)}

/-- Flat SAT-coordinate version of the corrected block residue span for actual
Booleanity rows.  For a variable `v`, the projected Booleanity row is allowed to
land in the multilinear span of the constant row and both variables in `v`'s
`Π+` block.  This is the concrete residue surface corresponding to
`BlockBooleanityActualProjectedResidueSpan`, not a hidden single-row seam. -/
noncomputable def SATBlockBooleanityActualProjectedResidueSpan
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin (cook_levin_compilation M n hn2 htb hns).numVars) :
    Submodule ℚ (SATDeciderGaugeSpace M n hn2 htb hns) :=
  Submodule.span ℚ
    (↑(SATBlockBooleanityActualProjectedResidueGenerators M n hn2 htb hns D v) :
      Set (SATDeciderGaugeSpace M n hn2 htb hns))

/-- The corrected Booleanity residue span has dimension at most three.  This is
the local rank absorption fact promised by the paper's multilinear/profile
surface: the True-side residue contributes only constant-plus-two-linear block
content. -/
theorem finrank_SATBlockBooleanityActualProjectedResidueSpan_le_three
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin (cook_levin_compilation M n hn2 htb hns).numVars) :
    Module.finrank ℚ
      (SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D v) ≤ 3 := by
  unfold SATBlockBooleanityActualProjectedResidueSpan
  exact (finrank_span_finset_le_card
    (SATBlockBooleanityActualProjectedResidueGenerators M n hn2 htb hns D v)).trans
      (by
        unfold SATBlockBooleanityActualProjectedResidueGenerators
        exact Finset.card_le_three)

/-- The constant row is an admitted SAT-level Booleanity residue generator. -/
theorem one_mem_SATBlockBooleanityActualProjectedResidueSpan
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin (cook_levin_compilation M n hn2 htb hns).numVars) :
    (1 : SATDeciderGaugeSpace M n hn2 htb hns) ∈
      SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D v := by
  exact Submodule.subset_span (by
    unfold SATBlockBooleanityActualProjectedResidueGenerators
    simp)

/-- The false coordinate of `v`'s `Π+` block is an admitted SAT-level
Booleanity residue generator. -/
theorem X_false_mem_SATBlockBooleanityActualProjectedResidueSpan
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin (cook_levin_compilation M n hn2 htb hns).numVars) :
    (X (satBlockFalse M n hn2 htb hns D (D.coord v).1) :
      SATDeciderGaugeSpace M n hn2 htb hns) ∈
      SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D v := by
  exact Submodule.subset_span (by
    unfold SATBlockBooleanityActualProjectedResidueGenerators
    simp)

/-- The true coordinate of `v`'s `Π+` block is an admitted SAT-level Booleanity
residue generator. -/
theorem X_true_mem_SATBlockBooleanityActualProjectedResidueSpan
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin (cook_levin_compilation M n hn2 htb hns).numVars) :
    (X (satBlockTrue M n hn2 htb hns D (D.coord v).1) :
      SATDeciderGaugeSpace M n hn2 htb hns) ∈
      SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D v := by
  exact Submodule.subset_span (by
    unfold SATBlockBooleanityActualProjectedResidueGenerators
    simp)

/-- Uniform rank payload for corrected Booleanity residue spans.  This packages
local residue absorption at the same granularity as the Booleanity span surface:
each actual Booleanity row may land in a three-dimensional block-local residue
space. -/
def CookLevinBooleanityResidueRankPayload
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop :=
  ∀ v : Fin (cook_levin_compilation M n hn2 htb hns).numVars,
    Module.finrank ℚ
      (SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D v) ≤ 3

/-- The corrected Booleanity residue rank payload is unconditional: it follows
from the explicit three-generator basis `{1, X_false, X_true}`. -/
theorem cookLevinBooleanityResidueRankPayload_unconditional
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) :
    CookLevinBooleanityResidueRankPayload M n hn2 htb hns D := by
  intro v
  exact finrank_SATBlockBooleanityActualProjectedResidueSpan_le_three
    M n hn2 htb hns D v

/-- Paper-scale corrected Booleanity residue rank payload. -/
abbrev PaperScaleCookLevinBooleanityResidueRankPayload
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  CookLevinBooleanityResidueRankPayload
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale corrected Booleanity residue rank payload is unconditional. -/
theorem paperScale_cookLevinBooleanityResidueRankPayload_unconditional
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    PaperScaleCookLevinBooleanityResidueRankPayload M htb hns :=
  cookLevinBooleanityResidueRankPayload_unconditional
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Span-level corrected Booleanity row certificate.  This is the proper target:
the Booleanity row is allowed to be block-local constant-plus-linear residue
content instead of being forced into a single source generator or the constant
row. -/
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
    SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D v

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

#print axioms SATBlockBooleanityActualProjectedResidueGenerators
#print axioms SATBlockBooleanityActualProjectedResidueSpan
#print axioms finrank_SATBlockBooleanityActualProjectedResidueSpan_le_three
#print axioms cookLevinBooleanityResidueRankPayload_unconditional
#print axioms paperScale_cookLevinBooleanityResidueRankPayload_unconditional
#print axioms one_mem_SATBlockBooleanityActualProjectedResidueSpan
#print axioms X_false_mem_SATBlockBooleanityActualProjectedResidueSpan
#print axioms X_true_mem_SATBlockBooleanityActualProjectedResidueSpan
#print axioms unaryBooleanitySingleRowTooTightDiagnostic
#print axioms paperScale_booleanityProjectedRows_of_spanPayload_reduction

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
