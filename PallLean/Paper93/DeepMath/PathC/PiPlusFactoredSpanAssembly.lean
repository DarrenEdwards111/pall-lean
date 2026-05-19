import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanityProjectedRowObstruction

/-!
# Span-level Booleanity inputs for factored assembly

The Booleanity side of the Cook--Levin product should no longer be routed
through the over-tight single-row payload.  This file promotes the new
span-level Booleanity certificate to the factored assembly frontier, while
keeping the rest side on the already-closed signed-cross row payload.

The remaining product theorem is now stated at the correct granularity:
span-level Booleanity rows + signed-cross rest rows imply the factored compiled
row certificate.  No span-to-single compression is required by this route.
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

/-- Correct factored-assembly input surface: Booleanity rows are span-level
projected rows; non-Boolean rest constraints remain signed-cross rows. -/
structure CookLevinSpanConstraintListAtomicRowInputs
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop where
  booleanity_span :
    CookLevinBooleanityFactorProjectedSpanPayload M n hn2 htb hns D
  booleanity_residue_rank :
    CookLevinBooleanityResidueRankPayload M n hn2 htb hns D
  rest_signed : CookLevinRestConstraintSignedCrossRows M n hn2 htb hns D

/-- Once the span-level Booleanity payload is supplied, the full span-level
constraint-list input surface is available because rest rows are unconditional. -/
theorem spanConstraintListAtomicRowInputs_of_booleanitySpan
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (hbool : CookLevinBooleanityFactorProjectedSpanPayload
      M n hn2 htb hns D) :
    CookLevinSpanConstraintListAtomicRowInputs M n hn2 htb hns D where
  booleanity_span := hbool
  booleanity_residue_rank :=
    cookLevinBooleanityResidueRankPayload_unconditional M n hn2 htb hns D
  rest_signed := cookLevinRestConstraintSignedCrossRows_unconditional
    M n hn2 htb hns D

/-- Paper-scale span-level constraint-list inputs. -/
abbrev PaperScaleCookLevinSpanConstraintListAtomicRowInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  CookLevinSpanConstraintListAtomicRowInputs
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale span-level inputs from a paper-scale Booleanity span payload. -/
theorem paperScale_spanConstraintListAtomicRowInputs_of_booleanitySpan
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hbool : PaperScaleCookLevinBooleanityFactorProjectedSpanPayload M htb hns) :
    PaperScaleCookLevinSpanConstraintListAtomicRowInputs M htb hns :=
  spanConstraintListAtomicRowInputs_of_booleanitySpan
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) hbool

/-- Product assembly at the corrected span-level surface.

This replaces the earlier route that tried to compress Booleanity span rows into
single generators before assembly.  The remaining theorem is precisely the
Leibniz/product synthesis over a Booleanity span payload and rest signed-cross
payload. -/
structure PaperScaleCookLevinFactoredRowCertificateSpanAssemblyReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  assemble : PaperScaleCookLevinSpanConstraintListAtomicRowInputs M htb hns →
    PaperScalePiPlusBooleanProjectedFactoredCompiledRowCertificateOneZero
      M htb hns

/-- Span-level Booleanity payload plus the span-level product assembly reduction
gives the factored compiled-row certificate directly. -/
theorem paperScale_factoredCompiledRowCertificate_of_booleanitySpan_spanAssemblyReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hbool : PaperScaleCookLevinBooleanityFactorProjectedSpanPayload M htb hns)
    (hred : PaperScaleCookLevinFactoredRowCertificateSpanAssemblyReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedFactoredCompiledRowCertificateOneZero
      M htb hns :=
  hred.assemble
    (paperScale_spanConstraintListAtomicRowInputs_of_booleanitySpan
      M htb hns hbool)

/-- Span-level assembly closes the paper-scale P-side raw-pullback membership
through the existing factored certificate route. -/
theorem paperScale_windowedCompiledRawPullbackMembershipOneZero_of_booleanitySpan_spanAssemblyReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hbool : PaperScaleCookLevinBooleanityFactorProjectedSpanPayload M htb hns)
    (hred : PaperScaleCookLevinFactoredRowCertificateSpanAssemblyReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembershipOneZero
      M htb hns :=
  paperScale_windowedCompiledRawPullbackMembershipOneZero_of_factoredRowCertificate
    M htb hns
    (paperScale_factoredCompiledRowCertificate_of_booleanitySpan_spanAssemblyReduction
      M htb hns hbool hred)

/-- Final contradiction closeout from the corrected span-level assembly surface,
NP-window inclusion, and the existing Route-B one-window blockers. -/
theorem no_decidesSAT_at_paperScale_of_booleanitySpan_spanAssemblyReduction_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hbool : PaperScaleCookLevinBooleanityFactorProjectedSpanPayload M htb hns)
    (hred : PaperScaleCookLevinFactoredRowCertificateSpanAssemblyReduction
      M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns)
    (W : SymmetricPowerBound.ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ))
    (W_finite : ∀ τ, Module.Finite ℚ ↥(W τ))
    (W_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (zero_common_span :
      CookLevinOneWindowZeroHistogramShiftCommonSpan
        M (2 ^ 804) paperScale_ge_two htb hns)
    (per_type_spanning :
      CookLevinOneWindowPerTypeSpanningActiveAdmissibleProfileCases
        M (2 ^ 804) paperScale_ge_two htb hns W) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_factoredRowCertificate_npInclusion
    M htb hns
    (paperScale_factoredCompiledRowCertificate_of_booleanitySpan_spanAssemblyReduction
      M htb hns hbool hred)
    hnp W W_finite W_dim zero_common_span per_type_spanning

/-! ## Axiom audit anchors -/

#print axioms CookLevinSpanConstraintListAtomicRowInputs.booleanity_residue_rank
#print axioms spanConstraintListAtomicRowInputs_of_booleanitySpan
#print axioms paperScale_spanConstraintListAtomicRowInputs_of_booleanitySpan
#print axioms paperScale_factoredCompiledRowCertificate_of_booleanitySpan_spanAssemblyReduction
#print axioms paperScale_windowedCompiledRawPullbackMembershipOneZero_of_booleanitySpan_spanAssemblyReduction
#print axioms no_decidesSAT_at_paperScale_of_booleanitySpan_spanAssemblyReduction_npInclusion

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
