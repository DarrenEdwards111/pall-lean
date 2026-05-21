import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanityProjectedRowObstruction
import PallLean.Paper93.DeepMath.PathC.PiPlusBoolNPDerivativeErasureObstruction

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
  booleanity_oneHit_derivatives :
    CookLevinBooleanityFactorOneHitDerivativeResiduePayload M n hn2 htb hns D
  booleanity_mixed_derivatives :
    CookLevinBooleanityFactorMixedDerivativeResiduePayload M n hn2 htb hns D
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
  booleanity_oneHit_derivatives :=
    cookLevinBooleanityFactorOneHitDerivativeResiduePayload_unconditional
      M n hn2 htb hns D
  booleanity_mixed_derivatives :=
    cookLevinBooleanityFactorMixedDerivativeResiduePayload_unconditional
      M n hn2 htb hns D
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


/-- The corrected span-level constraint-list inputs are now unconditional: the
Booleanity span payload is discharged by the false/true actual Booleanity normal
forms, the Booleanity residue rank is the explicit three-generator bound, and
rest signed-cross rows were already unconditional. -/
theorem spanConstraintListAtomicRowInputs_unconditional
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) :
    CookLevinSpanConstraintListAtomicRowInputs M n hn2 htb hns D :=
  spanConstraintListAtomicRowInputs_of_booleanitySpan
    M n hn2 htb hns D
    (cookLevinBooleanityFactorProjectedSpanPayload_unconditional
      M n hn2 htb hns D)

/-- Paper-scale corrected span-level constraint-list inputs, fully discharged. -/
theorem paperScale_spanConstraintListAtomicRowInputs_unconditional
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    PaperScaleCookLevinSpanConstraintListAtomicRowInputs M htb hns :=
  spanConstraintListAtomicRowInputs_unconditional
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-! ## Product assembly obstruction

The span/rank payload above is real: each actual Booleanity row lands in a
three-dimensional residue space.  What it does **not** provide is the
product-level Leibniz identity needed to turn local residue membership into the
full factored row certificate.

The tempting unconditional discharge would silently replace the Booleanity
product by its Boolean normal form `1` before differentiating.  The exact missing
identity would be, even in one variable with rest factor `1`,

`liftToBool (iterDerivList [0] (cookLevinBooleanFactorProd 1 * 1)) =
 liftToBool (iterDerivList [0] 1)`.

That identity is false: differentiating `1 - X(1-X)` gives `-1 + 2X`, which is
nonzero in the Boolean ambient.  Therefore `spanAssemblyReduction` cannot be
discharged from the rank bound alone.  A real proof must supply the missing
normalization-aware Leibniz/product algebra, not another named consumer of the
same hypothesis. -/

/-- Exact obstruction to an unconditional rank-only discharge of the former
`spanAssemblyReduction`: Booleanity quotient-normalization does not commute with
the derivative/product assembly step.  This is the concrete false identity that
blocks deriving the full factored row certificate from
`finrank_SATBlockBooleanityActualProjectedResidueSpan_le_three` and profile
finrank bounds alone. -/
theorem spanAssemblyReduction_rankOnly_derivativeErasure_obstruction :
    liftToBool
        (iterDerivList [0]
          (cookLevinBooleanFactorProd 1 * (1 : MvPolynomial (Fin 1) ℚ))) ≠
      liftToBool
        (iterDerivList [0] (1 : MvPolynomial (Fin 1) ℚ)) :=
  booleanityDerivativeErasure_oneVar_counterexample

/-! ## Axiom audit anchors -/

#print axioms CookLevinSpanConstraintListAtomicRowInputs.booleanity_residue_rank
#print axioms CookLevinSpanConstraintListAtomicRowInputs.booleanity_oneHit_derivatives
#print axioms CookLevinSpanConstraintListAtomicRowInputs.booleanity_mixed_derivatives
#print axioms spanConstraintListAtomicRowInputs_of_booleanitySpan
#print axioms paperScale_spanConstraintListAtomicRowInputs_of_booleanitySpan
#print axioms spanConstraintListAtomicRowInputs_unconditional
#print axioms paperScale_spanConstraintListAtomicRowInputs_unconditional
#print axioms spanAssemblyReduction_rankOnly_derivativeErasure_obstruction

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
