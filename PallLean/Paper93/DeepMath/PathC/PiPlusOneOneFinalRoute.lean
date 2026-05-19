import PallLean.Paper93.DeepMath.PathC.PiPlusOneOneAllocationReduction

/-!
# One-one final-route bridges

This file mirrors the old paper-scale `OneZero` final route at the widened
`(1,1)` window forced by same-block rest factors.  It does not prove the
remaining product/allocation reduction; instead it wires the new `(1,1)`
classifier and closeout inputs into the compiled raw-pullback and P-subspace
sockets used downstream.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- A `(1,1)` factored row-span classifier closes the paper-scale compiled
raw-pullback membership socket at `(1,1)`. -/
theorem paperScale_windowedCompiledRawPullbackMembershipOneOne_of_rowSpanClassifier
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hclass : PaperScalePiPlusBooleanProjectedFactoredRowSpanClassifierOneOne
      M htb hns) :
    PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembershipOneOne
      M htb hns :=
  compiledRawPullbackMembership_of_factoredRowSpanClassifier
    1 1 M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hclass

/-- A `(1,1)` factored row-span classifier closes the paper-scale compiled
P-subspace inclusion socket at `(1,1)`. -/
theorem paperScale_compiledPSubspaceInclusionOneOne_of_rowSpanClassifier
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hclass : PaperScalePiPlusBooleanProjectedFactoredRowSpanClassifierOneOne
      M htb hns) :
    PaperScalePiPlusBooleanProjectedCompiledPSubspaceInclusionOneOne
      M htb hns :=
  compiledPSubspaceInclusion_of_compiledRawPullbackMembership
    1 1 M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (paperScale_windowedCompiledRawPullbackMembershipOneOne_of_rowSpanClassifier
      M htb hns hclass)

/-- The compact `(1,1)` P-side closeout inputs close the factored row-span
classifier. -/
theorem paperScale_factoredRowSpanClassifierOneOne_of_psideCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs : PaperScalePiPlusBooleanProjectedOneOnePsideCloseoutInputs
      M htb hns) :
    PaperScalePiPlusBooleanProjectedFactoredRowSpanClassifierOneOne M htb hns :=
  paperScale_factoredRowSpanClassifierOneOne_of_closeoutInputs
    M htb hns hinputs

/-- The compact `(1,1)` P-side closeout inputs close the compiled raw-pullback
membership socket. -/
theorem paperScale_windowedCompiledRawPullbackMembershipOneOne_of_psideCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs : PaperScalePiPlusBooleanProjectedOneOnePsideCloseoutInputs
      M htb hns) :
    PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembershipOneOne
      M htb hns :=
  paperScale_windowedCompiledRawPullbackMembershipOneOne_of_rowSpanClassifier
    M htb hns
    (paperScale_factoredRowSpanClassifierOneOne_of_psideCloseoutInputs
      M htb hns hinputs)

/-- The compact `(1,1)` P-side closeout inputs close the compiled P-subspace
inclusion socket. -/
theorem paperScale_compiledPSubspaceInclusionOneOne_of_psideCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs : PaperScalePiPlusBooleanProjectedOneOnePsideCloseoutInputs
      M htb hns) :
    PaperScalePiPlusBooleanProjectedCompiledPSubspaceInclusionOneOne
      M htb hns :=
  paperScale_compiledPSubspaceInclusionOneOne_of_rowSpanClassifier
    M htb hns
    (paperScale_factoredRowSpanClassifierOneOne_of_psideCloseoutInputs
      M htb hns hinputs)

/-- If the remaining product/allocation reduction is supplied, polynomial span
alone closes the `(1,1)` compiled raw-pullback membership socket. -/
theorem paperScale_windowedCompiledRawPullbackMembershipOneOne_of_polynomialSpan_and_localFactorReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembershipOneOne
      M htb hns :=
  paperScale_windowedCompiledRawPullbackMembershipOneOne_of_rowSpanClassifier
    M htb hns
    (paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_localFactorReduction
      M htb hns hpoly hred)

/-- If the remaining product/allocation reduction is supplied, polynomial span
alone closes the `(1,1)` compiled P-subspace inclusion socket. -/
theorem paperScale_compiledPSubspaceInclusionOneOne_of_polynomialSpan_and_localFactorReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedCompiledPSubspaceInclusionOneOne
      M htb hns :=
  paperScale_compiledPSubspaceInclusionOneOne_of_rowSpanClassifier
    M htb hns
    (paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_localFactorReduction
      M htb hns hpoly hred)

/-! ## Axiom audit anchors -/

#print axioms paperScale_windowedCompiledRawPullbackMembershipOneOne_of_rowSpanClassifier
#print axioms paperScale_compiledPSubspaceInclusionOneOne_of_rowSpanClassifier
#print axioms paperScale_factoredRowSpanClassifierOneOne_of_psideCloseoutInputs
#print axioms paperScale_windowedCompiledRawPullbackMembershipOneOne_of_psideCloseoutInputs
#print axioms paperScale_compiledPSubspaceInclusionOneOne_of_psideCloseoutInputs
#print axioms paperScale_windowedCompiledRawPullbackMembershipOneOne_of_polynomialSpan_and_localFactorReduction
#print axioms paperScale_compiledPSubspaceInclusionOneOne_of_polynomialSpan_and_localFactorReduction

end PallLean.Paper93.DeepMath.PathC
