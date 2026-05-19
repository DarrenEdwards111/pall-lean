import PallLean.Paper93.DeepMath.PathC.PiPlusOneOneLocalFactorPayload

/-!
# One-one allocation reduction from local factor payloads

After the parity split, the honest global P-side window is `(1,1)`.  This file
names the remaining product/allocation seam precisely: prove that the now
unconditional paper-scale local-factor payload is sufficient to build the
transformed Leibniz generator allocation certificate.

The bridge here is intentionally not the full proof of product assembly.  It is
axiom-free plumbing that lets downstream closeouts depend on one sharp reduction
rather than repeatedly unpacking parity/cross/same-block cases.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine
open LeibnizProduct

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- The remaining `(1,1)` product/allocation seam: the unconditional local-factor
payload is sufficient to construct the paper-scale transformed Leibniz generator
allocation certificate.

This is the exact next mathematical target for product assembly. -/
structure PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  allocation_of_local :
    ∀ (_payload : BoolPoly.PaperScalePiPlusBooleanProjectedOneOneLocalFactorPayload M htb hns),
      PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorAllocationCertificateOneOne
        M htb hns

/-- Because the local-factor payload is now unconditional, the allocation
reduction immediately yields the `(1,1)` allocation certificate. -/
theorem paperScale_transformedLeibnizGeneratorAllocationCertificateOneOne_of_localFactorReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorAllocationCertificateOneOne
      M htb hns :=
  hred.allocation_of_local
    (BoolPoly.paperScalePiPlusBooleanProjectedOneOneLocalFactorPayload_unconditional
      M htb hns)

/-- The local-factor-to-allocation reduction yields the `(1,1)` transformed
Leibniz generator row certificate. -/
theorem paperScale_transformedLeibnizGeneratorRowCertificateOneOne_of_localFactorReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificateOneOne
      M htb hns :=
  paperScale_transformedLeibnizGeneratorRowCertificateOneOne_of_allocationCertificate
    M htb hns
    (paperScale_transformedLeibnizGeneratorAllocationCertificateOneOne_of_localFactorReduction
      M htb hns hred)

/-- The local-factor-to-allocation reduction yields the `(1,1)` transformed
Leibniz generator pullback. -/
theorem paperScale_transformedLeibnizGeneratorPullbackOneOne_of_localFactorReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorPullbackOneOne
      M htb hns :=
  paperScale_transformedLeibnizGeneratorPullbackOneOne_of_rowCertificate
    M htb hns
    (paperScale_transformedLeibnizGeneratorRowCertificateOneOne_of_localFactorReduction
      M htb hns hred)

/-- Normalized polynomial span plus the local-factor-to-allocation reduction
closes the `(1,1)` factored row-span classifier. -/
theorem paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_localFactorReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedFactoredRowSpanClassifierOneOne M htb hns :=
  paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_allocationCertificate
    M htb hns hpoly
    (paperScale_transformedLeibnizGeneratorAllocationCertificateOneOne_of_localFactorReduction
      M htb hns hred)

/-- A compact closeout package for the widened `(1,1)` P-side route.  It records
that the remaining inputs are exactly:

1. normalized-derivative polynomial span; and
2. local-factor-to-allocation product assembly.

No full product theorem is asserted here without the reduction. -/
structure PaperScalePiPlusBooleanProjectedOneOnePsideCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  polynomial_span : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
    M htb hns
  local_factor_to_allocation :
    PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns

/-- The compact closeout inputs imply the `(1,1)` factored row-span classifier. -/
theorem paperScale_factoredRowSpanClassifierOneOne_of_closeoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs : PaperScalePiPlusBooleanProjectedOneOnePsideCloseoutInputs
      M htb hns) :
    PaperScalePiPlusBooleanProjectedFactoredRowSpanClassifierOneOne M htb hns :=
  paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_localFactorReduction
    M htb hns hinputs.polynomial_span hinputs.local_factor_to_allocation

/-! ## Axiom audit anchors -/

#print axioms paperScale_transformedLeibnizGeneratorAllocationCertificateOneOne_of_localFactorReduction
#print axioms paperScale_transformedLeibnizGeneratorRowCertificateOneOne_of_localFactorReduction
#print axioms paperScale_transformedLeibnizGeneratorPullbackOneOne_of_localFactorReduction
#print axioms paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_localFactorReduction
#print axioms paperScale_factoredRowSpanClassifierOneOne_of_closeoutInputs

end PallLean.Paper93.DeepMath.PathC
