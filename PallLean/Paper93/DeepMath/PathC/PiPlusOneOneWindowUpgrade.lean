import PallLean.Paper93.DeepMath.PathC.PiPlusGeneratorAllocationCertificate
import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedWindowedInterfaces

/-!
# One-one window upgrade for Boolean-projected Route C

The paper-scale parity classifier shows that even-left rest factors require a
same-block `(1,1)` local span.  This file adds the parallel paper-scale
`OneOne` theorem surfaces and the axiom-free monotonicity bridges from the older
`OneZero` payloads to the wider `(1,1)` window.
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

namespace BoolPoly

end BoolPoly

/-- Paper-scale compiled-only membership at the `(1,1)` enlarged source window. -/
abbrev PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembershipOneOne
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembership
    1 1 M htb hns

/-- Paper-scale compiled P-subspace inclusion at the `(1,1)` enlarged source
window. -/
abbrev PaperScalePiPlusBooleanProjectedCompiledPSubspaceInclusionOneOne
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PaperScalePiPlusBooleanProjectedCompiledPSubspaceInclusion 1 1 M htb hns

/-- Paper-scale compiled row certificate at `(1,1)`. -/
abbrev PaperScalePiPlusBooleanProjectedWindowedCompiledRowCertificateOneOne
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PaperScalePiPlusBooleanProjectedWindowedCompiledRowCertificate 1 1 M htb hns

/-- Paper-scale factored compiled row certificate at `(1,1)`. -/
abbrev PaperScalePiPlusBooleanProjectedFactoredCompiledRowCertificateOneOne
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedWindowedFactoredCompiledRowCertificate 1 1
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- Paper-scale factored row-span classifier at `(1,1)`. -/
abbrev PaperScalePiPlusBooleanProjectedFactoredRowSpanClassifierOneOne
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedFactoredRowSpanClassifier 1 1
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- Paper-scale transformed Leibniz generator pullback at `(1,1)`. -/
abbrev PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorPullbackOneOne
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedTransformedLeibnizGeneratorPullback 1 1
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale transformed Leibniz generator row certificate at `(1,1)`. -/
abbrev PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificateOneOne
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificate 1 1
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale transformed Leibniz generator allocation certificate at `(1,1)`. -/
abbrev PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorAllocationCertificateOneOne
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedTransformedLeibnizGeneratorAllocationCertificate 1 1
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Widen a compiled-only raw-pullback membership payload from `(1,0)` to
`(1,1)` by monotonicity of the inclusive source SPDP window. -/
theorem paperScale_windowedCompiledRawPullbackMembershipOneOne_of_OneZero
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpull : PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembershipOneZero
      M htb hns) :
    PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembershipOneOne
      M htb hns := by
  intro S m hSlen hmdeg hmvars hadm
  exact mlBlockedSpdpSubspaceInc_mono_params
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    (le_rfl : Nat.log 2 (2 ^ 804) + 1 ≤ Nat.log 2 (2 ^ 804) + 1)
    (by omega : Nat.log 2 (2 ^ 804) + 0 ≤ Nat.log 2 (2 ^ 804) + 1)
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    (hpull S m hSlen hmdeg hmvars hadm)

/-- Widen a compiled P-subspace inclusion from `(1,0)` to `(1,1)`. -/
theorem paperScale_compiledPSubspaceInclusionOneOne_of_OneZero
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinc : PaperScalePiPlusBooleanProjectedCompiledPSubspaceInclusionOneZero
      M htb hns) :
    PaperScalePiPlusBooleanProjectedCompiledPSubspaceInclusionOneOne
      M htb hns := by
  intro row hrow
  rcases hinc hrow with ⟨pre, hpre, hmap⟩
  refine ⟨pre, ?_, hmap⟩
  exact mlBlockedSpdpSubspaceInc_mono_params
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    (le_rfl : Nat.log 2 (2 ^ 804) + 1 ≤ Nat.log 2 (2 ^ 804) + 1)
    (by omega : Nat.log 2 (2 ^ 804) + 0 ≤ Nat.log 2 (2 ^ 804) + 1)
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hpre

/-- Widen a compiled row certificate from `(1,0)` to `(1,1)`. -/
theorem paperScale_compiledRowCertificateOneOne_of_OneZero
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hrow : PaperScalePiPlusBooleanProjectedCompiledRowCertificateOneZero
      M htb hns) :
    PaperScalePiPlusBooleanProjectedWindowedCompiledRowCertificateOneOne
      M htb hns := by
  intro S m hSlen hmdeg hmvars hadm
  rcases hrow S m hSlen hmdeg hmvars hadm with
    ⟨κ', ℓ', S', m', hκ', hℓ', hSlen', hmdeg', hmvars', hadm', hroweq⟩
  refine ⟨κ', ℓ', S', m', hκ', ?_, hSlen', hmdeg', hmvars', hadm', hroweq⟩
  exact le_trans hℓ' (by omega : Nat.log 2 (2 ^ 804) + 0 ≤ Nat.log 2 (2 ^ 804) + 1)

/-- Widen a factored compiled row certificate from `(1,0)` to `(1,1)`. -/
theorem paperScale_factoredCompiledRowCertificateOneOne_of_OneZero
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hrow : PaperScalePiPlusBooleanProjectedFactoredCompiledRowCertificateOneZero
      M htb hns) :
    PaperScalePiPlusBooleanProjectedFactoredCompiledRowCertificateOneOne
      M htb hns := by
  intro S m hSlen hmdeg hmvars hadm
  rcases hrow S m hSlen hmdeg hmvars hadm with
    ⟨κ', ℓ', S', m', hκ', hℓ', hSlen', hmdeg', hmvars', hadm', hroweq⟩
  refine ⟨κ', ℓ', S', m', hκ', ?_, hSlen', hmdeg', hmvars', hadm', hroweq⟩
  exact le_trans hℓ' (by omega : Nat.log 2 (2 ^ 804) + 0 ≤ Nat.log 2 (2 ^ 804) + 1)

/-- Widen a factored row-span classifier from `(1,0)` to `(1,1)`. -/
theorem paperScale_factoredRowSpanClassifierOneOne_of_OneZero
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hclass : PaperScalePiPlusBooleanProjectedFactoredRowSpanClassifierOneZero
      M htb hns) :
    PaperScalePiPlusBooleanProjectedFactoredRowSpanClassifierOneOne
      M htb hns := by
  intro S m hSlen hmdeg hmvars hadm
  rcases hclass S m hSlen hmdeg hmvars hadm with ⟨G, hspan, hG⟩
  refine ⟨G, hspan, ?_⟩
  intro q hq
  exact mlBlockedSpdpSubspaceInc_mono_params
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    (le_rfl : Nat.log 2 (2 ^ 804) + 1 ≤ Nat.log 2 (2 ^ 804) + 1)
    (by omega : Nat.log 2 (2 ^ 804) + 0 ≤ Nat.log 2 (2 ^ 804) + 1)
    (cookLevinFactoredPoly M (2 ^ 804))
    (hG q hq)

/-- Widen a transformed Leibniz generator pullback from `(1,0)` to `(1,1)`. -/
theorem paperScale_transformedLeibnizGeneratorPullbackOneOne_of_OneZero
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpull : PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorPullbackOneZero
      M htb hns) :
    PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorPullbackOneOne
      M htb hns := by
  intro S m hSlen hmdeg hmvars hadm q hq
  exact mlBlockedSpdpSubspaceInc_mono_params
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    (le_rfl : Nat.log 2 (2 ^ 804) + 1 ≤ Nat.log 2 (2 ^ 804) + 1)
    (by omega : Nat.log 2 (2 ^ 804) + 0 ≤ Nat.log 2 (2 ^ 804) + 1)
    (cookLevinFactoredPoly M (2 ^ 804))
    (hpull S m hSlen hmdeg hmvars hadm q hq)

/-- Widen a transformed Leibniz generator row certificate from `(1,0)` to
`(1,1)`. -/
theorem paperScale_transformedLeibnizGeneratorRowCertificateOneOne_of_OneZero
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcert : PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificateOneZero
      M htb hns) :
    PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificateOneOne
      M htb hns := by
  intro S m hSlen hmdeg hmvars hadm q hq
  rcases hcert S m hSlen hmdeg hmvars hadm q hq with
    ⟨κ', ℓ', S', m', hκ', hℓ', hSlen', hmdeg', hmvars', hadm', hroweq⟩
  refine ⟨κ', ℓ', S', m', hκ', ?_, hSlen', hmdeg', hmvars', hadm', hroweq⟩
  exact le_trans hℓ' (by omega : Nat.log 2 (2 ^ 804) + 0 ≤ Nat.log 2 (2 ^ 804) + 1)

/-- Widen a transformed Leibniz generator allocation certificate from `(1,0)` to
`(1,1)`. -/
theorem paperScale_transformedLeibnizGeneratorAllocationCertificateOneOne_of_OneZero
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcert : PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorAllocationCertificateOneZero
      M htb hns) :
    PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorAllocationCertificateOneOne
      M htb hns := by
  intro S m hSlen hmdeg hmvars hadm alloc halloc_mem
  rcases hcert S m hSlen hmdeg hmvars hadm alloc halloc_mem with
    ⟨κ', ℓ', S', m', hκ', hℓ', hSlen', hmdeg', hmvars', hadm', hroweq⟩
  refine ⟨κ', ℓ', S', m', hκ', ?_, hSlen', hmdeg', hmvars', hadm', hroweq⟩
  exact le_trans hℓ' (by omega : Nat.log 2 (2 ^ 804) + 0 ≤ Nat.log 2 (2 ^ 804) + 1)

/-- A `(1,1)` row certificate still gives the `(1,1)` generator pullback. -/
theorem paperScale_transformedLeibnizGeneratorPullbackOneOne_of_rowCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcert : PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificateOneOne
      M htb hns) :
    PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorPullbackOneOne
      M htb hns :=
  transformedLeibnizGeneratorPullback_of_rowCertificate
    1 1 M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) hcert

/-- A `(1,1)` allocation certificate gives the `(1,1)` row certificate. -/
theorem paperScale_transformedLeibnizGeneratorRowCertificateOneOne_of_allocationCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (halloc : PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorAllocationCertificateOneOne
      M htb hns) :
    PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificateOneOne
      M htb hns :=
  transformedLeibnizGeneratorRowCertificate_of_allocationCertificate
    1 1 M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) halloc

/-- Paper-scale normalized Leibniz row-span plus `(1,1)` generator pullback gives
 the `(1,1)` factored row-span classifier. -/
theorem paperScale_factoredRowSpanClassifierOneOne_of_normalizedTransformedLeibniz
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hnorm : PaperScalePiPlusBooleanProjectedNormalizedTransformedLeibnizRowSpan
      M htb hns)
    (hpull : PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorPullbackOneOne
      M htb hns) :
    PaperScalePiPlusBooleanProjectedFactoredRowSpanClassifierOneOne M htb hns :=
  factoredRowSpanClassifier_of_normalizedTransformedLeibniz
    1 1 M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) hnorm hpull

/-- Paper-scale normalized-derivative polynomial span plus `(1,1)` generator
pullback gives the `(1,1)` factored row-span classifier. -/
theorem paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_generatorPullback
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M htb hns)
    (hpull : PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorPullbackOneOne
      M htb hns) :
    PaperScalePiPlusBooleanProjectedFactoredRowSpanClassifierOneOne M htb hns :=
  paperScale_factoredRowSpanClassifierOneOne_of_normalizedTransformedLeibniz
    M htb hns
    (paperScale_normalizedTransformedLeibnizRowSpan_of_polynomialSpan
      M htb hns hpoly)
    hpull

/-- Paper-scale normalized-derivative polynomial span plus a `(1,1)` row
certificate gives the `(1,1)` factored row-span classifier. -/
theorem paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_generatorRowCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M htb hns)
    (hcert : PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificateOneOne
      M htb hns) :
    PaperScalePiPlusBooleanProjectedFactoredRowSpanClassifierOneOne M htb hns :=
  paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_generatorPullback
    M htb hns hpoly
    (paperScale_transformedLeibnizGeneratorPullbackOneOne_of_rowCertificate
      M htb hns hcert)

/-- Paper-scale normalized-derivative polynomial span plus a `(1,1)` allocation
certificate gives the `(1,1)` factored row-span classifier. -/
theorem paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_allocationCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M htb hns)
    (halloc : PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorAllocationCertificateOneOne
      M htb hns) :
    PaperScalePiPlusBooleanProjectedFactoredRowSpanClassifierOneOne M htb hns :=
  paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_generatorRowCertificate
    M htb hns hpoly
    (paperScale_transformedLeibnizGeneratorRowCertificateOneOne_of_allocationCertificate
      M htb hns halloc)

/-! ## Axiom audit anchors -/

#print axioms paperScale_windowedCompiledRawPullbackMembershipOneOne_of_OneZero
#print axioms paperScale_compiledPSubspaceInclusionOneOne_of_OneZero
#print axioms paperScale_compiledRowCertificateOneOne_of_OneZero
#print axioms paperScale_factoredCompiledRowCertificateOneOne_of_OneZero
#print axioms paperScale_factoredRowSpanClassifierOneOne_of_OneZero
#print axioms paperScale_transformedLeibnizGeneratorPullbackOneOne_of_OneZero
#print axioms paperScale_transformedLeibnizGeneratorRowCertificateOneOne_of_OneZero
#print axioms paperScale_transformedLeibnizGeneratorAllocationCertificateOneOne_of_OneZero
#print axioms paperScale_transformedLeibnizGeneratorPullbackOneOne_of_rowCertificate
#print axioms paperScale_transformedLeibnizGeneratorRowCertificateOneOne_of_allocationCertificate
#print axioms paperScale_factoredRowSpanClassifierOneOne_of_normalizedTransformedLeibniz
#print axioms paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_generatorPullback
#print axioms paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_generatorRowCertificate
#print axioms paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_allocationCertificate

end PallLean.Paper93.DeepMath.PathC
