import PallLean.Paper93.DeepMath.PathC.PiPlusGeneratorPullbackCertificate

/-!
# Allocation-level transformed generator certificates

`distribDerivProds` hides each Leibniz generator behind set membership.  This
file opens that set back up: a generator is a concrete product indexed by a
derivative-allocation function `h : factor → List vars`.

The new certificate is the exact local transport theorem still needed for the
P-side generator pullback, but stated without the opaque `q ∈ distribDerivProds`
wrapper.
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

/-- Allocation-level version of the transformed Leibniz generator row
certificate.  For every way of distributing the derivative list `S` across the
transformed local factors, the corresponding concrete product has an inverse
`Pi+` pullback represented by an enlarged source SPDP row. -/
def PiPlusBooleanProjectedTransformedLeibnizGeneratorAllocationCertificate
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop :=
  ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : SATDeciderGaugeSpace M n hn2 htb hns),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
      ∀ (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
            M n hn2 htb hns D).length →
          List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)),
        (∀ i, ∀ v ∈ alloc i, v ∈ S) →
        ∃ (κ' ℓ' : Nat)
          (S' : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
          (m' : SATDeciderGaugeSpace M n hn2 htb hns),
          κ' ≤ Nat.log 2 n + extraK ∧
            ℓ' ≤ Nat.log 2 n + extraL ∧
              S'.length = κ' ∧
                m'.totalDegree ≤ ℓ' ∧
                  m'.vars ⊆ S'.toFinset ∧
                    isBlockAdmissible
                      (cook_levin_compilation M n hn2 htb hns).partition S' ∧
                      (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D).equiv.symm
                        (mlProj (m *
                          Finset.univ.prod (fun i : Fin
                            (piPlusBooleanProjectedTransformedConstraintFactors
                              M n hn2 htb hns D).length =>
                              iterDerivList (alloc i)
                                ((piPlusBooleanProjectedTransformedConstraintFactors
                                  M n hn2 htb hns D)[i.val])))) =
                        mlProj (m' * iterDerivList S'
                          (cookLevinFactoredPoly M n))

/-- Allocation-level certificates imply the previous set-membership generator
row certificate by unpacking `q ∈ distribDerivProds`. -/
theorem transformedLeibnizGeneratorRowCertificate_of_allocationCertificate
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (halloc : PiPlusBooleanProjectedTransformedLeibnizGeneratorAllocationCertificate
      extraK extraL M n hn2 htb hns D) :
    PiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificate
      extraK extraL M n hn2 htb hns D := by
  intro S m hSlen hmdeg hmvars hadm q hq
  rcases hq with ⟨alloc, halloc_mem, rfl⟩
  exact halloc S m hSlen hmdeg hmvars hadm alloc halloc_mem

/-- Allocation-level certificates imply the transformed-generator pullback
payload directly. -/
theorem transformedLeibnizGeneratorPullback_of_allocationCertificate
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (halloc : PiPlusBooleanProjectedTransformedLeibnizGeneratorAllocationCertificate
      extraK extraL M n hn2 htb hns D) :
    PiPlusBooleanProjectedTransformedLeibnizGeneratorPullback
      extraK extraL M n hn2 htb hns D :=
  transformedLeibnizGeneratorPullback_of_rowCertificate
    extraK extraL M n hn2 htb hns D
    (transformedLeibnizGeneratorRowCertificate_of_allocationCertificate
      extraK extraL M n hn2 htb hns D halloc)

/-- Paper-scale allocation certificate for the one-extra-derivative,
zero-extra-multiplier source window. -/
abbrev PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorAllocationCertificateOneZero
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedTransformedLeibnizGeneratorAllocationCertificate 1 0
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale row certificate from the allocation-level certificate. -/
theorem paperScale_transformedLeibnizGeneratorRowCertificateOneZero_of_allocationCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (halloc : PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorAllocationCertificateOneZero
      M htb hns) :
    PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificateOneZero
      M htb hns :=
  transformedLeibnizGeneratorRowCertificate_of_allocationCertificate
    1 0 M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) halloc

/-- Paper-scale P-side classifier from polynomial normalization plus allocation
transport of transformed generators. -/
theorem paperScale_factoredRowSpanClassifierOneZero_of_polynomialSpan_and_allocationCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M htb hns)
    (halloc : PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorAllocationCertificateOneZero
      M htb hns) :
    PaperScalePiPlusBooleanProjectedFactoredRowSpanClassifierOneZero M htb hns :=
  paperScale_factoredRowSpanClassifierOneZero_of_polynomialSpan_and_generatorRowCertificate
    M htb hns hpoly
    (paperScale_transformedLeibnizGeneratorRowCertificateOneZero_of_allocationCertificate
      M htb hns halloc)

/-! ## Axiom audit anchors -/

#print axioms transformedLeibnizGeneratorRowCertificate_of_allocationCertificate
#print axioms transformedLeibnizGeneratorPullback_of_allocationCertificate
#print axioms paperScale_transformedLeibnizGeneratorRowCertificateOneZero_of_allocationCertificate
#print axioms paperScale_factoredRowSpanClassifierOneZero_of_polynomialSpan_and_allocationCertificate

end PallLean.Paper93.DeepMath.PathC
