import PallLean.Paper93.DeepMath.PathC.PiPlusNormalizedDerivativeSpanReduction

/-!
# Row-certificate form of transformed Leibniz generator pullback

The transformed-generator pullback payload says every projected distributed
Leibniz generator pulls back into the enlarged source SPDP window.  This file
reduces that submodule-membership obligation to the concrete row-certificate
form: for each transformed generator, exhibit an actual source derivative list
and multiplier whose SPDP row is exactly the raw pullback.

This is closer to the local Cook--Levin algebra: once each transformed local
factor/product generator is identified with a source row, membership in
`mlBlockedSpdpSubspaceInc` is immediate by `Submodule.subset_span`.
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

/-- Row-certificate version of transformed Leibniz generator pullback.  For each
projected distributed derivative generator, give the concrete source SPDP row
that equals its inverse-`Pi+` pullback. -/
def PiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificate
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
      ∀ q ∈ distribDerivProds Finset.univ
              (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
                  M n hn2 htb hns D).length =>
                (piPlusBooleanProjectedTransformedConstraintFactors
                  M n hn2 htb hns D)[i.val]) S,
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
                        (mlProj (m * q)) =
                        mlProj (m' * iterDerivList S'
                          (cookLevinFactoredPoly M n))

/-- A row certificate immediately gives the transformed-generator pullback
payload, by inserting the exhibited row as a generator of the inclusive source
SPDP subspace. -/
theorem transformedLeibnizGeneratorPullback_of_rowCertificate
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (hcert : PiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificate
      extraK extraL M n hn2 htb hns D) :
    PiPlusBooleanProjectedTransformedLeibnizGeneratorPullback
      extraK extraL M n hn2 htb hns D := by
  intro S m hSlen hmdeg hmvars hadm q hq
  rcases hcert S m hSlen hmdeg hmvars hadm q hq with
    ⟨κ', ℓ', S', m', hκ', hℓ', hSlen', hmdeg', hmvars', hadm', hrow⟩
  rw [hrow]
  exact Submodule.subset_span
    ⟨S', m', by rwa [hSlen'], le_trans hmdeg' hℓ', hmvars', hadm', rfl⟩

/-- Paper-scale row-certificate version for the one-extra-derivative,
zero-extra-multiplier source window. -/
abbrev PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificateOneZero
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificate 1 0
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale transformed-generator pullback from row certificates. -/
theorem paperScale_transformedLeibnizGeneratorPullbackOneZero_of_rowCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcert : PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificateOneZero
      M htb hns) :
    PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorPullbackOneZero
      M htb hns :=
  transformedLeibnizGeneratorPullback_of_rowCertificate
    1 0 M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) hcert

/-- Paper-scale P-side classifier from the two sharpest current payloads:
polynomial-level normalized derivative span and transformed-generator row
certificates. -/
theorem paperScale_factoredRowSpanClassifierOneZero_of_polynomialSpan_and_generatorRowCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M htb hns)
    (hcert : PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificateOneZero
      M htb hns) :
    PaperScalePiPlusBooleanProjectedFactoredRowSpanClassifierOneZero M htb hns :=
  paperScale_factoredRowSpanClassifierOneZero_of_polynomialSpan_and_generatorPullback
    M htb hns hpoly
    (paperScale_transformedLeibnizGeneratorPullbackOneZero_of_rowCertificate
      M htb hns hcert)

/-! ## Axiom audit anchors -/

#print axioms transformedLeibnizGeneratorPullback_of_rowCertificate
#print axioms paperScale_transformedLeibnizGeneratorPullbackOneZero_of_rowCertificate
#print axioms paperScale_factoredRowSpanClassifierOneZero_of_polynomialSpan_and_generatorRowCertificate

end PallLean.Paper93.DeepMath.PathC
