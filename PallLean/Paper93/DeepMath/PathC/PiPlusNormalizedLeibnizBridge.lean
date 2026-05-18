import PallLean.Paper93.DeepMath.PathC.PiPlusTransformedConstraintLeibniz

/-!
# Bridge from Boolean-normalized transformed products to the P-side classifier

`PiPlusTransformedConstraintLeibniz` gives the ordinary Leibniz surface for the
product of transformed local Cook--Levin constraint factors.  The next real
mathematical obstruction is that the actual target is the Boolean normal form of
that product.

This file packages the obstruction in the exact form needed downstream:

* a normalized-row span property saying every derivative row of
  `zeroProfileBooleanNormalize L.prod` lies in the span of the transformed
  Leibniz row generators;
* a generator pullback property saying those generators pull back into the
  enlarged source SPDP window;
* a theorem that these two concrete facts imply the factored Route-C row-span
  classifier, hence the existing P-side closeout path can consume them.
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

/-- The factored Cook--Levin target under the concrete Boolean-projected `Pi+`
is the Boolean normal form of the product of transformed local constraint
factors.  This rewrites through the already-proved equality
`compiledPoly = cookLevinFactoredPoly`. -/
theorem piPlusBooleanProjectedGauge_of_blockCoordinates_factored_eq_normalized_transformedConstraints
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) :
    piPlusBooleanProjectedGauge M n hn2 htb hns
        (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D)
        (cookLevinFactoredPoly M n) =
      zeroProfileBooleanNormalize
        (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D).prod := by
  have h := piPlusBooleanProjectedGauge_of_blockCoordinates_compiledPoly_constraints
    M n hn2 htb hns D
  simpa [compiledPoly_eq_cookLevinFactoredPoly M n hn2 htb hns,
    piPlusBooleanProjectedTransformedConstraintFactors] using h

/-- Paper-scale form of the previous rewrite. -/
theorem cookLevinPiPlusBooleanProjectedGauge_paperScale_factored_eq_normalized_transformedConstraints
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns
        (cookLevinFactoredPoly M (2 ^ 804)) =
      zeroProfileBooleanNormalize
        (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
          M htb hns).prod := by
  exact piPlusBooleanProjectedGauge_of_blockCoordinates_factored_eq_normalized_transformedConstraints
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Concrete normalized Leibniz row-span property.  This is the precise
normalization seam left by the P-side assembly: derivative rows of the Boolean
normal form of the transformed local-factor product must be spanned by the
ordinary distributed-derivative rows of the unnormalized transformed product. -/
def PiPlusBooleanProjectedNormalizedTransformedLeibnizRowSpan
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop :=
  ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : SATDeciderGaugeSpace M n hn2 htb hns),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
      mlProj (m * iterDerivList S
        (zeroProfileBooleanNormalize
          (piPlusBooleanProjectedTransformedConstraintFactors
            M n hn2 htb hns D).prod)) ∈
        Submodule.span ℚ
          ((fun q => mlProj (m * q)) ''
            distribDerivProds Finset.univ
              (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
                  M n hn2 htb hns D).length =>
                (piPlusBooleanProjectedTransformedConstraintFactors
                  M n hn2 htb hns D)[i.val]) S)

/-- Pullback condition for every transformed Leibniz generator.  This is the
local-factor classification/pullback half of the remaining P-side assembly. -/
def PiPlusBooleanProjectedTransformedLeibnizGeneratorPullback
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
        (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D).equiv.symm
          (mlProj (m * q)) ∈
          mlBlockedSpdpSubspaceInc
            (cook_levin_compilation M n hn2 htb hns).partition
            (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
            (cookLevinFactoredPoly M n)

/-- The normalized-row span property plus generator pullback property imply the
factored row-span classifier.  This is the bridge that lets the remaining
Boolean-normalization and local-factor classifications close the P-side socket
without inventing any new endpoint plumbing. -/
theorem factoredRowSpanClassifier_of_normalizedTransformedLeibniz
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (hnorm : PiPlusBooleanProjectedNormalizedTransformedLeibnizRowSpan
      M n hn2 htb hns D)
    (hpull : PiPlusBooleanProjectedTransformedLeibnizGeneratorPullback
      extraK extraL M n hn2 htb hns D) :
    PiPlusBooleanProjectedFactoredRowSpanClassifier
      extraK extraL M n hn2 htb hns
      (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D) := by
  intro S m hSlen hmdeg hmvars hadm
  let G : Set (SATDeciderGaugeSpace M n hn2 htb hns) :=
    (fun q => mlProj (m * q)) ''
      distribDerivProds Finset.univ
        (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
            M n hn2 htb hns D).length =>
          (piPlusBooleanProjectedTransformedConstraintFactors
            M n hn2 htb hns D)[i.val]) S
  refine ⟨G, ?_, ?_⟩
  · rw [piPlusBooleanProjectedGauge_of_blockCoordinates_factored_eq_normalized_transformedConstraints]
    exact hnorm S m hSlen hmdeg hmvars hadm
  · intro row hrow
    rcases hrow with ⟨q, hq, rfl⟩
    exact hpull S m hSlen hmdeg hmvars hadm q hq

/-- Paper-scale normalized Leibniz row-span property. -/
abbrev PaperScalePiPlusBooleanProjectedNormalizedTransformedLeibnizRowSpan
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedNormalizedTransformedLeibnizRowSpan
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale transformed Leibniz generator-pullback property for the one-zero
P-side window. -/
abbrev PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorPullbackOneZero
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedTransformedLeibnizGeneratorPullback 1 0
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale closeout from the two concrete transformed-Leibniz payloads to
the existing P-side row-span classifier. -/
theorem paperScale_factoredRowSpanClassifierOneZero_of_normalizedTransformedLeibniz
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hnorm : PaperScalePiPlusBooleanProjectedNormalizedTransformedLeibnizRowSpan
      M htb hns)
    (hpull : PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorPullbackOneZero
      M htb hns) :
    PaperScalePiPlusBooleanProjectedFactoredRowSpanClassifierOneZero M htb hns :=
  factoredRowSpanClassifier_of_normalizedTransformedLeibniz
    1 0 M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) hnorm hpull

/-! ## Axiom audit anchors -/

#print axioms piPlusBooleanProjectedGauge_of_blockCoordinates_factored_eq_normalized_transformedConstraints
#print axioms cookLevinPiPlusBooleanProjectedGauge_paperScale_factored_eq_normalized_transformedConstraints
#print axioms factoredRowSpanClassifier_of_normalizedTransformedLeibniz
#print axioms paperScale_factoredRowSpanClassifierOneZero_of_normalizedTransformedLeibniz

end PallLean.Paper93.DeepMath.PathC
