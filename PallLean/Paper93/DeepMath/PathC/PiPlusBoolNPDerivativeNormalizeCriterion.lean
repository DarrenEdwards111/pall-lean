import PallLean.Paper93.DeepMath.PathC.PiPlusBoolNPImageExactCriterion

/-!
# Derivative-normalization criterion for Boolean NP image exactness

The paper Boolean ambient uses the normal representative of `compiledPoly`.
Image exactness for the raw Cook--Levin NP source rows follows if taking SPDP
rows after Boolean-normalizing the compiled polynomial gives the same Boolean
row as normalizing the corresponding raw row.
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

namespace BoolPoly

/-- Row-wise derivative-normalization compatibility between a raw polynomial `q`
and its Boolean representative `p`.  This is the local algebraic content needed
for image exactness. -/
def RawToBoolDerivativeNormalizationRows {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (q : MvPolynomial (Fin n) ℚ) (p : BoolPoly n) : Prop :=
  ∀ (S : List (Fin n)) (m : MvPolynomial (Fin n) ℚ),
    S.length = κ → m.totalDegree ≤ ℓ → m.vars ⊆ S.toFinset →
    isBlockAdmissible B S →
      liftToBool (m * iterDerivList S q) =
        liftToBool (m * iterDerivList S (p : MvPolynomial (Fin n) ℚ))

/-- Derivative-normalization compatibility gives the forward image-generator
criterion. -/
theorem rawToBool_image_forward_of_derivativeNormalizationRows {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (q : MvPolynomial (Fin n) ℚ) (p : BoolPoly n)
    (hrows : RawToBoolDerivativeNormalizationRows B κ ℓ q p) :
    RawToBoolImageForwardGenerators B κ ℓ q p := by
  intro S m hlen hdeg hvars hadm
  rw [hrows S m hlen hdeg hvars hadm]
  exact Submodule.subset_span ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩

/-- Derivative-normalization compatibility gives the reverse image-generator
criterion. -/
theorem rawToBool_image_reverse_of_derivativeNormalizationRows {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (q : MvPolynomial (Fin n) ℚ) (p : BoolPoly n)
    (hrows : RawToBoolDerivativeNormalizationRows B κ ℓ q p) :
    RawToBoolImageReverseGenerators B κ ℓ q p := by
  intro S m hlen hdeg hvars hadm
  rw [← hrows S m hlen hdeg hvars hadm]
  refine Submodule.mem_map_of_mem ?_
  exact Submodule.subset_span ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩

/-- Derivative-normalization compatibility gives exact image equality. -/
theorem rawToBool_image_exact_of_derivativeNormalizationRows {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (q : MvPolynomial (Fin n) ℚ) (p : BoolPoly n)
    (hrows : RawToBoolDerivativeNormalizationRows B κ ℓ q p) :
    Submodule.map (liftToBoolLinearMap n) (rawBlockedSpdpSubspace B κ ℓ q) =
      boolBlockedSpdpSubspace B κ ℓ p :=
  rawToBool_image_exact_of_generators B κ ℓ q p
    (rawToBool_image_forward_of_derivativeNormalizationRows B κ ℓ q p hrows)
    (rawToBool_image_reverse_of_derivativeNormalizationRows B κ ℓ q p hrows)

/-- Paper-scale derivative-normalization row compatibility for the Cook-Levin
NP source window. -/
def PaperScaleCookLevinRawToBoolSourceNPDerivativeNormalizationRows
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  RawToBoolDerivativeNormalizationRows
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    (paperScaleCompiledBoolPoly M htb hns)

/-- Paper-scale derivative-normalization rows imply both generator image criteria. -/
theorem paperScaleCookLevinRawToBoolSourceNPImageGenerators_of_derivativeNormalizationRows
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hrows : PaperScaleCookLevinRawToBoolSourceNPDerivativeNormalizationRows M htb hns) :
    PaperScaleCookLevinRawToBoolSourceNPImageForwardGenerators M htb hns ∧
      PaperScaleCookLevinRawToBoolSourceNPImageReverseGenerators M htb hns := by
  unfold PaperScaleCookLevinRawToBoolSourceNPDerivativeNormalizationRows
    PaperScaleCookLevinRawToBoolSourceNPImageForwardGenerators
    PaperScaleCookLevinRawToBoolSourceNPImageReverseGenerators at *
  exact ⟨
    rawToBool_image_forward_of_derivativeNormalizationRows
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
      (paperScaleCompiledBoolPoly M htb hns) hrows,
    rawToBool_image_reverse_of_derivativeNormalizationRows
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
      (paperScaleCompiledBoolPoly M htb hns) hrows⟩

/-- Paper-scale derivative-normalization rows imply the image-exactness field. -/
theorem paperScaleCookLevinRawToBoolSourceNPImageExact_of_derivativeNormalizationRows
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hrows : PaperScaleCookLevinRawToBoolSourceNPDerivativeNormalizationRows M htb hns) :
    PaperScaleCookLevinRawToBoolSourceNPImageExact M htb hns := by
  rcases paperScaleCookLevinRawToBoolSourceNPImageGenerators_of_derivativeNormalizationRows
      M htb hns hrows with ⟨hfwd, hrev⟩
  exact paperScaleCookLevinRawToBoolSourceNPImageExact_of_generators
    M htb hns hfwd hrev

/-- Final no-decider surface with image exactness reduced to the single
row-wise derivative-normalization obligation. -/
theorem no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPDerivativeRowsKernelFromDecider
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HrowInc : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRowPreservationInc M htb hns)
    (Hrow : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRowPreservation M htb hns)
    (HP : DecidesSAT M → PaperScaleCookLevinLegacyBlockedIncPSideRankBoundOneZero M htb hns)
    (Hderiv : DecidesSAT M → PaperScaleCookLevinRawToBoolSourceNPDerivativeNormalizationRows M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinRawToBoolSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M := by
  apply no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPKernelDisjointFromDecider
    M htb hns HrowInc Hrow HP
  · intro hdec
    exact paperScaleCookLevinRawToBoolSourceNPImageExact_of_derivativeNormalizationRows
      M htb hns (Hderiv hdec)
  · exact Hker

/-! ## Axiom audit anchors -/

#print axioms rawToBool_image_forward_of_derivativeNormalizationRows
#print axioms rawToBool_image_reverse_of_derivativeNormalizationRows
#print axioms rawToBool_image_exact_of_derivativeNormalizationRows
#print axioms paperScaleCookLevinRawToBoolSourceNPImageExact_of_derivativeNormalizationRows
#print axioms no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPDerivativeRowsKernelFromDecider

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
