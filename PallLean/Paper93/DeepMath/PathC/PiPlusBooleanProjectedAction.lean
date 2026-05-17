import PallLean.Paper93.DeepMath.PathC.PiPlusMLProjectionObstruction
import PallLean.Paper93.DeepMath.PathB.ZeroProfileNormalFormInstantiationProgress

/-!
# Boolean-projected Pi+ action

The raw Hadamard `Pi+` is an algebra equivalence on the polynomial ring, but it
can create quadratic leakage such as `X₀X₁ ↦ X₀² - X₁²`.  The multilinear
projection `mlProj` drops that leakage, which is too severe for quotient-level
Boolean algebra.

This file defines the corrected projected action using the Boolean quotient
normalizer from Route B:

`Pi+ᵦ(p) := booleanNormalize(Pi+(p))`,

where `booleanNormalize` implements `X_i^k = X_i` for positive powers.  This is
not claimed to be a linear equivalence; it is the projected/quotient action that
Route C must use for generator transport after the obstruction was exposed.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- Boolean-projected `Pi+` action associated to any SAT-scale `Pi+` transform.
This is the linear map `booleanNormalize ∘ Pi+`. -/
noncomputable def piPlusBooleanProjectedGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) :
    SATDeciderGaugeSpace M n hn2 htb hns →ₗ[ℚ]
      SATDeciderGaugeSpace M n hn2 htb hns :=
  (zeroProfileBooleanNormalizeLinearMap
      (n := (cook_levin_compilation M n hn2 htb hns).numVars)).comp piP.gauge

/-- The Boolean-projected `Pi+` action fixes constants whenever raw `Pi+` does. -/
theorem piPlusBooleanProjectedGauge_one
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hone : PiPlusUnitPreserving M n hn2 htb hns piP) :
    piPlusBooleanProjectedGauge M n hn2 htb hns piP
      (1 : SATDeciderGaugeSpace M n hn2 htb hns) = 1 := by
  unfold piPlusBooleanProjectedGauge
  change zeroProfileBooleanNormalize (piP.gauge (1 : SATDeciderGaugeSpace M n hn2 htb hns)) = 1
  rw [hone]
  simp

/-- Concrete paper-scale Boolean-projected `Pi+` action. -/
noncomputable def cookLevinPiPlusBooleanProjectedGauge_paperScale
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns →ₗ[ℚ]
      SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns :=
  piPlusBooleanProjectedGauge M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- The concrete paper-scale Boolean-projected `Pi+` action fixes `1`. -/
theorem cookLevinPiPlusBooleanProjectedGauge_paperScale_one
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns
      (1 : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns) = 1 :=
  piPlusBooleanProjectedGauge_one M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (cookLevinPiPlusSATTransform_paperScale_unitPreserving M htb hns)

/-- Local Boolean quotient repair: after Boolean normalization, the Hadamard
image of `X₀X₁` is `X₀ - X₁`, not zero. -/
theorem zeroProfileBooleanNormalize_piPlusHadamard2Gauge_mul_pair :
    zeroProfileBooleanNormalize
      (piPlusHadamard2Gauge ((X 0) * (X 1) : MvPolynomial (Fin 2) ℚ)) =
      (X 0 - X 1 : MvPolynomial (Fin 2) ℚ) := by
  rw [piPlusHadamard2Gauge_mul_pair_leakage]
  have hsub : (X 0 ^ 2 - X 1 ^ 2 : MvPolynomial (Fin 2) ℚ) =
      X 0 * X 0 - X 1 * X 1 := by
    ring
  rw [hsub, zeroProfileBooleanNormalize_sub]
  rw [zeroProfileBooleanNormalize_X_mul_X, zeroProfileBooleanNormalize_X_mul_X]

/-- The Boolean-projected local `Pi+` differs from raw `mlProj ∘ Pi+` on the
same leakage example: Boolean quotient keeps the linear representative. -/
theorem booleanProjected_vs_mlProj_local_leakage :
    zeroProfileBooleanNormalize
      (piPlusHadamard2Gauge ((X 0) * (X 1) : MvPolynomial (Fin 2) ℚ)) =
      (X 0 - X 1 : MvPolynomial (Fin 2) ℚ) ∧
    mlProj (piPlusHadamard2Gauge
      ((X 0) * (X 1) : MvPolynomial (Fin 2) ℚ)) = 0 :=
  ⟨zeroProfileBooleanNormalize_piPlusHadamard2Gauge_mul_pair,
    mlProj_piPlusHadamard2Gauge_mul_pair_leakage⟩

/-! ## Projected transport surface -/

/-- Forward generator transport for the Boolean-projected `Pi+` action.  This is
now the corrected Route-C generator target: transport via
`booleanNormalize ∘ Pi+`, not raw `Pi+` and not `mlProj ∘ Pi+`. -/
def PiPlusBooleanProjectedForwardGeneratorTransport
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  ∀ (κ ℓ : Nat) (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : SATDeciderGaugeSpace M n hn2 htb hns),
      S.length = κ →
      m.totalDegree ≤ ℓ →
      m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
      piPlusBooleanProjectedGauge M n hn2 htb hns piP
          (mlProj (m * SPDP.iterDerivList S p)) ∈
        mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition κ ℓ
          (piPlusBooleanProjectedGauge M n hn2 htb hns piP p)

/-- Paper-scale Boolean-projected generator transport target. -/
abbrev PaperScalePiPlusBooleanProjectedForwardGeneratorTransport
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedForwardGeneratorTransport M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-! ## Axiom audit anchors -/

#print axioms piPlusBooleanProjectedGauge_one
#print axioms cookLevinPiPlusBooleanProjectedGauge_paperScale_one
#print axioms zeroProfileBooleanNormalize_piPlusHadamard2Gauge_mul_pair
#print axioms booleanProjected_vs_mlProj_local_leakage

end PallLean.Paper93.DeepMath.PathC
