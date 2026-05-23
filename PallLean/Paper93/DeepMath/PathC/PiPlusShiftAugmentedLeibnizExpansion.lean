import PallLean.Paper93.DeepMath.PathC.PiPlusShiftAugmentedComposition

/-!
# Leibniz-distribution route to the shift-augmented generator expansion

`boundedProfileClassifiedSet` hides each generator behind an existential Leibniz
distribution `d`.  This file opens that existential and proves the precise
composition lemma needed next: it is enough to provide, for every concrete
Leibniz distribution `d`, a same-profile shift-augmented slot expansion of the
actual projected row.

This is intentionally the honest remaining boundary.  The theorem below does
not assert that arbitrary `project (mlProj (shift * ∏ᵢ ∂^{dᵢ} fᵢ))` decomposes
for free; it reduces `CookLevinShiftAugmentedGeneratorExpansion_paperScale` to
that explicit distributed-factor expansion obligation.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open SymmetricPowerBound
open WithinProfileBound
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- The concrete Leibniz product associated to one derivative distribution. -/
noncomputable def leibnizDistributionProduct {N L : Nat}
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (d : Fin L → List (Fin N)) : MvPolynomial (Fin N) ℚ :=
  Finset.univ.prod (fun i : Fin L => iterDerivList (d i) (factors i))

/-- Distribution-level shift-augmented expansion obligation.  A caller supplies
this for the exact Leibniz distribution `d` that witnesses membership in
`boundedProfileClassifiedSet`. -/
def DistributedShiftAugmentedSlotExpansion {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ)
    (classifier : ProjectedPostRowProfileClassifier κ factors constraintType)
    (h : ProfileHistogram) (S : List (Fin N))
    (shift : MvPolynomial (Fin N) ℚ)
    (d : Fin L → List (Fin N)) : Prop :=
  (∀ i, ∀ v ∈ d i, v ∈ S) →
  derivCountProfile constraintType d = h →
  (∑ i : Fin L, (d i).length) ≤ S.length →
    ShiftAugmentedProfileSlotExpansion B κ ℓ
      (classifier.profile h S shift (leibnizDistributionProduct factors d))
      (project (mlProj (shift * leibnizDistributionProduct factors d)))

/-- Generic generator expansion from distributed Leibniz expansions.  This is
exactly the existential-opening step for `boundedProfileClassifiedSet`. -/
theorem shiftAugmentedGeneratorExpansion_of_distributedLeibnizExpansions
    {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ)
    (classifier : ProjectedPostRowProfileClassifier κ factors constraintType)
    (hdist : ∀ (h : ProfileHistogram) (S : List (Fin N))
      (shift : MvPolynomial (Fin N) ℚ) (d : Fin L → List (Fin N)),
        DistributedShiftAugmentedSlotExpansion
          B κ ℓ factors constraintType project classifier h S shift d) :
    ∀ (h : ProfileHistogram)
      (S : List (Fin N)) (_hS : S.length ≤ κ)
      (shift : MvPolynomial (Fin N) ℚ) (_hshift : shift.vars ⊆ S.toFinset)
      (g : MvPolynomial (Fin N) ℚ),
        g ∈ boundedProfileClassifiedSet factors constraintType S h →
          ShiftAugmentedProfileSlotExpansion B κ ℓ
            (classifier.profile h S shift g)
            (project (mlProj (shift * g))) := by
  intro h S _hS shift _hshift g hg
  rcases hg with ⟨d, hd_elts, hg_eq, hprofile, hlen⟩
  subst g
  exact hdist h S shift d hd_elts hprofile hlen

/-- Paper-scale Cook--Levin abbreviation for the distribution-level expansion
obligation. -/
def CookLevinDistributedShiftAugmentedSlotExpansion_paperScale
    (M : TuringMachine.DTM) (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ 2 ^ 804) (κ ℓ : Nat)
    (project : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns →ₗ[ℚ]
      SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns)
    (classifier : CookLevinProjectedPostRowProfileClassifier_paperScale
      M htb hns κ) : Prop :=
  ∀ (h : ProfileHistogram)
    (S : List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
    (shift : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns)
    (d : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length →
      List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars)),
      DistributedShiftAugmentedSlotExpansion
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
        κ ℓ
        (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
            M htb hns).length =>
          (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
            M htb hns)[i.val])
        (cookLevinFactorConstraintType_paperScale M htb hns)
        project classifier h S shift d

/-- Discharge the paper-scale `CookLevinShiftAugmentedGeneratorExpansion` socket
from the explicit Leibniz-distribution expansion obligation. -/
theorem cookLevinShiftAugmentedGeneratorExpansion_paperScale_of_distributedLeibnizExpansions
    (M : TuringMachine.DTM) (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ 2 ^ 804) (κ ℓ : Nat)
    (project : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns →ₗ[ℚ]
      SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns)
    (classifier : CookLevinProjectedPostRowProfileClassifier_paperScale
      M htb hns κ)
    (hdist : CookLevinDistributedShiftAugmentedSlotExpansion_paperScale
      M htb hns κ ℓ project classifier) :
    CookLevinShiftAugmentedGeneratorExpansion_paperScale
      M htb hns κ ℓ project classifier := by
  intro h S hS shift hshift g hg
  exact shiftAugmentedGeneratorExpansion_of_distributedLeibnizExpansions
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ
    (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length =>
      (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns)[i.val])
    (cookLevinFactorConstraintType_paperScale M htb hns)
    project classifier
    hdist h S hS shift hshift g hg

/-- The same distributed-Leibniz expansion obligation gives the arity-5
within-profile finrank closeout immediately. -/
theorem cookLevinShiftAugmentedProjectedWithinProfileFinrank_paperScale_of_distributedLeibnizExpansions
    (M : TuringMachine.DTM) (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ 2 ^ 804) (κ ℓ : Nat)
    (project : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns →ₗ[ℚ]
      SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns)
    (classifier : CookLevinProjectedPostRowProfileClassifier_paperScale
      M htb hns κ)
    (hdist : CookLevinDistributedShiftAugmentedSlotExpansion_paperScale
      M htb hns κ ℓ project classifier) :
    ShiftAugmentedNaturallyProfiledProjectedWithinProfileFinrankClaim
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      κ ℓ
      (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
          M htb hns).length =>
        (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
          M htb hns)[i.val])
      (cookLevinFactorConstraintType_paperScale M htb hns)
      project classifier :=
  cookLevinShiftAugmentedProjectedWithinProfileFinrank_paperScale_of_expansion
    M htb hns κ ℓ project classifier
    (cookLevinShiftAugmentedGeneratorExpansion_paperScale_of_distributedLeibnizExpansions
      M htb hns κ ℓ project classifier hdist)

/-! ## Axiom audit anchors -/

#print axioms shiftAugmentedGeneratorExpansion_of_distributedLeibnizExpansions
#print axioms cookLevinShiftAugmentedGeneratorExpansion_paperScale_of_distributedLeibnizExpansions
#print axioms cookLevinShiftAugmentedProjectedWithinProfileFinrank_paperScale_of_distributedLeibnizExpansions

end PallLean.Paper93.DeepMath.PathC
