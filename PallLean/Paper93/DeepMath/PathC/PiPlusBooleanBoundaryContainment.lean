import PallLean.Paper93.DeepMath.PathC.PiPlusBoundaryProject
import PallLean.Paper93.DeepMath.PathC.PiPlusCompiledCoordinateTransport

/-!
# Route W: Boolean-boundary profile containment seam

This file keeps the Route-W project at the coefficient level.  The projection is
Boolean normal-form reduction (`zeroProfileBooleanNormalize`), while `Π+` remains
transport and `can(·)` remains an upstream window-index normalisation.

The theorems here reduce `ProjectedPostSpanProfileContainment` to the exact
coefficient-level generator statement needed next: every Boolean-normalized
post-row generator of a fixed profile lies in the compiled-basis profile
subspace.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open SymmetricPowerBound
open WithinProfileBound
open PallLean.Paper93
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- Generator-level form of Route-W profile containment.  Since
`projectedAllBoundedProfilePostSpan` is a span of projected generators, it is
enough to prove each projected generator lies in the appropriate Lemma-31
profile subspace. -/
def ProjectedPostSpanGeneratorContainment {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ) : Prop :=
  ∀ (h : ProfileHistogram), ProfileAdmissible κ h →
    ∀ (S : List (Fin N)), S.length ≤ κ →
    ∀ (shift : MvPolynomial (Fin N) ℚ), shift.vars ⊆ S.toFinset →
    ∀ (g : MvPolynomial (Fin N) ℚ),
      g ∈ boundedProfileClassifiedSet factors constraintType S h →
        project (mlProj (shift * g)) ∈
          profileSubspace h
            (fun σ : ConstraintType => interfaceSpace_compiledBasis B κ ℓ σ)

/-- Span closeout: generator-level containment implies the Route-W
`ProjectedPostSpanProfileContainment` socket. -/
theorem projectedPostSpanProfileContainment_of_generatorContainment {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ)
    (hgen : ProjectedPostSpanGeneratorContainment
      B κ ℓ factors constraintType project) :
    ProjectedPostSpanProfileContainment B κ ℓ factors constraintType project := by
  intro h hadm
  apply Submodule.span_le.mpr
  intro q hq
  simp only [Set.mem_iUnion, Set.mem_image] at hq
  rcases hq with ⟨S, hS, shift, hshift, g, hg, rfl⟩
  exact hgen h hadm S hS shift hshift g hg

/-- Boolean-normalized generator containment is the concrete coefficient-level
Route-W obligation for the Boolean boundary quotient project. -/
def BooleanBoundaryPostSpanGeneratorContainment {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType) : Prop :=
  ∀ (h : ProfileHistogram), ProfileAdmissible κ h →
    ∀ (S : List (Fin N)), S.length ≤ κ →
    ∀ (shift : MvPolynomial (Fin N) ℚ), shift.vars ⊆ S.toFinset →
    ∀ (g : MvPolynomial (Fin N) ℚ),
      g ∈ boundedProfileClassifiedSet factors constraintType S h →
        zeroProfileBooleanNormalize (mlProj (shift * g)) ∈
          profileSubspace h
            (fun σ : ConstraintType => interfaceSpace_compiledBasis B κ ℓ σ)

/-- Finite same-profile slot expansions are enough to discharge the concrete
Boolean-boundary generator containment obligation.  This is the coefficient-level
Property-2 target in its most usable form: after Boolean normalization, each
post-row generator must expand as a finite sum of products whose typed slots lie
in the compiled-basis interface spaces.  Lemma 31's membership constructor then
places the row in the profile subspace. -/
theorem booleanBoundaryPostSpanGeneratorContainment_of_slotExpansion
    {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (hexpand : ∀ (h : ProfileHistogram), ProfileAdmissible κ h →
      ∀ (S : List (Fin N)), S.length ≤ κ →
      ∀ (shift : MvPolynomial (Fin N) ℚ), shift.vars ⊆ S.toFinset →
      ∀ (g : MvPolynomial (Fin N) ℚ),
        g ∈ boundedProfileClassifiedSet factors constraintType S h →
          ∃ (ι : Type) (_ : Fintype ι),
          ∃ (coeff : ι → ℚ),
          ∃ (slot : ι → ∀ σ : ConstraintType,
              Fin (h σ) → MvPolynomial (Fin N) ℚ),
            (∀ t σ j, slot t σ j ∈
              interfaceSpace_compiledBasis B κ ℓ σ) ∧
            zeroProfileBooleanNormalize (mlProj (shift * g)) =
              ∑ t : ι, coeff t •
                (∏ σ : ConstraintType, ∏ j : Fin (h σ), slot t σ j)) :
    BooleanBoundaryPostSpanGeneratorContainment
      B κ ℓ factors constraintType := by
  classical
  intro h hadm S hS shift hshift g hg
  rcases hexpand h hadm S hS shift hshift g hg with
    ⟨ι, hι, coeff, slot, hslot, hrow⟩
  letI : Fintype ι := hι
  rw [hrow]
  exact profileSlotExpansion_mem_profileSubspace h
    (fun σ : ConstraintType => interfaceSpace_compiledBasis B κ ℓ σ)
    coeff slot hslot

/-- Boolean-normalized generator containment closes the Route-W containment
socket for `booleanBoundaryQuotientProject`. -/
theorem booleanBoundary_projectedPostSpanProfileContainment_of_generatorContainment
    {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (hgen : BooleanBoundaryPostSpanGeneratorContainment
      B κ ℓ factors constraintType) :
    ProjectedPostSpanProfileContainment
      B κ ℓ factors constraintType (booleanBoundaryQuotientProject N) := by
  refine projectedPostSpanProfileContainment_of_generatorContainment
    B κ ℓ factors constraintType (booleanBoundaryQuotientProject N) ?_
  intro h hadm S hS shift hshift g hg
  simpa [booleanBoundaryQuotientProject_apply] using
    hgen h hadm S hS shift hshift g hg

/-- Bundled certificate builder for the Boolean coefficient-level Route-W
quotient.  The only remaining mathematical input is the generator containment
statement above. -/
noncomputable def booleanBoundaryQuotientCompressionCertificate_of_generatorContainment
    {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (hgen : BooleanBoundaryPostSpanGeneratorContainment
      B κ ℓ factors constraintType) :
    BoundaryQuotientCompressionCertificate B κ ℓ factors constraintType where
  project := booleanBoundaryQuotientProject N
  project_idempotent := booleanBoundaryQuotientProject_idempotent N
  profile_containment :=
    booleanBoundary_projectedPostSpanProfileContainment_of_generatorContainment
      B κ ℓ factors constraintType hgen

/-! ## Paper-scale Cook--Levin Route-W obligation

This is the concrete next target: prove Boolean-normalized generator containment
for the already transformed `Π+ᵦ` Cook--Levin factor family.  It is stated as a
named proposition rather than assumed.
-/

def CookLevinBooleanBoundaryPostSpanGeneratorContainment_paperScale
    (M : TuringMachine.DTM) (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ 2 ^ 804) (κ ℓ : Nat) : Prop :=
  BooleanBoundaryPostSpanGeneratorContainment
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ
    (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length =>
      (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale M htb hns)[i.val])
    (cookLevinFactorConstraintType_paperScale M htb hns)

/-- Paper-scale Cook--Levin specialization of the same finite slot-expansion
closeout.  This is the direct next target for Route W: construct `hexpand` for
Boolean-normalized Cook--Levin transformed constraint generators. -/
theorem cookLevinBooleanBoundaryPostSpanGeneratorContainment_paperScale_of_slotExpansion
    (M : TuringMachine.DTM) (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ 2 ^ 804) (κ ℓ : Nat)
    (hexpand : ∀ (h : ProfileHistogram), ProfileAdmissible κ h →
      ∀ (S : List (Fin (cook_levin_compilation M (2 ^ 804)
        paperScale_ge_two htb hns).numVars)), S.length ≤ κ →
      ∀ (shift : MvPolynomial (Fin (cook_levin_compilation M (2 ^ 804)
        paperScale_ge_two htb hns).numVars) ℚ), shift.vars ⊆ S.toFinset →
      ∀ (g : MvPolynomial (Fin (cook_levin_compilation M (2 ^ 804)
        paperScale_ge_two htb hns).numVars) ℚ),
        g ∈ boundedProfileClassifiedSet
          (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
              M htb hns).length =>
            (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
              M htb hns)[i.val])
          (cookLevinFactorConstraintType_paperScale M htb hns) S h →
          ∃ (ι : Type) (_ : Fintype ι),
          ∃ (coeff : ι → ℚ),
          ∃ (slot : ι → ∀ σ : ConstraintType,
              Fin (h σ) → MvPolynomial (Fin (cook_levin_compilation M (2 ^ 804)
                paperScale_ge_two htb hns).numVars) ℚ),
            (∀ t σ j, slot t σ j ∈
              interfaceSpace_compiledBasis
                (cook_levin_compilation M (2 ^ 804)
                  paperScale_ge_two htb hns).partition κ ℓ σ) ∧
            zeroProfileBooleanNormalize (mlProj (shift * g)) =
              ∑ t : ι, coeff t •
                (∏ σ : ConstraintType, ∏ j : Fin (h σ), slot t σ j)) :
    CookLevinBooleanBoundaryPostSpanGeneratorContainment_paperScale
      M htb hns κ ℓ := by
  exact booleanBoundaryPostSpanGeneratorContainment_of_slotExpansion
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ
    (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length =>
      (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns)[i.val])
    (cookLevinFactorConstraintType_paperScale M htb hns)
    hexpand

/-- Paper-scale certificate builder for Cook--Levin `Π+ᵦ` factors, conditional
only on the coefficient-level generator containment obligation. -/
noncomputable def cookLevinBooleanBoundaryQuotientCompressionCertificate_paperScale_of_generatorContainment
    (M : TuringMachine.DTM) (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ 2 ^ 804) (κ ℓ : Nat)
    (hgen : CookLevinBooleanBoundaryPostSpanGeneratorContainment_paperScale
      M htb hns κ ℓ) :
    BoundaryQuotientCompressionCertificate
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      κ ℓ
      (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
          M htb hns).length =>
        (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale M htb hns)[i.val])
      (cookLevinFactorConstraintType_paperScale M htb hns) :=
  booleanBoundaryQuotientCompressionCertificate_of_generatorContainment
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ
    (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length =>
      (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale M htb hns)[i.val])
    (cookLevinFactorConstraintType_paperScale M htb hns)
    hgen

/-! ## Axiom audit anchors -/

#print axioms booleanBoundaryPostSpanGeneratorContainment_of_slotExpansion
#print axioms cookLevinBooleanBoundaryPostSpanGeneratorContainment_paperScale_of_slotExpansion
#print axioms projectedPostSpanProfileContainment_of_generatorContainment
#print axioms booleanBoundary_projectedPostSpanProfileContainment_of_generatorContainment
#print axioms booleanBoundaryQuotientCompressionCertificate_of_generatorContainment
#print axioms cookLevinBooleanBoundaryQuotientCompressionCertificate_paperScale_of_generatorContainment

end PallLean.Paper93.DeepMath.PathC
