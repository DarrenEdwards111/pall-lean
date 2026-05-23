import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanityProjectedRowObstruction
import PallLean.Paper93.DeepMath.PathC.PiPlusTransitionLeftShiftAugmentedContainment
import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanBoundaryContainment

/-!
# Shift-augmented Route-W composition surface

The Booleanity, adjacency, and transition-left commits discharged the local
per-row atoms.  This file composes those atoms into the `profileSubspace` target
used by the arity-5 shift-augmented Route-W closeout.

The key point is deliberately honest: the local row atoms give singleton-profile
memberships unconditionally.  The remaining global Leibniz/distribution task is
isolated as a finite same-profile slot expansion; once such an expansion is
provided for each Cook--Levin generator, the existing
`ShiftAugmentedNaturallyProfiledProjectedPostSpanContainment` and finrank
closeout apply directly.
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
open PallLean.SymTensorPowerDim

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

namespace BoolPoly

/-- Singleton profile concentrated at one constraint type. -/
def singletonConstraintProfile (τ : ConstraintType) : ProfileHistogram :=
  fun σ : ConstraintType => if σ = τ then 1 else 0

@[simp] theorem singletonConstraintProfile_self (τ : ConstraintType) :
    singletonConstraintProfile τ τ = 1 := by
  simp [singletonConstraintProfile]

@[simp] theorem singletonConstraintProfile_of_ne {τ σ : ConstraintType}
    (hσ : σ ≠ τ) : singletonConstraintProfile τ σ = 0 := by
  simp [singletonConstraintProfile, hσ]

/-- A one-row local membership is a singleton-profile product: the chosen type
contributes the row, and all other types contribute empty products. -/
theorem mem_shiftAugmented_singletonProfileSubspace_of_mem_interface
    {N : Nat} (B : BlockPartition N) (κ ℓ : Nat)
    (τ : ConstraintType) (row : MvPolynomial (Fin N) ℚ)
    (hrow : row ∈ shiftAugmentedInterfaceSpace_compiledBasis B κ ℓ τ) :
    row ∈ profileSubspace (singletonConstraintProfile τ)
      (fun σ : ConstraintType =>
        shiftAugmentedInterfaceSpace_compiledBasis B κ ℓ σ) := by
  classical
  let slot : ∀ σ : ConstraintType,
      Fin (singletonConstraintProfile τ σ) → MvPolynomial (Fin N) ℚ :=
    fun σ _ => if σ = τ then row else 1
  have hslot : ∀ σ j, slot σ j ∈
      shiftAugmentedInterfaceSpace_compiledBasis B κ ℓ σ := by
    intro σ j
    by_cases hστ : σ = τ
    · subst σ
      simpa [slot]
    · have hzero : singletonConstraintProfile τ σ = 0 := by
        simp [singletonConstraintProfile, hστ]
      have hempty : IsEmpty (Fin (singletonConstraintProfile τ σ)) := by
        rw [hzero]
        infer_instance
      exact False.elim (IsEmpty.false j)
  have hprod := profileProduct_mem_profileSubspace
    (singletonConstraintProfile τ)
    (fun σ : ConstraintType => shiftAugmentedInterfaceSpace_compiledBasis B κ ℓ σ)
    slot hslot
  have hprod_eq :
      (∏ σ : ConstraintType,
          ∏ j : Fin (singletonConstraintProfile τ σ), slot σ j) = row := by
    fin_cases τ <;>
      simp [singletonConstraintProfile, slot]
  simpa [hprod_eq]
    using hprod

/-- Booleanity post-row, after the paper-faithful collapse, lands in the
shift-augmented singleton Booleanity profile. -/
theorem booleanityPostRow_mem_shiftAugmented_singletonProfileSubspace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat) (v : Fin n) :
    MvPolynomial.rename
        (booleanityOneCoordinateCollapseMap M n hn2 htb hns D v)
        (cookLevinBooleanityPostRow M n hn2 htb hns D v) ∈
      profileSubspace (singletonConstraintProfile ConstraintType.booleanity)
        (fun σ : ConstraintType =>
          shiftAugmentedInterfaceSpace_compiledBasis B κ ℓ σ) := by
  have hlegacy :=
    rename_booleanityOneCoordinateCollapseMap_cookLevinBooleanityPostRow_mem_interfaceSpace
      M n hn2 htb hns D B κ ℓ v
  have haug : MvPolynomial.rename
        (booleanityOneCoordinateCollapseMap M n hn2 htb hns D v)
        (cookLevinBooleanityPostRow M n hn2 htb hns D v) ∈
      shiftAugmentedInterfaceSpace_compiledBasis B κ ℓ ConstraintType.booleanity :=
    interfaceSpace_compiledBasis_le_shiftAugmented B κ ℓ ConstraintType.booleanity hlegacy
  exact mem_shiftAugmented_singletonProfileSubspace_of_mem_interface
    B κ ℓ ConstraintType.booleanity _ haug

/-- Adjacency post-row, after endpoint collapse, lands in the shift-augmented
singleton adjacency profile. -/
theorem adjacencyPostRow_mem_shiftAugmented_singletonProfileSubspace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat)
    (i : Fin n) (hi : i.val + 1 < n)
    (hab : (D.coord i).1 ≠ (D.coord ⟨i.val + 1, hi⟩).1) :
    MvPolynomial.rename
        (adjacencyEndpointCollapseMap i ⟨i.val + 1, hi⟩ (by
          simpa [PaperFaithfulSeparation.cook_levin_numVars] using hn2))
        (cookLevinAdjacencyPostRow M n hn2 htb hns D i hi) ∈
      profileSubspace (singletonConstraintProfile ConstraintType.adjacency)
        (fun σ : ConstraintType =>
          shiftAugmentedInterfaceSpace_compiledBasis B κ ℓ σ) := by
  have hrow :=
    rename_adjacencyEndpointCollapseMap_cookLevinAdjacencyPostRow_mem_shiftAugmentedInterfaceSpace
      M n hn2 htb hns D B κ ℓ i hi hab
  exact mem_shiftAugmented_singletonProfileSubspace_of_mem_interface
    B κ ℓ ConstraintType.adjacency _ hrow

/-- Transition-left post-row, after endpoint collapse, lands in the
shift-augmented singleton transition-left profile. -/
theorem transitionLeftPostRow_mem_shiftAugmented_singletonProfileSubspace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat)
    (q : Fin M.numStates) (i : Fin n) (hi : i.val + 1 < n)
    (hab : (D.coord i).1 ≠ (D.coord ⟨i.val + 1, hi⟩).1) :
    MvPolynomial.rename
        (adjacencyEndpointCollapseMap i ⟨i.val + 1, hi⟩ (by
          simpa [PaperFaithfulSeparation.cook_levin_numVars] using hn2))
        (cookLevinTransitionLeftPostRow M n hn2 htb hns D q i hi) ∈
      profileSubspace (singletonConstraintProfile ConstraintType.transitionLeft)
        (fun σ : ConstraintType =>
          shiftAugmentedInterfaceSpace_compiledBasis B κ ℓ σ) := by
  have hrow :=
    rename_adjacencyEndpointCollapseMap_cookLevinTransitionLeftPostRow_mem_shiftAugmentedInterfaceSpace
      M n hn2 htb hns D B κ ℓ q i hi hab
  exact mem_shiftAugmented_singletonProfileSubspace_of_mem_interface
    B κ ℓ ConstraintType.transitionLeft _ hrow

end BoolPoly

/-- Finite same-profile expansion into shift-augmented Route-W slots.  This is
the exact composition target for distributed Cook--Levin Leibniz rows: every
summand must have the same natural profile `h`, with each slot already placed in
the arity-5 `W_σ`. -/
def ShiftAugmentedProfileSlotExpansion {N : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (h : ProfileHistogram) (row : MvPolynomial (Fin N) ℚ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι),
  ∃ (coeff : ι → ℚ),
  ∃ (slot : ι → ∀ σ : ConstraintType,
      Fin (h σ) → MvPolynomial (Fin N) ℚ),
    (∀ t σ j, slot t σ j ∈
      shiftAugmentedInterfaceSpace_compiledBasis B κ ℓ σ) ∧
    row = ∑ t : ι, coeff t •
      (∏ σ : ConstraintType, ∏ j : Fin (h σ), slot t σ j)

/-- Any finite same-profile shift-augmented slot expansion is a member of the
corresponding profile subspace. -/
theorem shiftAugmentedProfileSlotExpansion_mem_profileSubspace {N : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (h : ProfileHistogram) (row : MvPolynomial (Fin N) ℚ)
    (hexp : ShiftAugmentedProfileSlotExpansion B κ ℓ h row) :
    row ∈ profileSubspace h
      (fun σ : ConstraintType =>
        shiftAugmentedInterfaceSpace_compiledBasis B κ ℓ σ) := by
  classical
  rcases hexp with ⟨ι, hι, coeff, slot, hslot, hrow⟩
  letI : Fintype ι := hι
  rw [hrow]
  exact profileSlotExpansion_mem_profileSubspace h
    (fun σ : ConstraintType => shiftAugmentedInterfaceSpace_compiledBasis B κ ℓ σ)
    coeff slot hslot

/-- Paper-scale Cook--Levin shift-augmented generator expansion socket.  This is
the concrete remaining decomposition obligation: for every generated post-row,
classify its natural profile and provide a finite expansion into the already
proved Booleanity/adjacency/transition-left slots. -/
def CookLevinShiftAugmentedGeneratorExpansion_paperScale
    (M : TuringMachine.DTM) (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ 2 ^ 804) (κ ℓ : Nat)
    (project : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns →ₗ[ℚ]
      SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns)
    (classifier : CookLevinProjectedPostRowProfileClassifier_paperScale
      M htb hns κ) : Prop :=
  ∀ (h : ProfileHistogram)
    (S : List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
    (_hS : S.length ≤ κ)
    (shift : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns)
    (_hshift : shift.vars ⊆ S.toFinset)
    (g : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns),
      g ∈ boundedProfileClassifiedSet
        (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
            M htb hns).length =>
          (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
            M htb hns)[i.val])
        (cookLevinFactorConstraintType_paperScale M htb hns) S h →
        ShiftAugmentedProfileSlotExpansion
          (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
          κ ℓ (classifier.profile h S shift g)
          (project (mlProj (shift * g)))

/-- The finite slot-expansion socket discharges the shift-augmented
natural-profile generator containment. -/
theorem cookLevinShiftAugmentedNaturallyProfiledGeneratorContainment_paperScale_of_expansion
    (M : TuringMachine.DTM) (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ 2 ^ 804) (κ ℓ : Nat)
    (project : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns →ₗ[ℚ]
      SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns)
    (classifier : CookLevinProjectedPostRowProfileClassifier_paperScale
      M htb hns κ)
    (hexp : CookLevinShiftAugmentedGeneratorExpansion_paperScale
      M htb hns κ ℓ project classifier) :
    ShiftAugmentedNaturallyProfiledProjectedGeneratorContainment
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      κ ℓ
      (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
          M htb hns).length =>
        (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
          M htb hns)[i.val])
      (cookLevinFactorConstraintType_paperScale M htb hns)
      project classifier := by
  intro h S hS shift hshift g hg
  exact shiftAugmentedProfileSlotExpansion_mem_profileSubspace
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ (classifier.profile h S shift g) (project (mlProj (shift * g)))
    (hexp h S hS shift hshift g hg)

/-- Span-level shift-augmented Route-W containment for the paper-scale
Cook--Levin factor family, from the finite slot-expansion socket. -/
theorem cookLevinShiftAugmentedNaturallyProfiledPostSpanContainment_paperScale_of_expansion
    (M : TuringMachine.DTM) (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ 2 ^ 804) (κ ℓ : Nat)
    (project : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns →ₗ[ℚ]
      SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns)
    (classifier : CookLevinProjectedPostRowProfileClassifier_paperScale
      M htb hns κ)
    (hexp : CookLevinShiftAugmentedGeneratorExpansion_paperScale
      M htb hns κ ℓ project classifier) :
    ShiftAugmentedNaturallyProfiledProjectedPostSpanContainment
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      κ ℓ
      (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
          M htb hns).length =>
        (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
          M htb hns)[i.val])
      (cookLevinFactorConstraintType_paperScale M htb hns)
      project classifier := by
  exact shiftAugmentedNaturallyProfiledProjectedPostSpanContainment_of_generatorContainment
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ
    (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length =>
      (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns)[i.val])
    (cookLevinFactorConstraintType_paperScale M htb hns)
    project classifier
    (cookLevinShiftAugmentedNaturallyProfiledGeneratorContainment_paperScale_of_expansion
      M htb hns κ ℓ project classifier hexp)

/-- Final arity-5 finrank closeout for the paper-scale Cook--Levin
shift-augmented Route-W composition, conditional only on the finite slot
expansion decomposition. -/
theorem cookLevinShiftAugmentedProjectedWithinProfileFinrank_paperScale_of_expansion
    (M : TuringMachine.DTM) (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ 2 ^ 804) (κ ℓ : Nat)
    (project : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns →ₗ[ℚ]
      SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns)
    (classifier : CookLevinProjectedPostRowProfileClassifier_paperScale
      M htb hns κ)
    (hexp : CookLevinShiftAugmentedGeneratorExpansion_paperScale
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
  shiftAugmentedNaturallyProfiledProjectedWithinProfileFinrank_of_containment
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ
    (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length =>
      (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns)[i.val])
    (cookLevinFactorConstraintType_paperScale M htb hns)
    project classifier
    (cookLevinShiftAugmentedNaturallyProfiledPostSpanContainment_paperScale_of_expansion
      M htb hns κ ℓ project classifier hexp)

/-! ## Axiom audit anchors -/

#print axioms BoolPoly.mem_shiftAugmented_singletonProfileSubspace_of_mem_interface
#print axioms BoolPoly.booleanityPostRow_mem_shiftAugmented_singletonProfileSubspace
#print axioms BoolPoly.adjacencyPostRow_mem_shiftAugmented_singletonProfileSubspace
#print axioms BoolPoly.transitionLeftPostRow_mem_shiftAugmented_singletonProfileSubspace
#print axioms shiftAugmentedProfileSlotExpansion_mem_profileSubspace
#print axioms cookLevinShiftAugmentedNaturallyProfiledGeneratorContainment_paperScale_of_expansion
#print axioms cookLevinShiftAugmentedNaturallyProfiledPostSpanContainment_paperScale_of_expansion
#print axioms cookLevinShiftAugmentedProjectedWithinProfileFinrank_paperScale_of_expansion

end PallLean.Paper93.DeepMath.PathC
