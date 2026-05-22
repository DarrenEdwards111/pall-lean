import PallLean.Paper93.DeepMath.PathC.PiPlusAllocatedProductMultilinearRank

/-!
# Pi+ compiled-coordinate transport

This file isolates Route α's coordinate bridge.  The Cook--Levin `Pi+` block
coordinate data gives an explicit algebra/linear isomorphism between the
uniform SAT polynomial ambient

`SATDeciderGaugeSpace M n hn2 htb hns = MvPolynomial (Fin numVars) ℚ`

and the compiled block ambient

`MvPolynomial (D.blockIndex × Bool) ℚ`.

The canonical compiled-basis interface/profile spaces from Lemma 31 are then
transported across that isomorphism.  This gives the paper-faithful statement
that the fixed compiled-coordinate profile spaces have the same polylogarithmic
rank budget as the existing uniform-coordinate compiled-basis spaces, without
asserting a false shared `W_σ` containment in the raw uniform basis.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93
open PallLean.Paper93.DeepMath.PathB
open SymmetricPowerBound
open WithinProfileBound

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- The compiled block-coordinate polynomial ambient associated to a concrete
Cook--Levin `Pi+` block-coordinate chart. -/
abbrev PiPlusCompiledBlockAmbient
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Type :=
  MvPolynomial (D.blockIndex × Bool) ℚ

/-- The explicit uniform-to-compiled coordinate algebra equivalence. -/
noncomputable def piPlusSATCoordinateAlgEquiv
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) :
    SATDeciderGaugeSpace M n hn2 htb hns ≃ₐ[ℚ]
      PiPlusCompiledBlockAmbient M n hn2 htb hns D :=
  MvPolynomial.renameEquiv ℚ D.coord

/-- The associated uniform-to-compiled coordinate linear equivalence. -/
noncomputable def piPlusSATCoordinateLinearEquiv
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) :
    SATDeciderGaugeSpace M n hn2 htb hns ≃ₗ[ℚ]
      PiPlusCompiledBlockAmbient M n hn2 htb hns D :=
  (piPlusSATCoordinateAlgEquiv M n hn2 htb hns D).toLinearEquiv

/-- In compiled coordinates, the SAT `Pi+` algebra equivalence is exactly the
block-local Hadamard equivalence conjugated by the coordinate chart. -/
theorem piPlusSATBlockAlgEquiv_eq_coordinate_trans_block_trans_coordinate_symm
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) :
    piPlusSATBlockAlgEquiv M n hn2 htb hns D =
      ((piPlusSATCoordinateAlgEquiv M n hn2 htb hns D).trans
        (blockPiPlusAlgEquiv D.blockIndex)).trans
          (piPlusSATCoordinateAlgEquiv M n hn2 htb hns D).symm := by
  rfl

/-- Applying the uniform-to-compiled coordinate chart after the SAT `Pi+`
transform is the same as applying the block-local Hadamard transform directly in
compiled coordinates.  This is the concrete transport square used by Route α. -/
theorem piPlusSATCoordinateAlgEquiv_apply_piPlusSATBlockAlgEquiv
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    piPlusSATCoordinateAlgEquiv M n hn2 htb hns D
        (piPlusSATBlockAlgEquiv M n hn2 htb hns D p) =
      blockPiPlusAlgEquiv D.blockIndex
        (piPlusSATCoordinateAlgEquiv M n hn2 htb hns D p) := by
  simp [piPlusSATBlockAlgEquiv, piPlusSATCoordinateAlgEquiv]

/-- Paper-scale version of the compiled-coordinate transport square for
`cookLevinPiPlusSATTransform_paperScale`. -/
theorem cookLevinPiPlusSATCoordinateAlgEquiv_paperScale_apply_gauge
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (p : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns) :
    piPlusSATCoordinateAlgEquiv M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
        ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge p) =
      blockPiPlusAlgEquiv
        (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).blockIndex
        (piPlusSATCoordinateAlgEquiv M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) p) := by
  rw [cookLevinPiPlusSATTransform_paperScale_gauge_apply]
  exact piPlusSATCoordinateAlgEquiv_apply_piPlusSATBlockAlgEquiv
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) p

/-- Concrete constraint-type classification for the Boolean-projected `Pi+`
transformed Cook--Levin factor list.  It mirrors the compiler's three-list
layout: booleanity prefix, adjacency middle segment, transition-skeleton tail
(recorded in the existing profile bookkeeping as `transitionLeft`). -/
noncomputable def cookLevinFactorConstraintType
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) :
    Fin (piPlusBooleanProjectedTransformedConstraintFactors M n hn2 htb hns D).length →
      ConstraintType :=
  fun i =>
    if i.1 < n then
      ConstraintType.booleanity
    else if i.1 < n + (PaperFaithfulSeparation.adjConstraintList n).length then
      ConstraintType.adjacency
    else
      ConstraintType.transitionLeft

/-- The transformed-factor classifier is `booleanity` on the initial Boolean
constraint prefix. -/
theorem cookLevinFactorConstraintType_eq_booleanity
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : Fin (piPlusBooleanProjectedTransformedConstraintFactors M n hn2 htb hns D).length)
    (hi : i.1 < n) :
    cookLevinFactorConstraintType M n hn2 htb hns D i = ConstraintType.booleanity := by
  simp [cookLevinFactorConstraintType, hi]

/-- The transformed-factor classifier is `adjacency` on the adjacency segment. -/
theorem cookLevinFactorConstraintType_eq_adjacency
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : Fin (piPlusBooleanProjectedTransformedConstraintFactors M n hn2 htb hns D).length)
    (hlo : n ≤ i.1)
    (hi : i.1 < n + (PaperFaithfulSeparation.adjConstraintList n).length) :
    cookLevinFactorConstraintType M n hn2 htb hns D i = ConstraintType.adjacency := by
  simp [cookLevinFactorConstraintType, Nat.not_lt.mpr hlo, hi]

/-- The transformed-factor classifier is `transitionLeft` on the transition
skeleton tail. -/
theorem cookLevinFactorConstraintType_eq_transitionLeft
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : Fin (piPlusBooleanProjectedTransformedConstraintFactors M n hn2 htb hns D).length)
    (hi : n + (PaperFaithfulSeparation.adjConstraintList n).length ≤ i.1) :
    cookLevinFactorConstraintType M n hn2 htb hns D i = ConstraintType.transitionLeft := by
  have hnot_bool : ¬ i.1 < n := Nat.not_lt.mpr (le_trans (Nat.le_add_right _ _) hi)
  have hnot_adj : ¬ i.1 < n + (PaperFaithfulSeparation.adjConstraintList n).length :=
    Nat.not_lt.mpr hi
  simp [cookLevinFactorConstraintType, hnot_bool, hnot_adj]

/-- Paper-scale specialization of the transformed-factor classifier. -/
noncomputable abbrev cookLevinFactorConstraintType_paperScale
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale M htb hns).length →
      ConstraintType :=
  cookLevinFactorConstraintType M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Same-ambient form of P5 σ-only dependence for the implemented compiled-basis
interface spaces.  The concrete implementation is independent of `(B, κ, ℓ)`
and depends only on the constraint type `σ`.  The parameters are therefore
paper-compatible bookkeeping: they keep the API aligned with the surrounding
SPDP row-space budget `M^B_{κ,ℓ}`, while P5's σ-only local alphabet is reflected
by this equality. -/
theorem interfaceSpace_compiledBasis_eq_of_same_type_sameAmbient
    {N : Nat} (B B' : BlockPartition N) (κ κ' ℓ ℓ' : Nat) (σ : ConstraintType) :
    interfaceSpace_compiledBasis B κ ℓ σ = interfaceSpace_compiledBasis B' κ' ℓ' σ := by
  rfl

/-- Transport of a canonical compiled-basis interface space into the explicit
compiled block ambient.  This is the fixed `W_τ` chart in compiled coordinates. -/
noncomputable def compiledBlockInterfaceSpace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat) (τ : ConstraintType) :
    Submodule ℚ (PiPlusCompiledBlockAmbient M n hn2 htb hns D) :=
  Submodule.map (piPlusSATCoordinateLinearEquiv M n hn2 htb hns D).toLinearMap
    (interfaceSpace_compiledBasis B κ ℓ τ)

/-- Transport preserves the `d₀ = 3` interface-space rank budget. -/
theorem compiledBlockInterfaceSpace_finrank_le_three
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat) (τ : ConstraintType) :
    Module.finrank ℚ ↥(compiledBlockInterfaceSpace M n hn2 htb hns D B κ ℓ τ) ≤ 3 := by
  classical
  unfold compiledBlockInterfaceSpace
  rw [LinearEquiv.finrank_map_eq]
  exact interfaceSpace_compiledBasis_finrank_le_three B κ ℓ τ

/-- Membership transports from the uniform canonical interface space to the
fixed compiled-block interface space. -/
theorem mem_compiledBlockInterfaceSpace_of_mem_interfaceSpace_compiledBasis
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat) (τ : ConstraintType)
    {p : SATDeciderGaugeSpace M n hn2 htb hns}
    (hp : p ∈ interfaceSpace_compiledBasis B κ ℓ τ) :
    (piPlusSATCoordinateLinearEquiv M n hn2 htb hns D) p ∈
      compiledBlockInterfaceSpace M n hn2 htb hns D B κ ℓ τ := by
  classical
  unfold compiledBlockInterfaceSpace
  exact Submodule.mem_map_of_mem hp

/-- A local factor already placed in the canonical compiled-basis chart remains
in the fixed compiled-block interface space after any allocated local derivative
and coordinate transport. -/
theorem compiledImage_iterDerivList_mem_compiledBlockInterfaceSpace_of_mem_interfaceSpace_compiledBasis
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat) (τ : ConstraintType)
    {p : SATDeciderGaugeSpace M n hn2 htb hns}
    (hp : p ∈ interfaceSpace_compiledBasis B κ ℓ τ)
    (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
    (piPlusSATCoordinateLinearEquiv M n hn2 htb hns D) (SPDP.iterDerivList S p) ∈
      compiledBlockInterfaceSpace M n hn2 htb hns D B κ ℓ τ := by
  exact mem_compiledBlockInterfaceSpace_of_mem_interfaceSpace_compiledBasis
    M n hn2 htb hns D B κ ℓ τ
    (iterDerivList_mem_interfaceSpace_compiledBasis B κ ℓ τ p hp S)

/-- Route-α local-factor transport for the allocated derivative factors.  Once
the unallocated transformed constraint factor at index `i` is identified with
its canonical compiled-basis type `constraintType i`, the allocated derivative
local factor's compiled image lies in the fixed compiled-block `W_{τ}`. -/
theorem allocatedDerivativeLocalFactor_compiledImage_mem_compiledBlockInterfaceSpace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat)
    (constraintType : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length → ConstraintType)
    (hbase : ∀ i,
      (piPlusBooleanProjectedTransformedConstraintFactors M n hn2 htb hns D)[i.val] ∈
        interfaceSpace_compiledBasis B κ ℓ (constraintType i))
    (i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length) :
    (piPlusSATCoordinateLinearEquiv M n hn2 htb hns D)
      ((BoolPoly.allocatedDerivativeLocalFactors M n hn2 htb hns D alloc) i) ∈
      compiledBlockInterfaceSpace M n hn2 htb hns D B κ ℓ (constraintType i) := by
  classical
  unfold BoolPoly.allocatedDerivativeLocalFactors
  exact compiledImage_iterDerivList_mem_compiledBlockInterfaceSpace_of_mem_interfaceSpace_compiledBasis
    M n hn2 htb hns D B κ ℓ (constraintType i) (hbase i) (alloc i)

/-- Paper-scale specialization of allocated local-factor compiled-coordinate
membership. -/
theorem paperScale_allocatedDerivativeLocalFactor_compiledImage_mem_compiledBlockInterfaceSpace
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (alloc : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length →
      List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
    (κ ℓ : Nat)
    (constraintType : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length → ConstraintType)
    (hbase : ∀ i,
      (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale M htb hns)[i.val] ∈
        interfaceSpace_compiledBasis
          (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
          κ ℓ (constraintType i))
    (i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length) :
    (piPlusSATCoordinateLinearEquiv M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns))
      ((BoolPoly.allocatedDerivativeLocalFactors M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc) i) ∈
      compiledBlockInterfaceSpace M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
        κ ℓ (constraintType i) := by
  exact allocatedDerivativeLocalFactor_compiledImage_mem_compiledBlockInterfaceSpace
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    alloc (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ constraintType hbase i

/-- Transport of a whole Lemma-31 profile subspace into the compiled block
ambient. -/
noncomputable def compiledBlockProfileSubspace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat) (h : ProfileHistogram) :
    Submodule ℚ (PiPlusCompiledBlockAmbient M n hn2 htb hns D) :=
  Submodule.map (piPlusSATCoordinateLinearEquiv M n hn2 htb hns D).toLinearMap
    (profileSubspace h
      (fun τ : ConstraintType => interfaceSpace_compiledBasis B κ ℓ τ))

/-- The compiled-coordinate transported profile subspace has exactly the same
finrank as the uniform-coordinate source profile subspace. -/
theorem compiledBlockProfileSubspace_finrank_eq
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat) (h : ProfileHistogram) :
    Module.finrank ℚ ↥(compiledBlockProfileSubspace M n hn2 htb hns D B κ ℓ h) =
      Module.finrank ℚ ↥(profileSubspace h
        (fun τ : ConstraintType => interfaceSpace_compiledBasis B κ ℓ τ)) := by
  classical
  unfold compiledBlockProfileSubspace
  rw [LinearEquiv.finrank_map_eq]

/-- Route α transport of Lemma 31: after moving to explicit compiled block
coordinates, every admissible profile subspace keeps the existing
`withinProfileBound κ` budget. -/
theorem compiledBlockProfileSubspace_finrank_le_withinProfileBound
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat) (h : ProfileHistogram) (hadm : ProfileAdmissible κ h) :
    Module.finrank ℚ ↥(compiledBlockProfileSubspace M n hn2 htb hns D B κ ℓ h) ≤
      withinProfileBound κ := by
  classical
  rw [compiledBlockProfileSubspace_finrank_eq]
  exact profileSubspace_compiledBasis_finrank_le_withinProfileBound B κ ℓ h hadm

/-- Paper-scale explicit uniform-to-compiled coordinate algebra equivalence. -/
noncomputable def cookLevinPiPlusSATCoordinateAlgEquiv_paperScale
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns ≃ₐ[ℚ]
      PiPlusCompiledBlockAmbient M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) :=
  piPlusSATCoordinateAlgEquiv M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale explicit uniform-to-compiled coordinate linear equivalence. -/
noncomputable def cookLevinPiPlusSATCoordinateLinearEquiv_paperScale
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns ≃ₗ[ℚ]
      PiPlusCompiledBlockAmbient M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) :=
  piPlusSATCoordinateLinearEquiv M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale transported profile subspace bound. -/
theorem paperScale_compiledBlockProfileSubspace_finrank_le_withinProfileBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (κ ℓ : Nat) (h : ProfileHistogram) (hadm : ProfileAdmissible κ h) :
    Module.finrank ℚ ↥(compiledBlockProfileSubspace
        M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
        κ ℓ h) ≤ withinProfileBound κ :=
  compiledBlockProfileSubspace_finrank_le_withinProfileBound
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ h hadm

/-! ## Axiom audit anchors -/

#print axioms piPlusSATCoordinateAlgEquiv
#print axioms piPlusSATCoordinateLinearEquiv
#print axioms piPlusSATBlockAlgEquiv_eq_coordinate_trans_block_trans_coordinate_symm
#print axioms piPlusSATCoordinateAlgEquiv_apply_piPlusSATBlockAlgEquiv
#print axioms cookLevinPiPlusSATCoordinateAlgEquiv_paperScale_apply_gauge
#print axioms cookLevinFactorConstraintType
#print axioms cookLevinFactorConstraintType_eq_booleanity
#print axioms cookLevinFactorConstraintType_eq_adjacency
#print axioms cookLevinFactorConstraintType_eq_transitionLeft
#print axioms cookLevinFactorConstraintType_paperScale
#print axioms interfaceSpace_compiledBasis_eq_of_same_type_sameAmbient
#print axioms compiledBlockInterfaceSpace
#print axioms compiledBlockInterfaceSpace_finrank_le_three
#print axioms mem_compiledBlockInterfaceSpace_of_mem_interfaceSpace_compiledBasis
#print axioms compiledImage_iterDerivList_mem_compiledBlockInterfaceSpace_of_mem_interfaceSpace_compiledBasis
#print axioms allocatedDerivativeLocalFactor_compiledImage_mem_compiledBlockInterfaceSpace
#print axioms paperScale_allocatedDerivativeLocalFactor_compiledImage_mem_compiledBlockInterfaceSpace
#print axioms compiledBlockProfileSubspace
#print axioms compiledBlockProfileSubspace_finrank_eq
#print axioms compiledBlockProfileSubspace_finrank_le_withinProfileBound
#print axioms cookLevinPiPlusSATCoordinateAlgEquiv_paperScale
#print axioms cookLevinPiPlusSATCoordinateLinearEquiv_paperScale
#print axioms paperScale_compiledBlockProfileSubspace_finrank_le_withinProfileBound

end PallLean.Paper93.DeepMath.PathC
