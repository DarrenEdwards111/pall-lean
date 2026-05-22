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

/-- The raw Cook--Levin product-factor list before applying the Boolean-projected
`Pi+` transform. -/
noncomputable def piPlusRawConstraintFactors
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    List (SATDeciderGaugeSpace M n hn2 htb hns) :=
  (cook_levin_compilation M n hn2 htb hns).constraints.map
    (fun c => (1 : SATDeciderGaugeSpace M n hn2 htb hns) - c.poly)

/-- The transformed factor list is exactly the raw factor list mapped by the
Boolean-projected coordinate-built `Pi+` gauge. -/
theorem piPlusBooleanProjectedTransformedConstraintFactors_eq_map_raw
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) :
    piPlusBooleanProjectedTransformedConstraintFactors M n hn2 htb hns D =
      (piPlusRawConstraintFactors M n hn2 htb hns).map
        (piPlusBooleanProjectedGauge M n hn2 htb hns
          (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D)) := by
  rfl

/-- Route-α coordinate image of the Boolean-projected `Pi+` gauge.  In compiled
block coordinates, the transformed factor is literally the block-Hadamard image
followed by Boolean quotient normalization.  This is the real Lemma-130 algebraic
transport square before choosing the private local chart for the resulting row. -/
theorem piPlusSATCoordinateLinearEquiv_piPlusBooleanProjectedGauge_of_blockCoordinates
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    (piPlusSATCoordinateLinearEquiv M n hn2 htb hns D)
      (piPlusBooleanProjectedGauge M n hn2 htb hns
        (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D) p) =
      blockBooleanNormalize
        (blockPiPlusAlgHom D.blockIndex
          ((piPlusSATCoordinateAlgEquiv M n hn2 htb hns D) p)) := by
  classical
  rw [piPlusBooleanProjectedGauge_of_blockCoordinates_apply]
  change MvPolynomial.rename D.coord
      (zeroProfileBooleanNormalize
        (piPlusSATBlockAlgEquiv M n hn2 htb hns D p)) =
    blockBooleanNormalize
      (blockPiPlusAlgHom D.blockIndex
        (MvPolynomial.rename D.coord p))
  rw [show piPlusSATBlockAlgEquiv M n hn2 htb hns D p =
      MvPolynomial.rename D.coord.symm
        (blockPiPlusAlgHom D.blockIndex (MvPolynomial.rename D.coord p)) by
    simp [piPlusSATBlockAlgEquiv, MvPolynomial.renameEquiv_apply,
      blockPiPlusAlgEquiv]]
  rw [BoolPoly.zeroProfileBooleanNormalize_rename_equiv_blockBooleanNormalize D.coord.symm]
  simp

/-- Paper-scale coordinate image of the Boolean-projected Cook--Levin `Pi+`
gauge. -/
theorem paperScale_piPlusSATCoordinateLinearEquiv_piPlusBooleanProjectedGauge
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (p : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns) :
    (piPlusSATCoordinateLinearEquiv M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns))
      (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns p) =
      blockBooleanNormalize
        (blockPiPlusAlgHom
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).blockIndex
          ((piPlusSATCoordinateAlgEquiv M (2 ^ 804) paperScale_ge_two htb hns
            (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)) p)) := by
  exact piPlusSATCoordinateLinearEquiv_piPlusBooleanProjectedGauge_of_blockCoordinates
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) p

/-- Private local transformed-factor chart: the span generated by the actual
compiled-coordinate Boolean-projected factor.  This is intentionally indexed by
the concrete private chart, not just by `ConstraintType`; that index is exactly
what Lemma 130 supplies and what the older σ-only global submodule erased. -/
noncomputable def privateTransformedFactorChart
    {ι : Type*} (p : MvPolynomial (ι × Bool) ℚ) :
    Submodule ℚ (MvPolynomial (ι × Bool) ℚ) :=
  Submodule.span ℚ ({p} : Set (MvPolynomial (ι × Bool) ℚ))

/-- A private transformed-factor chart is one-dimensional at most. -/
theorem privateTransformedFactorChart_finrank_le_one
    {ι : Type*} (p : MvPolynomial (ι × Bool) ℚ) :
    Module.finrank ℚ ↥(privateTransformedFactorChart p) ≤ 1 := by
  classical
  simpa [privateTransformedFactorChart] using
    (finrank_span_finset_le_card ({p} : Finset (MvPolynomial (ι × Bool) ℚ)))

/-- The compiled-coordinate image of any Boolean-projected `Pi+` transformed
factor lies in its private Lemma-130 local chart. -/
theorem piPlus_transformedFactor_mem_privateChart
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    (piPlusSATCoordinateLinearEquiv M n hn2 htb hns D)
      (piPlusBooleanProjectedGauge M n hn2 htb hns
        (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D) p) ∈
      privateTransformedFactorChart
        (blockBooleanNormalize
          (blockPiPlusAlgHom D.blockIndex
            ((piPlusSATCoordinateAlgEquiv M n hn2 htb hns D) p))) := by
  rw [piPlusSATCoordinateLinearEquiv_piPlusBooleanProjectedGauge_of_blockCoordinates]
  unfold privateTransformedFactorChart
  exact Submodule.subset_span (by simp)

/-- Concrete raw-list version for the actual Cook--Levin transformed constraint
factors.  This is the first unconditional Lemma-130 membership statement: each
factor maps into the one-dimensional private chart generated by its own compiled
normal form. -/
theorem piPlus_transformedConstraintFactor_mem_privateChart
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : Fin (piPlusRawConstraintFactors M n hn2 htb hns).length) :
    (piPlusSATCoordinateLinearEquiv M n hn2 htb hns D)
      (((piPlusRawConstraintFactors M n hn2 htb hns).map
        (piPlusBooleanProjectedGauge M n hn2 htb hns
          (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D)))[i.1]'(by
            simp [i.2])) ∈
      privateTransformedFactorChart
        (blockBooleanNormalize
          (blockPiPlusAlgHom D.blockIndex
            ((piPlusSATCoordinateAlgEquiv M n hn2 htb hns D)
              ((piPlusRawConstraintFactors M n hn2 htb hns).get i)))) := by
  classical
  simp only [List.get_eq_getElem, List.getElem_map]
  exact piPlus_transformedFactor_mem_privateChart M n hn2 htb hns D
    ((piPlusRawConstraintFactors M n hn2 htb hns).get i)

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
#print axioms piPlusRawConstraintFactors
#print axioms piPlusBooleanProjectedTransformedConstraintFactors_eq_map_raw
#print axioms piPlusSATCoordinateLinearEquiv_piPlusBooleanProjectedGauge_of_blockCoordinates
#print axioms paperScale_piPlusSATCoordinateLinearEquiv_piPlusBooleanProjectedGauge
#print axioms privateTransformedFactorChart
#print axioms privateTransformedFactorChart_finrank_le_one
#print axioms piPlus_transformedFactor_mem_privateChart
#print axioms piPlus_transformedConstraintFactor_mem_privateChart
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
