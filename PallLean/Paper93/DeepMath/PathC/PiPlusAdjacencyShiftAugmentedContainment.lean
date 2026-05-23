import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedSignedConcreteFactors
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeDischargeSubgoals
import PallLean.Paper93.DeepMath.PathB.ZeroProfileNormalFormInstantiationProgress
import PallLean.Paper93.CompiledCoefficientBasis

/-!
# Shift-augmented adjacency row containment

This file is the adjacency analogue of the repaired Booleanity row atom, but
for the new paper-faithful arity-5 `W_σ` chart.  After the local endpoint
transport that sends an adjacency edge to the canonical two endpoint slots, the
adjacency post-row is `1 - X₀ * X₁`, hence it lies in
`shiftAugmentedInterfaceSpace_compiledBasis ... ConstraintType.adjacency`.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open SymmetricPowerBound
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

namespace BoolPoly

/-- Endpoint collapse for a two-endpoint adjacency row: the first endpoint maps
to canonical local slot `0`, the second endpoint maps to canonical local slot
`1`, and all unrelated variables are left fixed. -/
noncomputable def adjacencyEndpointCollapseMap {N : Nat}
    (a b : Fin N) (hN : 1 < N) : Fin N → Fin N :=
  fun x =>
    if x = a then
      ⟨0, by omega⟩
    else if x = b then
      ⟨1, hN⟩
    else x

/-- The canonical adjacency row `1 - X₀X₁` belongs to the shift-augmented
adjacency interface chart. -/
theorem canonicalAdjacencyPostRow_mem_shiftAugmentedInterfaceSpace
    {N : Nat} (B : BlockPartition N) (κ ℓ : Nat) :
    ((1 : MvPolynomial (Fin N) ℚ) - canonicalLocalEndpointPair) ∈
      shiftAugmentedInterfaceSpace_compiledBasis B κ ℓ ConstraintType.adjacency := by
  have hone := shiftAugmentedInterfacePolynomial_mem_shiftAugmentedInterfaceSpace
    B κ ℓ ConstraintType.adjacency shiftAugmentedConstSlot
  norm_num [shiftAugmentedInterfacePolynomial, shiftAugmentedConstSlot,
    shiftAugmentedLocalArity] at hone
  have hpair :=
    canonicalLocalEndpointPair_mem_shiftAugmentedInterfaceSpace_of_not_transitionRight
      B κ ℓ ConstraintType.adjacency (by simp)
  exact Submodule.sub_mem _ hone hpair

/-- Under endpoint collapse, the flat signed adjacency atom with coefficient
`1` is exactly the canonical row `1 - X₀X₁`. -/
theorem rename_adjacencyEndpointCollapseMap_satSignedCrossAtom_one_eq_canonical
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (a b : Fin (cook_levin_compilation M n hn2 htb hns).numVars)
    (hab : a ≠ b) :
    MvPolynomial.rename
        (adjacencyEndpointCollapseMap a b (by
          simpa [PaperFaithfulSeparation.cook_levin_numVars] using hn2))
        (satSignedCrossAtom M n hn2 htb hns 1 a b) =
      ((1 : SATDeciderGaugeSpace M n hn2 htb hns) - canonicalLocalEndpointPair) := by
  have hN : 1 < (cook_levin_compilation M n hn2 htb hns).numVars := by
    simpa [PaperFaithfulSeparation.cook_levin_numVars] using hn2
  have hpos : 0 < (cook_levin_compilation M n hn2 htb hns).numVars :=
    lt_trans (by norm_num) hN
  unfold satSignedCrossAtom adjacencyEndpointCollapseMap canonicalLocalEndpointPair
  have hba : ¬ b = a := by
    intro h
    exact hab h.symm
  simp [MvPolynomial.rename_X, hba, canonicalLocalX, canonicalLocalX1, hN, hpos]

/-- Transported adjacency atom membership in the shift-augmented adjacency
interface chart. -/
theorem rename_adjacencyEndpointCollapseMap_satSignedCrossAtom_one_mem_shiftAugmentedInterfaceSpace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat)
    (a b : Fin (cook_levin_compilation M n hn2 htb hns).numVars)
    (hab : a ≠ b) :
    MvPolynomial.rename
        (adjacencyEndpointCollapseMap a b (by
          simpa [PaperFaithfulSeparation.cook_levin_numVars] using hn2))
        (satSignedCrossAtom M n hn2 htb hns 1 a b) ∈
      shiftAugmentedInterfaceSpace_compiledBasis B κ ℓ ConstraintType.adjacency := by
  rw [rename_adjacencyEndpointCollapseMap_satSignedCrossAtom_one_eq_canonical
    M n hn2 htb hns a b hab]
  exact canonicalAdjacencyPostRow_mem_shiftAugmentedInterfaceSpace B κ ℓ

/-- Concrete Cook--Levin adjacency post-row, before endpoint transport.  For an
adjacency constraint between consecutive variables, this is the Boolean-projected
`Π+` pullback of the concrete adjacency factor. -/
noncomputable def cookLevinAdjacencyPostRow
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : Fin n) (hi : i.val + 1 < n) :
    SATDeciderGaugeSpace M n hn2 htb hns :=
  (piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
    (zeroProfileBooleanNormalize
      (piPlusSATBlockAlgEquiv M n hn2 htb hns D
        (((1 : MvPolynomial (Fin n) ℚ) - (adjLC n i hi).poly) :
          SATDeciderGaugeSpace M n hn2 htb hns)))

/-- If the two adjacency endpoints are in distinct `Π+` blocks, the concrete
adjacency post-row is the signed-cross atom zero-derivative row. -/
theorem cookLevinAdjacencyPostRow_eq_mlProj_satSignedCrossAtom
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : Fin n) (hi : i.val + 1 < n)
    (hab : (D.coord i).1 ≠ (D.coord ⟨i.val + 1, hi⟩).1) :
    cookLevinAdjacencyPostRow M n hn2 htb hns D i hi =
      mlProj
        ((1 : SATDeciderGaugeSpace M n hn2 htb hns) *
          SPDP.iterDerivList []
            (satSignedCrossAtom M n hn2 htb hns 1 i ⟨i.val + 1, hi⟩)) := by
  unfold cookLevinAdjacencyPostRow
  rw [adjacencyFactor_eq_satSignedCrossAtom M n hn2 htb hns i hi]
  exact (adjacencyFactor_signedCrossAtomRowCertificate_unconditional
    M n hn2 htb hns D i hi hab).2

/-- The concrete adjacency endpoints are distinct. -/
theorem adjacency_consecutive_endpoints_ne
    {n : Nat} (i : Fin n) (hi : i.val + 1 < n) :
    (i : Fin n) ≠ ⟨i.val + 1, hi⟩ := by
  intro h
  have hv := congrArg Fin.val h
  simp at hv

/-- The zero-derivative signed adjacency row simplifies to the signed atom. -/
theorem mlProj_one_mul_iterDerivList_nil_satSignedCrossAtom_one
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (a b : Fin (cook_levin_compilation M n hn2 htb hns).numVars)
    (hab : a ≠ b) :
    mlProj
        ((1 : SATDeciderGaugeSpace M n hn2 htb hns) *
          SPDP.iterDerivList []
            (satSignedCrossAtom M n hn2 htb hns 1 a b)) =
      satSignedCrossAtom M n hn2 htb hns 1 a b := by
  unfold satSignedCrossAtom
  simp
  have hmul :
      mlProj (X a * X b : SATDeciderGaugeSpace M n hn2 htb hns) =
        (X a * X b : SATDeciderGaugeSpace M n hn2 htb hns) :=
    mlProj_X_mul_X_ne (σ := Fin (cook_levin_compilation M n hn2 htb hns).numVars)
      (a := a) (b := b) hab
  rw [sub_eq_add_neg, mlProj_add]
  have hone : mlProj (1 : SATDeciderGaugeSpace M n hn2 htb hns) = 1 := by
    rw [show (1 : SATDeciderGaugeSpace M n hn2 htb hns) =
      MvPolynomial.monomial 0 1 by rfl, mlProj_monomial]
    have h0 : Finsupp.IsMultilinear
        (0 : Fin (cook_levin_compilation M n hn2 htb hns).numVars →₀ Nat) := by
      intro x
      simp
    rw [if_pos h0]
  have hneg :
      mlProj (-(X a * X b : SATDeciderGaugeSpace M n hn2 htb hns)) =
        -(X a * X b : SATDeciderGaugeSpace M n hn2 htb hns) := by
    rw [← neg_one_smul ℚ (X a * X b : SATDeciderGaugeSpace M n hn2 htb hns),
      mlProj_smul, hmul]
  rw [hone, hneg]

/-- Main adjacency per-row containment: after endpoint collapse, each concrete
adjacency post-row lies in the arity-5 shift-augmented adjacency chart. -/
theorem rename_adjacencyEndpointCollapseMap_cookLevinAdjacencyPostRow_mem_shiftAugmentedInterfaceSpace
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
      shiftAugmentedInterfaceSpace_compiledBasis B κ ℓ ConstraintType.adjacency := by
  rw [cookLevinAdjacencyPostRow_eq_mlProj_satSignedCrossAtom
    M n hn2 htb hns D i hi hab]
  rw [mlProj_one_mul_iterDerivList_nil_satSignedCrossAtom_one
    M n hn2 htb hns i ⟨i.val + 1, hi⟩
    (adjacency_consecutive_endpoints_ne i hi)]
  exact rename_adjacencyEndpointCollapseMap_satSignedCrossAtom_one_mem_shiftAugmentedInterfaceSpace
    M n hn2 htb hns B κ ℓ i ⟨i.val + 1, hi⟩
    (adjacency_consecutive_endpoints_ne i hi)

/-! ## Axiom audit anchors -/

#print axioms canonicalAdjacencyPostRow_mem_shiftAugmentedInterfaceSpace
#print axioms rename_adjacencyEndpointCollapseMap_satSignedCrossAtom_one_eq_canonical
#print axioms cookLevinAdjacencyPostRow_eq_mlProj_satSignedCrossAtom
#print axioms rename_adjacencyEndpointCollapseMap_cookLevinAdjacencyPostRow_mem_shiftAugmentedInterfaceSpace

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
