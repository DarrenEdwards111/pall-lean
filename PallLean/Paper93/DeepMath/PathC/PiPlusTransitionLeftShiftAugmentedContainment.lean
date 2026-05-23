import PallLean.Paper93.DeepMath.PathC.PiPlusAdjacencyShiftAugmentedContainment

/-!
# Shift-augmented transition-left row containment

This is the transition-left analogue of the adjacency arity-5 row containment.
A transition skeleton factor has the signed-cross form `1 - c • X_a X_b`, with
`c = transCoeff M q`.  After endpoint collapse, the post-row is
`1 - c • X₀X₁`, which lies in the shift-augmented transition-left chart because
that chart contains both `1` and the endpoint-pair slot.
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

/-- The canonical coefficient-weighted transition-left row `1 - c • X₀X₁`
belongs to the shift-augmented transition-left interface chart. -/
theorem canonicalTransitionLeftPostRow_mem_shiftAugmentedInterfaceSpace
    {N : Nat} (B : BlockPartition N) (κ ℓ : Nat) (c : ℚ) :
    ((1 : MvPolynomial (Fin N) ℚ) - c • canonicalLocalEndpointPair) ∈
      shiftAugmentedInterfaceSpace_compiledBasis B κ ℓ ConstraintType.transitionLeft := by
  have hone := shiftAugmentedInterfacePolynomial_mem_shiftAugmentedInterfaceSpace
    B κ ℓ ConstraintType.transitionLeft shiftAugmentedConstSlot
  norm_num [shiftAugmentedInterfacePolynomial, shiftAugmentedConstSlot,
    shiftAugmentedLocalArity] at hone
  have hpair :=
    canonicalLocalEndpointPair_mem_shiftAugmentedInterfaceSpace_of_not_transitionRight
      B κ ℓ ConstraintType.transitionLeft (by simp)
  exact Submodule.sub_mem _ hone (Submodule.smul_mem _ c hpair)

/-- Under endpoint collapse, a flat signed cross atom becomes the canonical
coefficient-weighted row `1 - c • X₀X₁`. -/
theorem rename_adjacencyEndpointCollapseMap_satSignedCrossAtom_eq_canonical
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M n hn2 htb hns).numVars)
    (hab : a ≠ b) :
    MvPolynomial.rename
        (adjacencyEndpointCollapseMap a b (by
          simpa [PaperFaithfulSeparation.cook_levin_numVars] using hn2))
        (satSignedCrossAtom M n hn2 htb hns c a b) =
      ((1 : SATDeciderGaugeSpace M n hn2 htb hns) -
        c • canonicalLocalEndpointPair) := by
  have hN : 1 < (cook_levin_compilation M n hn2 htb hns).numVars := by
    simpa [PaperFaithfulSeparation.cook_levin_numVars] using hn2
  have hpos : 0 < (cook_levin_compilation M n hn2 htb hns).numVars :=
    lt_trans (by norm_num) hN
  unfold satSignedCrossAtom adjacencyEndpointCollapseMap canonicalLocalEndpointPair
  have hba : ¬ b = a := by
    intro h
    exact hab h.symm
  simp [MvPolynomial.rename_X, hba, canonicalLocalX, canonicalLocalX1, hN, hpos]

/-- Transported signed cross atom membership in the shift-augmented
transition-left interface chart. -/
theorem rename_adjacencyEndpointCollapseMap_satSignedCrossAtom_mem_transitionLeft_shiftAugmentedInterfaceSpace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat) (c : ℚ)
    (a b : Fin (cook_levin_compilation M n hn2 htb hns).numVars)
    (hab : a ≠ b) :
    MvPolynomial.rename
        (adjacencyEndpointCollapseMap a b (by
          simpa [PaperFaithfulSeparation.cook_levin_numVars] using hn2))
        (satSignedCrossAtom M n hn2 htb hns c a b) ∈
      shiftAugmentedInterfaceSpace_compiledBasis B κ ℓ ConstraintType.transitionLeft := by
  rw [rename_adjacencyEndpointCollapseMap_satSignedCrossAtom_eq_canonical
    M n hn2 htb hns c a b hab]
  exact canonicalTransitionLeftPostRow_mem_shiftAugmentedInterfaceSpace B κ ℓ c

/-- Concrete Cook--Levin transition-left post-row, before endpoint transport. -/
noncomputable def cookLevinTransitionLeftPostRow
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (q : Fin M.numStates) (i : Fin n) (hi : i.val + 1 < n) :
    SATDeciderGaugeSpace M n hn2 htb hns :=
  (piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
    (zeroProfileBooleanNormalize
      (piPlusSATBlockAlgEquiv M n hn2 htb hns D
        (((1 : MvPolynomial (Fin n) ℚ) - (transSkelLC M n q i hi).poly) :
          SATDeciderGaugeSpace M n hn2 htb hns)))

/-- If the transition endpoints are in distinct `Π+` blocks, the concrete
transition-left post-row is the corresponding signed-cross zero-derivative row. -/
theorem cookLevinTransitionLeftPostRow_eq_mlProj_satSignedCrossAtom
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (q : Fin M.numStates) (i : Fin n) (hi : i.val + 1 < n)
    (hab : (D.coord i).1 ≠ (D.coord ⟨i.val + 1, hi⟩).1) :
    cookLevinTransitionLeftPostRow M n hn2 htb hns D q i hi =
      mlProj
        ((1 : SATDeciderGaugeSpace M n hn2 htb hns) *
          SPDP.iterDerivList []
            (satSignedCrossAtom M n hn2 htb hns (transCoeff M q)
              i ⟨i.val + 1, hi⟩)) := by
  unfold cookLevinTransitionLeftPostRow
  rw [transitionFactor_eq_satSignedCrossAtom M n hn2 htb hns q i hi]
  exact (transitionFactor_signedCrossAtomRowCertificate_unconditional
    M n hn2 htb hns D q i hi hab).2

/-- The zero-derivative signed row simplifies to the signed atom, for arbitrary
coefficient `c`. -/
theorem mlProj_one_mul_iterDerivList_nil_satSignedCrossAtom
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M n hn2 htb hns).numVars)
    (hab : a ≠ b) :
    mlProj
        ((1 : SATDeciderGaugeSpace M n hn2 htb hns) *
          SPDP.iterDerivList []
            (satSignedCrossAtom M n hn2 htb hns c a b)) =
      satSignedCrossAtom M n hn2 htb hns c a b := by
  unfold satSignedCrossAtom
  simp
  have hmul :
      mlProj (X a * X b : SATDeciderGaugeSpace M n hn2 htb hns) =
        (X a * X b : SATDeciderGaugeSpace M n hn2 htb hns) :=
    mlProj_X_mul_X_ne
      (σ := Fin (cook_levin_compilation M n hn2 htb hns).numVars)
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
      mlProj (-(c • (X a * X b : SATDeciderGaugeSpace M n hn2 htb hns))) =
        -(c • (X a * X b : SATDeciderGaugeSpace M n hn2 htb hns)) := by
    rw [← neg_one_smul ℚ (c • (X a * X b : SATDeciderGaugeSpace M n hn2 htb hns)),
      mlProj_smul, mlProj_smul, hmul]
  rw [hone, hneg]

/-- Main transition-left per-row containment: after endpoint collapse, each
concrete transition-left post-row lies in the arity-5 shift-augmented
transition-left chart. -/
theorem rename_adjacencyEndpointCollapseMap_cookLevinTransitionLeftPostRow_mem_shiftAugmentedInterfaceSpace
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
      shiftAugmentedInterfaceSpace_compiledBasis B κ ℓ ConstraintType.transitionLeft := by
  rw [cookLevinTransitionLeftPostRow_eq_mlProj_satSignedCrossAtom
    M n hn2 htb hns D q i hi hab]
  rw [mlProj_one_mul_iterDerivList_nil_satSignedCrossAtom
    M n hn2 htb hns (transCoeff M q) i ⟨i.val + 1, hi⟩
    (adjacency_consecutive_endpoints_ne i hi)]
  exact rename_adjacencyEndpointCollapseMap_satSignedCrossAtom_mem_transitionLeft_shiftAugmentedInterfaceSpace
    M n hn2 htb hns B κ ℓ (transCoeff M q) i ⟨i.val + 1, hi⟩
    (adjacency_consecutive_endpoints_ne i hi)

/-! ## Axiom audit anchors -/

#print axioms canonicalTransitionLeftPostRow_mem_shiftAugmentedInterfaceSpace
#print axioms rename_adjacencyEndpointCollapseMap_satSignedCrossAtom_eq_canonical
#print axioms cookLevinTransitionLeftPostRow_eq_mlProj_satSignedCrossAtom
#print axioms rename_adjacencyEndpointCollapseMap_cookLevinTransitionLeftPostRow_mem_shiftAugmentedInterfaceSpace

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
