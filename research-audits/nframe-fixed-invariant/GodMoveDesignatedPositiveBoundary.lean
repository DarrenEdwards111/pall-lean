import GodMoveDesignatedComplementRows
import GodMoveExpanderPositiveProjection
import GodMoveSATDesignatedExtraction
import GodMoveRamanujanCalibration

/-!
# Positive boundary coordinates for the actual designated sheet

Complementing the projected derivative rows of the actual booleanity-factor
product exposes a coefficient identity minor.  Thus the positive boundary
map can act on these designated-sheet rows directly, with no assumed rank
certificate or inverse Gram matrix.  This is a map of coefficient vectors;
no general invariance of SPDP rank under variable mixing is asserted.

The full k-subset derivative family is independent after mapping. Membership
in a specified blocked SPDP space additionally requires block admissibility,
as recorded separately below; all subsets are admissible for discrete blocks.

The boundary must have at least the dimension of the preserved minor.  This
construction does not provide a polynomial-dimensional encoding or a SAT
runtime bound.
-/

namespace GodMoveDesignatedPositiveBoundary

open MvPolynomial SPDP MultilinearSPDP SymmetricPower
open GodMoveMonomialMinor GodMoveQuadraticSheetLift
open GodMoveDesignatedComplementRows GodMoveExpanderPositiveProjection
open GodMovePositiveBoundaryMap GodMoveSATDesignatedExtraction
open GodMoveSATUnitExtraction GodMoveUnitCharacteristic GodMoveMachineSourceMinor
open GodMoveMachineFaceExtraction
open PallLean.Paper93.DeepMath.PathB ComposableMachine SeparationTarget
open Step4Compiler.Step252
open scoped BigOperators

variable {m k : ℕ}
variable {Edge : Type*} [Fintype Edge] [DecidableEq Edge]

/-- Equal-cardinality complementary squarefree columns are incomparable
unless their index sets agree. -/
theorem complementaryColumn_le_iff_of_card_eq (S T : Finset (Fin m))
    (hcard : S.card = T.card) :
    complementaryColumn S ≤ complementaryColumn T ↔ S = T := by
  constructor
  · intro h
    have hsub : T ⊆ S := by
      intro i hi
      by_contra hn
      have hh := h i
      simp [complementaryColumn, tagMonomial_apply, hi, hn] at hh
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  · rintro rfl
    exact le_rfl

/-- Multiplication by a complementary monomial cannot create another
same-cardinality complementary column. Its diagonal is the constant term. -/
theorem coefficient_mul_derivativeRow (S T : Finset (Fin m))
    (hcard : S.card = T.card) (p : GodMoveMonomialMinor.Poly m) :
    coeff (complementaryColumn T) (p * derivativeRow S) =
      if T = S then constantCoeff p else 0 := by
  classical
  rw [derivativeRow_eq_monomial, coeff_mul_monomial']
  simp only [complementaryColumn_le_iff_of_card_eq S T hcard]
  by_cases h : S = T
  · subst T
    simp [constantCoeff_eq]
  · simp [h, Ne.symm h]

/-- Actual zero-shift projected derivative rows of the booleanity product. -/
noncomputable def qRow (S : Finset (Fin m)) : GodMoveMonomialMinor.Poly m :=
  mlProj (boolFactorDerivProd S)

/-- A row belongs to a specified blocked space only when its derivative list
is admissible for that partition. The zero shift fits every shift allowance. -/
theorem qRow_mem_strict (B : BlockPartition m) (S : KSubset m k) (ell : ℕ)
    (hS : isBlockAdmissible B S.val.toList) :
    qRow S.val ∈ mlBlockedSpdpSubspace B k ell (boolFactorFullProd m) := by
  apply Submodule.subset_span
  refine ⟨S.val.toList, (1 : GodMoveMonomialMinor.Poly m), ?_, by simp, by simp,
    hS, ?_⟩
  · simpa using kSubset_size S
  · simp [qRow, boolFactorDerivProd_eq_iterDerivList]

/-- Affine complementation exposes an actual identity minor in these rows. -/
theorem complemented_qRow_coefficient (S T : Finset (Fin m))
    (hcard : S.card = T.card) :
    coeff (complementaryColumn T) (affineComplement m (qRow S)) =
      if T = S then 1 else 0 := by
  classical
  rw [qRow, complemented_qRow_factorization, coefficient_mul_derivativeRow S T hcard]
  simp only [map_prod, map_sub, map_one, map_mul, constantCoeff_X,
    mul_zero, sub_zero, Finset.prod_const_one]

/-- The boundary first complements a row, then reads and mixes its selected
coefficients using the positive external matrix. -/
noncomputable def designatedBoundary (G : TseitinGraph (Fin m) Edge)
    (erased : Finset Edge) (q : ℕ) :
    GodMoveMonomialMinor.Poly m →ₗ[ℚ] (Fin q → ℚ) :=
  coefficientBoundary (k := k) G erased q ∘ₗ (affineComplement m).toLinearMap

theorem designatedBoundary_qRow_eq_derivativeRow
    (G : TseitinGraph (Fin m) Edge) (erased : Finset Edge) (q : ℕ)
    (T : KSubset m k) :
    designatedBoundary (k := k) G erased q (qRow T.val) =
      coefficientBoundary (k := k) G erased q (derivativeRow T.val) := by
  classical
  ext j
  change (∑ S : KSubset m k,
      coeff (complementaryColumn S.val) (affineComplement m (qRow T.val)) * _) =
    ∑ S : KSubset m k, coeff (complementaryColumn S.val) (derivativeRow T.val) * _
  apply Finset.sum_congr rfl
  intro S _
  rw [complemented_qRow_coefficient T.val S.val
    ((kSubset_size T).trans (kSubset_size S).symm), coefficient_identity]

/-- These actual designated rows map to the same distinct Vandermonde rows. -/
theorem designatedBoundary_qRow (G : TseitinGraph (Fin m) Edge)
    (erased : Finset Edge) (q : ℕ) (T : KSubset m k) :
    designatedBoundary (k := k) G erased q (qRow T.val) =
      boundaryMatrix (Fintype.card (Screen erased)) q (screenLabel G erased T) := by
  rw [designatedBoundary_qRow_eq_derivativeRow, coefficientBoundary_derivativeRow]

theorem boundary_qRows_linearIndependent (G : TseitinGraph (Fin m) Edge) {c q : ℕ}
    (hexp : G.HasExpansion c) (hwindow : 4 * k ≤ m)
    (erased : Finset Edge) (herased : erased.card < 2 * c)
    (hcapacity : Nat.choose m k ≤ q) :
    LinearIndependent ℚ (fun S : KSubset m k =>
      designatedBoundary (k := k) G erased q (qRow S.val)) := by
  simp only [designatedBoundary_qRow_eq_derivativeRow]
  exact boundary_derivativeRows_linearIndependent G hexp hwindow erased herased hcapacity

/-- Every injectively indexed admissible subfamily survives the same boundary.
This applies to a production partition's chosen minor without asserting that
all k-subsets are admissible for that partition. -/
theorem admissible_subfamily_boundary_certificate {ι : Type*}
    (B : BlockPartition m) (ell : ℕ)
    (G : TseitinGraph (Fin m) Edge) {c q : ℕ}
    (hexp : G.HasExpansion c) (hwindow : 4 * k ≤ m)
    (erased : Finset Edge) (herased : erased.card < 2 * c)
    (hcapacity : Nat.choose m k ≤ q)
    (f : ι → KSubset m k) (hf : Function.Injective f)
    (hadm : ∀ i, isBlockAdmissible B (f i).val.toList) :
    (∀ i, qRow (f i).val ∈ mlBlockedSpdpSubspace B k ell (boolFactorFullProd m)) ∧
      LinearIndependent ℚ (fun i =>
        designatedBoundary (k := k) G erased q (qRow (f i).val)) := by
  exact ⟨fun i => qRow_mem_strict B (f i) ell (hadm i),
    (boundary_qRows_linearIndependent G hexp hwindow erased herased hcapacity).comp f hf⟩

/-- A concrete nonvacuous instance: the four singleton derivatives of the
four-variable sheet survive erasure of any three K4 edges and map to four
independent boundary vectors. This is the same K4 with proved spectrum. -/
theorem K4_boundary_qRows_linearIndependent (erased : Finset (Fin 6))
    (herased : erased.card < 4) :
    LinearIndependent ℚ (fun S : KSubset 4 1 =>
      designatedBoundary (k := 1) K4 erased 4 (qRow S.val)) := by
  exact boundary_qRows_linearIndependent K4
    GodMoveRamanujanCalibration.K4_spectral_and_expansion.1
    (by decide) erased herased (by decide)

/-- The positive boundary theorem applies to the actual production sheet,
using its proved identity. This asserts independence of the derivative
family; membership in its coupled partition requires admissibility. -/
theorem designated_sheet_boundary_rows_linearIndependent
    (D : TuringMachine.DTM) (n : ℕ) (hn2 : 2 ≤ n)
    (htb : D.timeBound ≤ 4) (hns : D.numStates ≤ n)
    (B : BlockPartition (PaperFaithfulCompilation.cookLevinUVSplit D n).total)
    (G : TseitinGraph (Fin (n / 3)) Edge) {c q : ℕ}
    (hexp : G.HasExpansion c) (hwindow : 4 * k ≤ n / 3)
    (erased : Finset Edge) (herased : erased.card < 2 * c)
    (hcapacity : Nat.choose (n / 3) k ≤ q) :
    LinearIndependent ℚ (fun S : KSubset (n / 3) k =>
      designatedBoundary (k := k) G erased q
        (mlProj (iterDerivList S.val.toList
          (cookLevinStrictFOBTarget D n hn2 htb hns B).coupledPoly))) := by
  rw [designated_sheet_eq_boolFactorFullProd]
  simpa only [qRow, boolFactorDerivProd_eq_iterDerivList] using
    boundary_qRows_linearIndependent G hexp hwindow erased herased hcapacity

/-- Faithful SAT correctness yields these rows through the existing exact
sheet extraction. No runtime or rank upper bound is assumed or concluded. -/
theorem sat_extracted_sheet_boundary_rows_linearIndependent
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) (n : ℕ)
    (G : TseitinGraph (Fin (n / 3)) Edge) {c q : ℕ}
    (hexp : G.HasExpansion c) (hwindow : 4 * k ≤ n / 3)
    (erased : Finset Edge) (herased : erased.card < 2 * c)
    (hcapacity : Nat.choose (n / 3) k ≤ q) :
    LinearIndependent ℚ (fun S : KSubset (n / 3) k =>
      designatedBoundary (k := k) G erased q
        (mlProj (iterDerivList S.val.toList
          (sheetExtraction n
            (machineSource M T (unitFormula (n / 3)) (n / 3)))))) := by
  rw [sheetExtraction, AlgHom.comp_apply, unitExtraction_of_decides M T hD,
    quadraticLift_fullMonomial]
  simpa only [qRow, boolFactorDerivProd_eq_iterDerivList] using
    boundary_qRows_linearIndependent G hexp hwindow erased herased hcapacity

/-- Every linear boundary preserving these actual rows needs their full
binomial dimension, independently of expansion or positivity. -/
theorem faithful_designated_boundary_dimension {q : ℕ}
    (B : GodMoveMonomialMinor.Poly m →ₗ[ℚ] (Fin q → ℚ))
    (hB : LinearIndependent ℚ (fun S : KSubset m k => B (qRow S.val))) :
    Nat.choose m k ≤ q := by
  simpa only [kSubset_card, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using hB.fintype_card_le_finrank

end GodMoveDesignatedPositiveBoundary

#print axioms GodMoveDesignatedPositiveBoundary.complementaryColumn_le_iff_of_card_eq
#print axioms GodMoveDesignatedPositiveBoundary.coefficient_mul_derivativeRow
#print axioms GodMoveDesignatedPositiveBoundary.qRow_mem_strict
#print axioms GodMoveDesignatedPositiveBoundary.complemented_qRow_coefficient
#print axioms GodMoveDesignatedPositiveBoundary.designatedBoundary_qRow
#print axioms GodMoveDesignatedPositiveBoundary.boundary_qRows_linearIndependent
#print axioms GodMoveDesignatedPositiveBoundary.admissible_subfamily_boundary_certificate
#print axioms GodMoveDesignatedPositiveBoundary.K4_boundary_qRows_linearIndependent
#print axioms GodMoveDesignatedPositiveBoundary.designated_sheet_boundary_rows_linearIndependent
#print axioms GodMoveDesignatedPositiveBoundary.sat_extracted_sheet_boundary_rows_linearIndependent
#print axioms GodMoveDesignatedPositiveBoundary.faithful_designated_boundary_dimension
