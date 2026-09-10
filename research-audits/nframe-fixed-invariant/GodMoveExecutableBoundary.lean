import GodMoveExecutableScreen
import GodMoveDesignatedPositiveBoundary

/-!
# Positive boundary entries from directly computed expander codes

An entry is obtained by computing one screen's binary code and raising its
successor to the requested power. No screen-type enumeration occurs in this
algorithm. The resulting rows are rows of the already proved positive moment
matrix, so expansion gives their independence with the same explicit boundary
capacity. Coefficient identities connect them to both the unit monomial and
the actual nonmultilinear designated sheet extracted from a faithful SAT source.

The finite coefficient maps still sum over all choose(m,k) labels, and their
polynomial operations remain noncomputable here. Per-entry execution does not
give polynomial-time normalization, full boundary output, or SAT separation.
-/

namespace GodMoveExecutableBoundary

open MvPolynomial SPDP MultilinearSPDP SymmetricPower
open GodMoveMonomialMinor GodMoveExecutableScreen GodMovePositiveBoundaryMap
open GodMoveDesignatedPositiveBoundary GodMoveQuadraticSheetLift
open GodMoveSATUnitExtraction GodMoveSATDesignatedExtraction GodMoveUnitCharacteristic
open GodMoveMachineFaceExtraction
open PallLean.Paper93.DeepMath.PathB ComposableMachine SeparationTarget
open Step4Compiler.Step252
open scoped BigOperators

variable {m E k : ℕ}

/-- One executable integer entry: direct binary screen code, successor, power. -/
def entryNat (G : TseitinGraph (Fin m) (Fin E)) (erased : Finset (Fin E))
    (S : Finset (Fin m)) (j : ℕ) : ℕ :=
  ((screenCode G erased S).val + 1) ^ j

/-- The same exactly represented integer as a rational moment-matrix entry. -/
def entry (G : TseitinGraph (Fin m) (Fin E)) (erased : Finset (Fin E))
    (S : Finset (Fin m)) (j : ℕ) : ℚ :=
  (entryNat G erased S j : ℚ)

/-- An entry has magnitude at most 2^(E*j); this accounts for growing precision. -/
theorem entryNat_le (G : TseitinGraph (Fin m) (Fin E)) (erased : Finset (Fin E))
    (S : Finset (Fin m)) (j : ℕ) : entryNat G erased S j ≤ 2 ^ (E * j) := by
  have hcode := (screenCode G erased S).isLt
  exact (Nat.pow_le_pow_left (by omega : (screenCode G erased S).val + 1 ≤ 2 ^ E) j).trans
    (by rw [pow_mul])

theorem entry_eq_boundaryMatrix (G : TseitinGraph (Fin m) (Fin E))
    (erased : Finset (Fin E)) (q : ℕ) (S : KSubset m k) :
    (fun j : Fin q => entry G erased S.val j.val) =
      boundaryMatrix (2 ^ E) q (executableScreenLabel G erased S) := by
  ext j
  simp [entry, entryNat, boundaryMatrix, node, executableScreenLabel]

/-- The computed entries preserve the selected minor when its dimension fits. -/
theorem entry_rows_linearIndependent (G : TseitinGraph (Fin m) (Fin E)) {c q : ℕ}
    (hexp : G.HasExpansion c) (hwindow : 4 * k ≤ m)
    (erased : Finset (Fin E)) (herased : erased.card < 2 * c)
    (hcapacity : Nat.choose m k ≤ q) :
    LinearIndependent ℚ (fun S : KSubset m k =>
      (fun j : Fin q => entry G erased S.val j.val)) := by
  classical
  let e := Fintype.equivFin (KSubset m k)
  have hi := (executableScreenLabel_injective G hexp hwindow erased herased).comp
    e.symm.injective
  have hli := selected_rows_linearIndependent
    (fun i => executableScreenLabel G erased (e.symm i)) hi
    (by simpa only [kSubset_card] using hcapacity)
  have hrows : (fun S : KSubset m k => (fun j : Fin q => entry G erased S.val j.val)) =
      (fun S : KSubset m k => boundaryMatrix (2 ^ E) q (executableScreenLabel G erased S)) :=
    funext (fun S => entry_eq_boundaryMatrix G erased q S)
  rw [hrows]
  simpa only [Function.comp_def, e.symm_apply_apply] using hli.comp e e.injective

/-- This finite linear map uses direct per-label entries. Its sum still ranges
over all binomially many derivative labels. -/
noncomputable def coefficientBoundary (G : TseitinGraph (Fin m) (Fin E))
    (erased : Finset (Fin E)) (q : ℕ) :
    GodMoveMonomialMinor.Poly m →ₗ[ℚ] (Fin q → ℚ) where
  toFun p j := ∑ S : KSubset m k,
    coeff (complementaryColumn S.val) p * entry G erased S.val j.val
  map_add' p p' := by
    ext j
    simp only [coeff_add, add_mul, Finset.sum_add_distrib, Pi.add_apply]
  map_smul' a p := by
    ext j
    simp only [coeff_smul, smul_eq_mul, Pi.smul_apply, Finset.mul_sum, mul_assoc,
      RingHom.id_apply]

theorem coefficientBoundary_derivativeRow (G : TseitinGraph (Fin m) (Fin E))
    (erased : Finset (Fin E)) (q : ℕ) (T : KSubset m k) :
    coefficientBoundary (k := k) G erased q (derivativeRow T.val) =
      (fun j : Fin q => entry G erased T.val j.val) := by
  classical
  ext j
  simp [coefficientBoundary, coefficient_identity]

/-- Affine complementation exposes the already proved designated-sheet duals. -/
noncomputable def designatedBoundary (G : TseitinGraph (Fin m) (Fin E))
    (erased : Finset (Fin E)) (q : ℕ) :
    GodMoveMonomialMinor.Poly m →ₗ[ℚ] (Fin q → ℚ) :=
  coefficientBoundary (k := k) G erased q ∘ₗ (affineComplement m).toLinearMap

/-- An actual projected derivative of the nonmultilinear sheet has precisely
the directly computed positive row as its image. -/
theorem designatedBoundary_qRow (G : TseitinGraph (Fin m) (Fin E))
    (erased : Finset (Fin E)) (q : ℕ) (T : KSubset m k) :
    designatedBoundary (k := k) G erased q (qRow T.val) =
      (fun j : Fin q => entry G erased T.val j.val) := by
  classical
  ext j
  change (∑ S : KSubset m k,
    coeff (complementaryColumn S.val) (affineComplement m (qRow T.val)) *
      entry G erased S.val j.val) = entry G erased T.val j.val
  have hc (S : KSubset m k) := complemented_qRow_coefficient T.val S.val
    ((kSubset_size T).trans (kSubset_size S).symm)
  simp only [hc]
  have heq (S : KSubset m k) : S.val = T.val ↔ S = T := Subtype.ext_iff.symm
  simp only [heq]
  simp

theorem boundary_qRows_linearIndependent (G : TseitinGraph (Fin m) (Fin E)) {c q : ℕ}
    (hexp : G.HasExpansion c) (hwindow : 4 * k ≤ m)
    (erased : Finset (Fin E)) (herased : erased.card < 2 * c)
    (hcapacity : Nat.choose m k ≤ q) :
    LinearIndependent ℚ (fun S : KSubset m k =>
      designatedBoundary (k := k) G erased q (qRow S.val)) := by
  simp only [designatedBoundary_qRow]
  exact entry_rows_linearIndependent G hexp hwindow erased herased hcapacity

/-- The actual production sheet supplies these rows, with no replacement by
its Boolean normalization and no additional preservation assumption. -/
theorem designated_sheet_boundary_rows_linearIndependent
    (D : TuringMachine.DTM) (n : ℕ) (hn2 : 2 ≤ n)
    (htb : D.timeBound ≤ 4) (hns : D.numStates ≤ n)
    (B : BlockPartition (PaperFaithfulCompilation.cookLevinUVSplit D n).total)
    (G : TseitinGraph (Fin (n / 3)) (Fin E)) {c q : ℕ}
    (hexp : G.HasExpansion c) (hwindow : 4 * k ≤ n / 3)
    (erased : Finset (Fin E)) (herased : erased.card < 2 * c)
    (hcapacity : Nat.choose (n / 3) k ≤ q) :
    LinearIndependent ℚ (fun S : KSubset (n / 3) k =>
      designatedBoundary (k := k) G erased q
        (mlProj (iterDerivList S.val.toList
          (cookLevinStrictFOBTarget D n hn2 htb hns B).coupledPoly))) := by
  rw [designated_sheet_eq_boolFactorFullProd]
  simpa only [qRow, boolFactorDerivProd_eq_iterDerivList] using
    boundary_qRows_linearIndependent G hexp hwindow erased herased hcapacity

/-- The exact faithful SAT-source extraction is compatible with the computed
screen entries. Full source normalization and full boundary evaluation remain
separate, unproved efficiency requirements. -/
theorem sat_extracted_sheet_boundary_rows_linearIndependent
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) (n : ℕ)
    (G : TseitinGraph (Fin (n / 3)) (Fin E)) {c q : ℕ}
    (hexp : G.HasExpansion c) (hwindow : 4 * k ≤ n / 3)
    (erased : Finset (Fin E)) (herased : erased.card < 2 * c)
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

/-- Executable rational-entry checks are also verified by kernel reduction. -/
theorem K4_entry_checks :
    entry K4 ∅ {0} 3 = 512 ∧ entry K4 {0, 1, 2} {1} 3 = 15625 := by decide

#eval entry K4 ∅ {0} 3
#eval entry K4 {0, 1, 2} {1} 3

end GodMoveExecutableBoundary

#print axioms GodMoveExecutableBoundary.entryNat_le
#print axioms GodMoveExecutableBoundary.entry_eq_boundaryMatrix
#print axioms GodMoveExecutableBoundary.entry_rows_linearIndependent
#print axioms GodMoveExecutableBoundary.coefficientBoundary_derivativeRow
#print axioms GodMoveExecutableBoundary.designatedBoundary_qRow
#print axioms GodMoveExecutableBoundary.boundary_qRows_linearIndependent
#print axioms GodMoveExecutableBoundary.designated_sheet_boundary_rows_linearIndependent
#print axioms GodMoveExecutableBoundary.sat_extracted_sheet_boundary_rows_linearIndependent
#print axioms GodMoveExecutableBoundary.K4_entry_checks
