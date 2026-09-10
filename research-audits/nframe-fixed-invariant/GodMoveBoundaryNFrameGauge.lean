import GodMoveDesignatedPositiveBoundary
import PallLean.Paper93.Concrete.FullLagrangianFixed

/-!
# The retained designated rows in the actual production N-Frame gauge

The concrete coefficient duals already exposed by the positive-boundary
construction define a projection onto exactly the designated derivative-row
span. Idempotence, finite range, and rank are derived from that coefficient
identity, without selecting an arbitrary complementary space. The resulting
object inhabits the unchanged production `ObserverGauge` type.

The permitted coordinate field is zero, so the unchanged production action is
exactly β r + γ/(1+r), where r = choose(m,k). This is a representation bridge,
not a claim that the gauge is a production minimizer, is found by a fast SAT
machine, or has polynomial rank. The explicit sum has r terms. No construction
runtime lower bound is inferred from the dimension of a semantic range.
-/

namespace GodMoveBoundaryNFrameGauge

open MvPolynomial MultilinearSPDP SymmetricPower
open GodMoveMonomialMinor GodMoveQuadraticSheetLift GodMoveDesignatedPositiveBoundary
open GodMoveSATDesignatedExtraction GodMoveSATUnitExtraction GodMoveUnitCharacteristic
open GodMoveMachineFaceExtraction
open PallLean.Paper93.NFrame PallLean.Paper93.Concrete
open PallLean.Paper93.DeepMath.PathB ComposableMachine SeparationTarget
open Step4Compiler.Step252
open scoped BigOperators

abbrev Poly (n : ℕ) := MvPolynomial (Fin n) ℚ

variable (m k : ℕ)

/-- The actual coefficient duals of the designated derivative rows. -/
noncomputable def rowCoordinates : Poly m →ₗ[ℚ] (KSubset m k → ℚ) where
  toFun p S := coeff (complementaryColumn S.val) (affineComplement m p)
  map_add' p p' := by ext S; simp
  map_smul' a p := by ext S; simp

/-- Reconstruct a polynomial in the retained designated derivative-row span. -/
noncomputable def rowSynthesis : (KSubset m k → ℚ) →ₗ[ℚ] Poly m where
  toFun a := ∑ S, a S • qRow S.val
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a b := by simp [Finset.smul_sum, smul_smul]

@[simp] theorem rowCoordinates_qRow (T : KSubset m k) :
    rowCoordinates m k (qRow T.val) = fun S => if S = T then 1 else 0 := by
  ext S
  simp only [rowCoordinates, LinearMap.coe_mk, AddHom.coe_mk,
    complemented_qRow_coefficient T.val S.val
      ((kSubset_size T).trans (kSubset_size S).symm)]
  simp

@[simp] theorem coordinates_synthesis (a : KSubset m k → ℚ) :
    rowCoordinates m k (rowSynthesis m k a) = a := by
  classical
  ext T
  simp [rowSynthesis, map_sum, rowCoordinates_qRow]

theorem rowSynthesis_injective : Function.Injective (rowSynthesis m k) := by
  intro a b h
  have := congrArg (rowCoordinates m k) h
  simpa using this

/-- Independence follows from the actual coefficient duality, without graph
expansion or a separate rank premise. -/
theorem qRows_linearIndependent :
    LinearIndependent ℚ (fun S : KSubset m k => qRow S.val) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  have h : rowSynthesis m k a = 0 := ha
  have hz : a = 0 := by
    have hc := congrArg (rowCoordinates m k) h
    simpa using hc
  exact congrFun hz i

/-- The projection is a finite, explicit sum of the proved coefficient duals. -/
noncomputable def rowProjection : Poly m →ₗ[ℚ] Poly m :=
  rowSynthesis m k ∘ₗ rowCoordinates m k

theorem rowProjection_idempotent :
    rowProjection m k ∘ₗ rowProjection m k = rowProjection m k := by
  ext p
  simp [rowProjection]

theorem rowProjection_range :
    LinearMap.range (rowProjection m k) = LinearMap.range (rowSynthesis m k) := by
  ext p
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨rowCoordinates m k p, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨rowSynthesis m k a, by simp [rowProjection]⟩

theorem rowProjection_rank :
    Module.finrank ℚ (LinearMap.range (rowProjection m k)) = Nat.choose m k := by
  rw [rowProjection_range, LinearMap.finrank_range_of_inj (rowSynthesis_injective m k)]
  simp

@[simp] theorem rowProjection_qRow (S : KSubset m k) :
    rowProjection m k (qRow S.val) = qRow S.val := by
  classical
  simp [rowProjection, rowCoordinates_qRow, rowSynthesis]

/-- A genuine gauge in the existing production type, with no changed fields. -/
noncomputable def boundaryGauge : ObserverGauge m where
  projection := rowProjection m k
  is_idempotent := rowProjection_idempotent m k
  rank_finite := by rw [rowProjection_range]; infer_instance
  coord := trivialCoord m

theorem boundaryGauge_admissible : AdmissibleGauge (boundaryGauge m k).toCandidateGauge :=
  ⟨0, (rowProjection m k).map_zero⟩

/-- The production projection rank is exactly the preserved minor dimension. -/
theorem boundaryGauge_rank :
    Module.finrank ℚ (LinearMap.range (boundaryGauge m k).projection) = Nat.choose m k :=
  rowProjection_rank m k

theorem boundaryGauge_fixes_qRow (S : KSubset m k) :
    (boundaryGauge m k).projection (qRow S.val) = qRow S.val :=
  rowProjection_qRow m k S

/-- The fixed vectors are derivative rows of the actual production target.
Blocked-space membership is governed separately by its partition. -/
theorem boundaryGauge_fixes_designated_sheet_row
    (D : TuringMachine.DTM) (n : ℕ) (hn2 : 2 ≤ n)
    (htb : D.timeBound ≤ 4) (hns : D.numStates ≤ n)
    (B : SPDP.BlockPartition (PaperFaithfulCompilation.cookLevinUVSplit D n).total)
    (S : KSubset (n / 3) k) :
    (boundaryGauge (n / 3) k).projection
        (mlProj (SPDP.iterDerivList S.val.toList
          (cookLevinStrictFOBTarget D n hn2 htb hns B).coupledPoly)) =
      mlProj (SPDP.iterDerivList S.val.toList
        (cookLevinStrictFOBTarget D n hn2 htb hns B).coupledPoly) := by
  rw [designated_sheet_eq_boolFactorFullProd]
  simpa only [qRow, boolFactorDerivProd_eq_iterDerivList] using
    boundaryGauge_fixes_qRow (n / 3) k S

/-- Faithful machine correctness yields the same fixed rows through the
previous exact sheet extraction, with no extra preservation premise. -/
theorem boundaryGauge_fixes_sat_extracted_row
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (n : ℕ) (S : KSubset (n / 3) k) :
    (boundaryGauge (n / 3) k).projection
        (mlProj (SPDP.iterDerivList S.val.toList
          (sheetExtraction n
            (machineSource M T (unitFormula (n / 3)) (n / 3))))) =
      mlProj (SPDP.iterDerivList S.val.toList
        (sheetExtraction n
          (machineSource M T (unitFormula (n / 3)) (n / 3)))) := by
  rw [sheetExtraction, AlgHom.comp_apply, unitExtraction_of_decides M T hD,
    quadraticLift_fullMonomial]
  simpa only [qRow, boolFactorDerivProd_eq_iterDerivList] using
    boundaryGauge_fixes_qRow (n / 3) k S

/-- The production gauge retains exactly the coefficient data used by the
actual positive boundary, on every input polynomial. -/
theorem boundaryGauge_preserves_designatedBoundary
    {Edge : Type*} [Fintype Edge] [DecidableEq Edge]
    (G : PallLean.Paper93.DeepMath.PathB.TseitinGraph (Fin m) Edge)
    (erased : Finset Edge) (q : ℕ) (p : Poly m) :
    designatedBoundary (k := k) G erased q ((boundaryGauge m k).projection p) =
      designatedBoundary (k := k) G erased q p := by
  ext j
  change (∑ S : KSubset m k,
      rowCoordinates m k (rowSynthesis m k (rowCoordinates m k p)) S * _) =
    ∑ S : KSubset m k, rowCoordinates m k p S * _
  rw [coordinates_synthesis]

/-- The unchanged production action, evaluated on this concrete gauge. -/
theorem boundaryGauge_action {d : ℕ} (G : RegularGraphFixed m d) (α β γ : ℝ) :
    fullLagrangianFixed α β γ G (boundaryGauge m k) =
      β * (Nat.choose m k : ℝ) + γ / (1 + (Nat.choose m k : ℝ)) := by
  simp [fullLagrangianFixed, logDetBarrier,
    boundaryGauge, trivialCoord, rowProjection_rank, div_eq_mul_inv]

theorem boundaryGauge_action_ge_rank_term {d : ℕ}
    (G : RegularGraphFixed m d) (α β γ : ℝ) (hγ : 0 ≤ γ) :
    β * (Nat.choose m k : ℝ) ≤ fullLagrangianFixed α β γ G (boundaryGauge m k) := by
  rw [boundaryGauge_action]
  have h : 0 ≤ γ / (1 + (Nat.choose m k : ℝ)) := div_nonneg hγ (by positivity)
  linarith

end GodMoveBoundaryNFrameGauge

#print axioms GodMoveBoundaryNFrameGauge.coordinates_synthesis
#print axioms GodMoveBoundaryNFrameGauge.qRows_linearIndependent
#print axioms GodMoveBoundaryNFrameGauge.rowProjection_idempotent
#print axioms GodMoveBoundaryNFrameGauge.rowProjection_range
#print axioms GodMoveBoundaryNFrameGauge.rowProjection_rank
#print axioms GodMoveBoundaryNFrameGauge.boundaryGauge_admissible
#print axioms GodMoveBoundaryNFrameGauge.boundaryGauge_rank
#print axioms GodMoveBoundaryNFrameGauge.boundaryGauge_fixes_qRow
#print axioms GodMoveBoundaryNFrameGauge.boundaryGauge_fixes_designated_sheet_row
#print axioms GodMoveBoundaryNFrameGauge.boundaryGauge_fixes_sat_extracted_row
#print axioms GodMoveBoundaryNFrameGauge.boundaryGauge_preserves_designatedBoundary
#print axioms GodMoveBoundaryNFrameGauge.boundaryGauge_action
#print axioms GodMoveBoundaryNFrameGauge.boundaryGauge_action_ge_rank_term
