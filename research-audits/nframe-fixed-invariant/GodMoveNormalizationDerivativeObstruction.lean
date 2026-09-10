import GodMoveCircuitNormalization
import GodMoveCircuitArithmetization
import GodMoveMonomialMinor

/-!
# Boolean normalization can increase the actual projected derivative rank

The three-gate Boolean circuit `x; x AND x; (x AND x) AND x` arithmetizes
to `x^3`, while its Boolean normal form is `x`. Before normalization, its
zeroth and first derivatives contain only powers at least two, so multilinear
coefficient filtering kills every zero-shift row. After normalization the
first derivative is one. Thus normalization strictly increases both the
strict and inclusive existing SPDP ranks at one derivative and zero shift.

This also separates applying a linear map to an already-formed row space
from recomputing derivatives after applying that map to its source polynomial.
Linearity alone provides no rank-monotonicity theorem for the latter.
No universal obstruction to other invariants or restricted transport is claimed.
-/

namespace GodMoveNormalizationDerivativeObstruction

open MvPolynomial SPDP MultilinearSPDP
open GodMoveBooleanInterpolation GodMoveCircuitNormalization
open GodMoveCircuitArithmetization
open GodMoveMonomialMinor (discreteBlocks)
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer (CGate)

abbrev P := Poly 1

noncomputable def cubic : P := X 0 ^ 3

/-- Reusing the first wire twice and then rereading it is legal DAG sharing. -/
def cubeCircuit : List (CGate 1) :=
  [.var 0, .bin (· && ·) 0 0, .bin (· && ·) 1 0]

theorem rawPoly_cubeCircuit : rawPoly cubeCircuit = cubic := by
  simp [rawPoly, cubeCircuit, compile, runArithmetic, arithGate, select,
    AExpr.eval, cubic, pow_succ]
  ring

theorem normalize_cubic : normalize cubic = (X 0 : P) := by
  rw [cubic, X_pow_eq_monomial, normalize_monomial]
  change monomial _ (1 : ℚ) = monomial (Finsupp.single 0 1) 1
  apply congrArg (fun α : Fin 1 →₀ ℕ => monomial α (1 : ℚ))
  apply Finsupp.ext
  intro i
  fin_cases i
  norm_num [SymmetricPower.tagMonomial_apply]

theorem derivative_cubic : pderiv (0 : Fin 1) cubic =
    monomial (Finsupp.single 0 2) (3 : ℚ) := by
  rw [cubic, X_pow_eq_monomial, pderiv_monomial_single]
  norm_num

theorem normalization_derivative_ne :
    pderiv (0 : Fin 1) (normalize cubic) ≠
      normalize (pderiv (0 : Fin 1) cubic) := by
  intro h
  have heval := congrArg (MvPolynomial.eval (fun _ : Fin 1 => (1 : ℚ))) h
  rw [normalize_cubic, pderiv_X_self, derivative_cubic, normalize_monomial] at heval
  norm_num [eval_monomial, Finsupp.prod] at heval

private theorem project_constant_times_power_eq_zero (c : ℚ) (k : ℕ) (hk : 1 < k) :
    mlProj ((C c : P) * monomial (Finsupp.single 0 k) (1 : ℚ)) = 0 := by
  rw [C_mul_monomial, mul_one, mlProj_monomial]
  have hnot : ¬ Finsupp.IsMultilinear (Finsupp.single (0 : Fin 1) k) := by
    intro h
    have hi := h 0
    simpa using (not_le_of_gt hk) (by simpa using hi)
  rw [if_neg hnot]

private theorem project_constant_times_derivative_eq_zero (c : ℚ) :
    mlProj ((C c : P) * pderiv (0 : Fin 1) cubic) = 0 := by
  rw [derivative_cubic, C_mul_monomial, mlProj_monomial]
  have hnot : ¬ Finsupp.IsMultilinear (Finsupp.single (0 : Fin 1) 2) := by
    intro h
    have hi := h 0
    norm_num at hi
  rw [if_neg hnot]

/-- Every zero-shift row of order zero or one is killed by `mlProj`. -/
theorem raw_inclusive_subspace_eq_bot :
    mlBlockedSpdpSubspaceInc (discreteBlocks 1) 1 0 cubic = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro q ⟨S, m, hlen, hdeg, _, _, rfl⟩
    have hm := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hdeg)
    rw [hm]
    cases S with
    | nil =>
        simp only [iterDerivList, List.foldl_nil]
        rw [cubic, X_pow_eq_monomial, project_constant_times_power_eq_zero _ 3 (by decide)]
        exact Submodule.zero_mem _
    | cons i is =>
        have his : is = [] := List.length_eq_zero_iff.mp (by
          simp only [List.length_cons] at hlen
          omega)
        subst is
        have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
        subst i
        simp only [iterDerivList, List.foldl_cons, List.foldl_nil]
        rw [project_constant_times_derivative_eq_zero]
        exact Submodule.zero_mem _
  · exact bot_le

theorem raw_strict_rank_zero : mlBlockedSpdpRank (discreteBlocks 1) 1 0 cubic = 0 := by
  have hsub : mlBlockedSpdpSubspace (discreteBlocks 1) 1 0 cubic = ⊥ :=
    le_bot_iff.mp (by
      rw [← raw_inclusive_subspace_eq_bot]
      exact mlBlockedSpdpSubspace_le_inc _ _ _ _)
  simp [mlBlockedSpdpRank, hsub]

theorem raw_inclusive_rank_zero :
    mlBlockedSpdpRankInc (discreteBlocks 1) 1 0 cubic = 0 := by
  simp [mlBlockedSpdpRankInc, raw_inclusive_subspace_eq_bot]

theorem one_mem_normalized_strict_subspace :
    (1 : P) ∈ mlBlockedSpdpSubspace (discreteBlocks 1) 1 0 (normalize cubic) := by
  rw [normalize_cubic]
  apply Submodule.subset_span
  refine ⟨[0], (1 : P), rfl, by simp, by simp, ?_, ?_⟩
  · constructor
    · simp
    · intro b
      fin_cases b
      simp [discreteBlocks]
  · simp only [iterDerivList, List.foldl_cons, List.foldl_nil, pderiv_X_self, one_mul]
    symm
    apply mlProj_of_isMultilinear
    intro α hα i
    have hα0 : α = 0 := by simpa [MvPolynomial.coeff_one, eq_comm] using hα
    simp [hα0]

theorem normalized_strict_rank_pos :
    0 < mlBlockedSpdpRank (discreteBlocks 1) 1 0 (normalize cubic) := by
  unfold mlBlockedSpdpRank
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨1, one_mem_normalized_strict_subspace⟩, ?_⟩
  intro h
  exact one_ne_zero (congrArg Subtype.val h)

theorem normalization_increases_strict_rank :
    mlBlockedSpdpRank (discreteBlocks 1) 1 0 (rawPoly cubeCircuit) <
      mlBlockedSpdpRank (discreteBlocks 1) 1 0 (normalize (rawPoly cubeCircuit)) := by
  rw [rawPoly_cubeCircuit, raw_strict_rank_zero]
  exact normalized_strict_rank_pos

theorem normalization_increases_inclusive_rank :
    mlBlockedSpdpRankInc (discreteBlocks 1) 1 0 (rawPoly cubeCircuit) <
      mlBlockedSpdpRankInc (discreteBlocks 1) 1 0 (normalize (rawPoly cubeCircuit)) := by
  rw [rawPoly_cubeCircuit, raw_inclusive_rank_zero]
  exact normalized_strict_rank_pos.trans_le (Submodule.finrank_mono
    (mlBlockedSpdpSubspace_le_inc _ _ _ _))

end GodMoveNormalizationDerivativeObstruction

#print axioms GodMoveNormalizationDerivativeObstruction.rawPoly_cubeCircuit
#print axioms GodMoveNormalizationDerivativeObstruction.normalize_cubic
#print axioms GodMoveNormalizationDerivativeObstruction.normalization_derivative_ne
#print axioms GodMoveNormalizationDerivativeObstruction.raw_strict_rank_zero
#print axioms GodMoveNormalizationDerivativeObstruction.raw_inclusive_rank_zero
#print axioms GodMoveNormalizationDerivativeObstruction.normalization_increases_strict_rank
#print axioms GodMoveNormalizationDerivativeObstruction.normalization_increases_inclusive_rank
