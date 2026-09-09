import GodMoveFaithfulHandshake

/-!
# Exact evaluation of the characteristic target encodes model counting

At the all-half rational point, every Boolean delta-basis polynomial has
value `2^(-n)`. Hence exact evaluation of the canonical characteristic
polynomial, multiplied by `2^n`, is the number of satisfying `n`-bit
assignments. This is an algebraic reduction, not a machine-time theorem.

In particular, an alleged efficient exact extraction into an efficiently
evaluable representation must account for the counting information it
produces. No separation of counting from decision, no P-side rank bound,
and no lower bound on arbitrary extraction algorithms is asserted here.
-/

namespace GodMoveCharacteristicCounting

open MvPolynomial
open GodMoveBooleanInterpolation GodMovePinnedSATQueries GodMoveFaithfulHandshake
open PallLean.Paper93.DeepMath.PathB
open CookLevinReduction ComposableMachine SeparationTarget
open scoped BigOperators

/-- A concrete finite count, not an assumed counting oracle. -/
noncomputable def trueCount {n : ℕ} (f : Assignment n → Bool) : ℕ :=
  (Finset.univ.filter fun a => f a = true).card

noncomputable def satisfyingCount (n : ℕ) (φ : Formula) : ℕ :=
  trueCount (fun a : Assignment n => evalFormula (extendAssignment a) φ)

def halfPoint (n : ℕ) : Fin n → ℚ := fun _ => 1 / 2

theorem boolMonomial_eval_half {n : ℕ} (a : Assignment n) :
    MvPolynomial.eval (halfPoint n) (Step4Compiler.boolMonomial a) =
      (1 / 2 : ℚ) ^ n := by
  classical
  norm_num [Step4Compiler.boolMonomial, halfPoint, apply_ite]
  simp [one_div]

theorem interpolate_eval_half {n : ℕ} (f : Assignment n → Bool) :
    MvPolynomial.eval (halfPoint n) (interpolate f) =
      (trueCount f : ℚ) * (1 / 2 : ℚ) ^ n := by
  classical
  unfold interpolate Step4Compiler.chi_phi
  simp only [map_sum, apply_ite, map_zero, boolMonomial_eval_half]
  rw [← Finset.sum_filter]
  simp [trueCount]

/-- Exact midpoint evaluation recovers the complete finite truth count. -/
theorem trueCount_eq_scaled_eval {n : ℕ} (f : Assignment n → Bool) :
    (trueCount f : ℚ) =
      (2 : ℚ) ^ n * MvPolynomial.eval (halfPoint n) (interpolate f) := by
  rw [interpolate_eval_half]
  have hprod : (2 : ℚ) ^ n * (1 / 2 : ℚ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (trueCount f : ℚ) = (trueCount f : ℚ) * 1 := (mul_one _).symm
    _ = (trueCount f : ℚ) * ((2 : ℚ) ^ n * (1 / 2 : ℚ) ^ n) := by rw [hprod]
    _ = _ := by ring

theorem satisfyingCount_eq_scaled_characteristic_eval (n : ℕ) (φ : Formula) :
    (satisfyingCount n φ : ℚ) =
      (2 : ℚ) ^ n * MvPolynomial.eval (halfPoint n) (verifierCharacteristic n φ) :=
  trueCount_eq_scaled_eval _

theorem satisfyingCount_eq_scaled_machineQuery_eval {n : ℕ}
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (φ : Formula) (hvars : VariablesBelow n φ) :
    (satisfyingCount n φ : ℚ) =
      (2 : ℚ) ^ n * MvPolynomial.eval (halfPoint n)
        (machineQueryPolynomial (n := n) M T φ) := by
  rw [machineQueryPolynomial_eq_verifierCharacteristic M T hD φ hvars]
  exact satisfyingCount_eq_scaled_characteristic_eval n φ

theorem trueCount_pos_iff {n : ℕ} (f : Assignment n → Bool) :
    0 < trueCount f ↔ ∃ a, f a = true := by
  classical
  simp [trueCount, Finset.card_pos, Finset.nonempty_def]

theorem satisfyingCount_empty (n : ℕ) : satisfyingCount n [] = 2 ^ n := by
  simp [satisfyingCount, trueCount, evalFormula]

theorem satisfyingCount_pos_iff (n : ℕ) (φ : Formula)
    (hvars : VariablesBelow n φ) :
    0 < satisfyingCount n φ ↔ Satisfiable φ := by
  rw [satisfyingCount, trueCount_pos_iff]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨extendAssignment a, ha⟩
  · rintro ⟨a, ha⟩
    let b : Assignment n := fun i => a i.val
    refine ⟨b, ?_⟩
    have heq : evalFormula (extendAssignment b) φ = evalFormula a φ := by
      apply SATVerifierSpec.evalFormula_congr
      intro c hc l hl
      have hi := hvars c hc l hl
      exact extendAssignment_fin b ⟨l.1, hi⟩
    exact heq.trans ha

/-- An exact extracted representation has the same counting information.
This theorem places no runtime assumptions on the representation or map. -/
theorem satisfyingCount_eq_scaled_extracted_eval {n : ℕ} {Source : Type*}
    (extract : Source → Poly n) (source : Source) (φ : Formula)
    (hexact : extract source = verifierCharacteristic n φ) :
    (satisfyingCount n φ : ℚ) =
      (2 : ℚ) ^ n * MvPolynomial.eval (halfPoint n) (extract source) := by
  rw [hexact]
  exact satisfyingCount_eq_scaled_characteristic_eval n φ

end GodMoveCharacteristicCounting

#print axioms GodMoveCharacteristicCounting.boolMonomial_eval_half
#print axioms GodMoveCharacteristicCounting.interpolate_eval_half
#print axioms GodMoveCharacteristicCounting.trueCount_eq_scaled_eval
#print axioms GodMoveCharacteristicCounting.satisfyingCount_eq_scaled_characteristic_eval
#print axioms GodMoveCharacteristicCounting.satisfyingCount_eq_scaled_machineQuery_eval
#print axioms GodMoveCharacteristicCounting.satisfyingCount_pos_iff
#print axioms GodMoveCharacteristicCounting.satisfyingCount_empty
#print axioms GodMoveCharacteristicCounting.satisfyingCount_eq_scaled_extracted_eval
