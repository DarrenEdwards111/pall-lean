import GodMoveComputedWireRank
import GodMoveDirectVerifierCircuit

/-!
# Separating samples already supply SAT witnesses

An evaluation sample list separates the actual wire space when a polynomial
in that space vanishing on the samples must be zero. Since the circuit target
belongs to that space, any nonzero Boolean output must be true on a selected
sample. For a direct CNF verifier this gives a satisfying assignment whenever
one exists.

The selector may depend on the entire supplied circuit. This is a correctness
reduction, not an assertion that a separating list can be found efficiently.
Polynomial sample count alone does not establish a polynomial-time selector.
-/

namespace GodMoveSamplingBarrier

open GodMoveBooleanInterpolation GodMoveComputedWireRank GodMoveCircuitConnection
open GodMoveDirectVerifierCircuit GodMovePinnedSATQueries
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer (CGate output)
open CookLevinReduction

/-- Boolean evaluations on these samples detect every nonzero computed-wire
linear combination. This is a semantic condition on the whole wire space. -/
def SeparatesWires {n : ℕ} (c : List (CGate n)) (samples : List (Assignment n)) : Prop :=
  ∀ p ∈ wireSpace c,
    (∀ a ∈ samples, MvPolynomial.eval (booleanPoint a) p = 0) → p = 0

theorem separating_samples_hit {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (hsep : SeparatesWires c samples)
    (p : Poly n) (hp : p ∈ wireSpace c) (hpne : p ≠ 0) :
    ∃ a ∈ samples, MvPolynomial.eval (booleanPoint a) p ≠ 0 := by
  classical
  by_contra h
  apply hpne
  apply hsep p hp
  intro a ha
  by_contra hval
  exact h ⟨a, ha, hval⟩

theorem eval_circuitTarget {n : ℕ} (c : List (CGate n)) (a : Assignment n) :
    MvPolynomial.eval (booleanPoint a) (circuitTarget c) = bit (output c a) := by
  rw [circuitTarget_eq_interpolate, eval_interpolate]

/-- A separating list hits the accepting set of its own circuit whenever
that set is nonempty, even though the list may depend on the circuit. -/
theorem exists_accept_iff_sample_accepts {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (hsep : SeparatesWires c samples) :
    (∃ a : Assignment n, output c a = true) ↔ samples.any (output c) = true := by
  classical
  constructor
  · rintro ⟨a, ha⟩
    have hpne : circuitTarget c ≠ 0 := by
      intro hz
      have he := eval_circuitTarget c a
      rw [hz, map_zero, ha] at he
      norm_num [bit] at he
    obtain ⟨b, hb, hval⟩ := separating_samples_hit c samples hsep _
      (circuitTarget_mem_wireSpace c) hpne
    apply List.any_eq_true.mpr
    refine ⟨b, hb, ?_⟩
    rw [eval_circuitTarget] at hval
    cases he : output c b <;> simp_all [bit]
  · intro h
    obtain ⟨a, _, ha⟩ := List.any_eq_true.mp h
    exact ⟨a, ha⟩

theorem satisfiable_iff_finite_witness {n : ℕ} (φ : Formula)
    (hvars : VariablesBelow n φ) :
    Satisfiable φ ↔ ∃ a : Assignment n, evalFormula (extendAssignment a) φ = true := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨fun i => b i.val, ?_⟩
    have he : evalFormula (extendAssignment (fun i : Fin n => b i.val)) φ =
        evalFormula b φ := by
      apply SATVerifierSpec.evalFormula_congr
      intro cl hcl lit hlit
      simp [extendAssignment, hvars cl hcl lit hlit]
    exact he.trans hb
  · rintro ⟨a, ha⟩
    exact ⟨extendAssignment a, ha⟩

/-- A list separating a fixed formula's actual verifier wires decides SAT
by testing only its listed assignments. Finding that list is a separate task. -/
theorem satisfiable_iff_sample_accepts {n : ℕ} (φ : Formula)
    (hvars : VariablesBelow n φ) (samples : List (Assignment n))
    (hsep : SeparatesWires (verifierCircuit n φ) samples) :
    Satisfiable φ ↔ samples.any (output (verifierCircuit n φ)) = true := by
  rw [satisfiable_iff_finite_witness φ hvars]
  rw [← exists_accept_iff_sample_accepts (verifierCircuit n φ) samples hsep]
  apply exists_congr
  intro a
  rw [verifierCircuit_computes n φ a]

/-- The reduction returns an actual satisfying assignment among the samples. -/
theorem satisfiable_has_selected_witness {n : ℕ} (φ : Formula)
    (hvars : VariablesBelow n φ) (samples : List (Assignment n))
    (hsep : SeparatesWires (verifierCircuit n φ) samples) (hsat : Satisfiable φ) :
    ∃ a ∈ samples, evalFormula (extendAssignment a) φ = true := by
  obtain ⟨a, ha, hout⟩ := List.any_eq_true.mp
    ((satisfiable_iff_sample_accepts φ hvars samples hsep).mp hsat)
  exact ⟨a, ha, (verifierCircuit_computes n φ a).symm.trans hout⟩

end GodMoveSamplingBarrier

#print axioms GodMoveSamplingBarrier.separating_samples_hit
#print axioms GodMoveSamplingBarrier.exists_accept_iff_sample_accepts
#print axioms GodMoveSamplingBarrier.satisfiable_iff_finite_witness
#print axioms GodMoveSamplingBarrier.satisfiable_iff_sample_accepts
#print axioms GodMoveSamplingBarrier.satisfiable_has_selected_witness
