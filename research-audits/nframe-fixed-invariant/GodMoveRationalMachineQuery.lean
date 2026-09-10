import GodMoveWeightedWireQuery
import GodMoveMachineCircuitOracle
import GodMoveSignedBinary

/-!
# Actual SAT-machine queries for exact rational wire relations

Supplied rational coefficients are cleared and serialized as signed binary
weights. A finite Boolean circuit tests the resulting integer relation, and
the existing Tseitin encoder supplies the actual SAT-machine input word.
Correctness of the machine yields both decision and witness correctness.

The rational precision budget is explicit. No unrestricted predicate oracle
or Boolean assignment table is used by this query construction. The bound on
precision generated throughout adaptive discovery is proved separately in
`GodMoveMachineDiscoveryPrecision`.
-/

namespace GodMoveRationalMachineQuery

open GodMoveBooleanInterpolation GodMoveRationalClearing GodMoveSignedBinary
open GodMoveWeightedWireQuery GodMoveMachineCircuitOracle
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer (CGate runFrom output)
open ComposableMachine SeparationTarget
open scoped BigOperators

def rationalTerms {n : ℕ} (c : List (CGate n)) (q : Fin c.length → ℚ) (b : ℕ) :
    List (Fin c.length × SignedBits) :=
  List.ofFn (fun i => (i, encodedClearedWeights q b i))

def rationalQuery {n : ℕ} (c : List (CGate n)) (q : Fin c.length → ℚ) (b : ℕ) :
    List (CGate n) := weightedQuery c (rationalTerms c q b)

def rationalWireValue {n : ℕ} (c : List (CGate n)) (q : Fin c.length → ℚ)
    (a : Assignment n) : ℚ :=
  let vals := runFrom a [] c
  rationalValue q (fun i => vals.getD i.val false)

theorem rationalTerms_value {n : ℕ} (c : List (CGate n)) (q : Fin c.length → ℚ)
    (b : ℕ) (hb : CoeffPrecision q b) (vals : List Bool) :
    termValue vals (rationalTerms c q b) =
      integerValue (clearedWeights q) (fun i => vals.getD i.val false) := by
  simp [termValue, rationalTerms, integerValue, List.map_ofFn, List.sum_ofFn,
    encodedClearedWeights_value q b hb]

/-- The Boolean query tests the exact rational relation; integer clearing and
serialization are justified, rather than assumed to preserve its zero set. -/
theorem rationalQuery_output {n : ℕ} (c : List (CGate n)) (q : Fin c.length → ℚ)
    (b : ℕ) (hb : CoeffPrecision q b) (a : Assignment n) :
    output (rationalQuery c q b) a = decide (rationalWireValue c q a ≠ 0) := by
  rw [rationalQuery, weightedQuery_output, rationalTerms_value c q b hb]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact not_congr (rationalValue_zero_iff q _).symm

theorem rationalTerms_length {n : ℕ} (c : List (CGate n))
    (q : Fin c.length → ℚ) (b : ℕ) : (rationalTerms c q b).length = c.length := by
  simp [rationalTerms]

theorem rationalTerms_bits {n : ℕ} (c : List (CGate n))
    (q : Fin c.length → ℚ) (b : ℕ) :
    termBits (rationalTerms c q b) = c.length * coefficientWidth c.length b := by
  simp [termBits, rationalTerms, encodedClearedWeights, encodeInt_length,
    List.map_ofFn, List.sum_ofFn]

/-- Includes the original shared circuit, all explicit binary coefficients,
full-carry arithmetic, and the final comparator. -/
def queryGateBudget (s b : ℕ) : ℕ :=
  32 * (s + s + s * coefficientWidth s b + 1) ^ 2

theorem rationalQuery_length_le {n : ℕ} (c : List (CGate n))
    (q : Fin c.length → ℚ) (b : ℕ) :
    (rationalQuery c q b).length ≤ queryGateBudget c.length b := by
  simpa only [rationalQuery, rationalTerms_length, rationalTerms_bits, queryGateBudget]
    using weightedQuery_gate_count_le c (rationalTerms c q b)

theorem rationalQuery_word_length_le {n : ℕ} (c : List (CGate n))
    (q : Fin c.length → ℚ) (b : ℕ) :
    (circuitQuery (rationalQuery c q b)).length ≤
      100 * (n + queryGateBudget c.length b + 1) ^ 2 := by
  apply (circuitQuery_length_le _).trans
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.add_le_add_right (Nat.add_le_add_left (rationalQuery_length_le c q b) n) 1) 2)

/-- A bound on actual SAT-machine steps, excluding the host construction and
arithmetic costs. The precision parameter is retained explicitly. -/
theorem rationalQuery_clock_le (T : ℕ → ℕ) (C d : ℕ)
    (hT : ∀ m, T m ≤ C * (m + 1) ^ d) {n : ℕ} (c : List (CGate n))
    (q : Fin c.length → ℚ) (b : ℕ) :
    T (circuitQuery (rationalQuery c q b)).length ≤
      (C * 101 ^ d) * (n + queryGateBudget c.length b + 1) ^ (2 * d) := by
  apply (circuitClock_le T C d hT _).trans
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.add_le_add_right (Nat.add_le_add_left (rationalQuery_length_le c q b) n) 1) _)

def rationalSAT (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (q : Fin c.length → ℚ) (b : ℕ) : Bool :=
  circuitSAT M T (rationalQuery c q b)

theorem rationalSAT_correct (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    {n : ℕ} (c : List (CGate n)) (q : Fin c.length → ℚ) (b : ℕ)
    (hb : CoeffPrecision q b) :
    rationalSAT M T c q b = true ↔ ∃ a, rationalWireValue c q a ≠ 0 := by
  rw [rationalSAT, circuitSAT_correct M T hD]
  simp only [rationalQuery_output c q b hb, decide_eq_true_eq]

def rationalWitnessWithCount (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (q : Fin c.length → ℚ) (b : ℕ) : Option (Assignment n) × ℕ :=
  GodMoveMachineCircuitOracle.findWitnessWithCount M T (rationalQuery c q b)

theorem rationalWitness_some (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    {n : ℕ} (c : List (CGate n)) (q : Fin c.length → ℚ) (b : ℕ)
    (hb : CoeffPrecision q b) (a : Assignment n)
    (ha : (rationalWitnessWithCount M T c q b).1 = some a) :
    rationalWireValue c q a ≠ 0 := by
  have h := GodMoveMachineCircuitOracle.findWitness_some_correct M T hD
    (rationalQuery c q b) a ha
  simpa only [rationalQuery_output c q b hb, decide_eq_true_eq] using h

theorem rationalWitness_none_iff (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    {n : ℕ} (c : List (CGate n)) (q : Fin c.length → ℚ) (b : ℕ)
    (hb : CoeffPrecision q b) :
    (rationalWitnessWithCount M T c q b).1 = none ↔
      ¬ ∃ a, rationalWireValue c q a ≠ 0 := by
  have h := GodMoveMachineCircuitOracle.findWitness_none_iff M T hD (rationalQuery c q b)
  simpa only [rationalQuery_output c q b hb, decide_eq_true_eq] using h

theorem rationalWitness_queries_le (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (q : Fin c.length → ℚ) (b : ℕ) :
    (rationalWitnessWithCount M T c q b).2 ≤ n + 1 :=
  GodMoveMachineCircuitOracle.findWitnessWithCount_count_le M T (rationalQuery c q b)

private def fractionalCircuit : List (CGate 2) := [.var 0, .var 1, .cst true]

private def fractionalWeights : Fin fractionalCircuit.length → ℚ :=
  ![(1 / 2 : ℚ), (1 / 3 : ℚ), (-5 / 6 : ℚ)]

/-- info: [true, true, true, false] -/
#guard_msgs in
#eval (GodMoveBooleanWireTable.allAssignments 2).map
  (output (rationalQuery fractionalCircuit fractionalWeights 3))

/-- info: true -/
#guard_msgs in
#eval decide ((GodMoveBooleanWireTable.allAssignments 2).all (fun a =>
  output (rationalQuery fractionalCircuit fractionalWeights 3) a ==
    decide (rationalWireValue fractionalCircuit fractionalWeights a ≠ 0)))

end GodMoveRationalMachineQuery

#print axioms GodMoveRationalMachineQuery.rationalTerms_value
#print axioms GodMoveRationalMachineQuery.rationalQuery_output
#print axioms GodMoveRationalMachineQuery.rationalQuery_length_le
#print axioms GodMoveRationalMachineQuery.rationalQuery_word_length_le
#print axioms GodMoveRationalMachineQuery.rationalQuery_clock_le
#print axioms GodMoveRationalMachineQuery.rationalSAT_correct
#print axioms GodMoveRationalMachineQuery.rationalWitness_some
#print axioms GodMoveRationalMachineQuery.rationalWitness_none_iff
#print axioms GodMoveRationalMachineQuery.rationalWitness_queries_le
