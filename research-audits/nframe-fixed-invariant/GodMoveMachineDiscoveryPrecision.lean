import GodMoveMachineDiscovery
import GodMoveGramSamplePrecision

/-!
# Precision throughout the actual SAT-machine discovery

Every basis state on the executed discovery branch spans previously sampled
Boolean wire rows. The Gram argument therefore bounds the exact coefficients
used by the actual row finder, without an extra precision hypothesis.

This bounds values and emitted query sizes. It does not bound the number of
host arithmetic operations or prove a complete Turing-machine runtime bound.
-/

namespace GodMoveMachineDiscoveryPrecision

open GodMoveBooleanInterpolation GodMoveBooleanWireTable GodMoveRationalRowBasis
open GodMoveResidualQueries GodMoveMachineRowFinder GodMoveMachineDiscovery
open GodMoveRationalMachineQuery GodMoveSignedBinary GodMoveMachineCircuitOracle
open GodMoveAdaptiveRefinement (sampleRowSpan_append_singleton)
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer (CGate)
open ComposableMachine

def precisionBudget (s : ℕ) : ℕ := 2 * (s + 1) ^ 2 + 1

theorem queryGateBudget_mono (s : ℕ) {b d : ℕ} (h : b ≤ d) :
    queryGateBudget s b ≤ queryGateBudget s d := by
  unfold queryGateBudget coefficientWidth
  gcongr

def StatePrecision {s : ℕ} (B : RowBasis s) : Prop :=
  ∀ j, coefficientBits (residualCoefficients B j) ≤ precisionBudget s

theorem sample_state_precision {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (B : RowBasis c.length)
    (hspan : GodMoveRationalRowBasis.rowSpan B = GodMoveRowSpanSeparation.rowSpan c samples) :
    StatePrecision B := by
  intro j
  exact GodMoveGramSamplePrecision.sample_state_coefficientBits_le c samples B hspan j

/-- This predicate follows exactly the basis states visited by `discover`.
It makes the precision assertion at every state where queries can occur. -/
def DiscoveryPrecision (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n)) :
    ℕ → RowBasis c.length → Prop
  | 0, _ => True
  | fuel + 1, B =>
      StatePrecision B ∧
        match (findRowWithCount M T c B).1 with
        | none => True
        | some a => DiscoveryPrecision M T c fuel (insert B (wireRow c a))

theorem discover_precision (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (fuel : ℕ) (B : RowBasis c.length)
    (samples : List (Assignment n))
    (hspan : GodMoveRationalRowBasis.rowSpan B = GodMoveRowSpanSeparation.rowSpan c samples) :
    DiscoveryPrecision M T c fuel B := by
  induction fuel generalizing B samples with
  | zero => trivial
  | succ fuel ih =>
    refine ⟨sample_state_precision c samples B hspan, ?_⟩
    cases ha : (findRowWithCount M T c B).1 with
    | none => trivial
    | some a =>
        apply ih (insert B (wireRow c a)) (samples ++ [a])
        rw [insert_span, hspan, sampleRowSpan_append_singleton]

theorem machineSearch_precision (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) :
    DiscoveryPrecision M T c (c.length + 1) (empty c.length) := by
  apply discover_precision M T c (c.length + 1) (empty c.length) []
  rw [empty_span, GodMoveAdaptiveDiscovery.sampleRowSpan_nil]

theorem state_query_gates_le {n : ℕ} (c : List (CGate n))
    (B : RowBasis c.length) (hB : StatePrecision B) (j : Fin c.length) :
    (rationalQuery c (residualCoefficients B j)
      (coefficientBits (residualCoefficients B j))).length ≤
      queryGateBudget c.length (precisionBudget c.length) :=
  (rationalQuery_length_le c _ _).trans (queryGateBudget_mono _ (hB j))

theorem state_query_word_length_le {n : ℕ} (c : List (CGate n))
    (B : RowBasis c.length) (hB : StatePrecision B) (j : Fin c.length) :
    (circuitQuery (rationalQuery c (residualCoefficients B j)
      (coefficientBits (residualCoefficients B j)))).length ≤
      100 * (n + queryGateBudget c.length (precisionBudget c.length) + 1) ^ 2 := by
  apply (circuitQuery_length_le _).trans
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.add_le_add_right (Nat.add_le_add_left (state_query_gates_le c B hB j) n) 1) 2)

/-- Every coordinate query has this clock bound when the supplied SAT clock
is polynomial. Prefix specialization preserves gate count and decreases the
input count, so the same majorant also covers witness-search restrictions. -/
theorem state_query_clock_le (T : ℕ → ℕ) (C d : ℕ)
    (hT : ∀ m, T m ≤ C * (m + 1) ^ d) {n : ℕ} (c : List (CGate n))
    (B : RowBasis c.length) (hB : StatePrecision B) (j : Fin c.length) :
    T (circuitQuery (rationalQuery c (residualCoefficients B j)
      (coefficientBits (residualCoefficients B j)))).length ≤
      (C * 101 ^ d) *
        (n + queryGateBudget c.length (precisionBudget c.length) + 1) ^ (2 * d) := by
  apply (circuitClock_le T C d hT _).trans
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.add_le_add_right (Nat.add_le_add_left (state_query_gates_le c B hB j) n) 1) _)

end GodMoveMachineDiscoveryPrecision

#print axioms GodMoveMachineDiscoveryPrecision.sample_state_precision
#print axioms GodMoveMachineDiscoveryPrecision.discover_precision
#print axioms GodMoveMachineDiscoveryPrecision.machineSearch_precision
#print axioms GodMoveMachineDiscoveryPrecision.state_query_gates_le
#print axioms GodMoveMachineDiscoveryPrecision.state_query_word_length_le
#print axioms GodMoveMachineDiscoveryPrecision.state_query_clock_le
