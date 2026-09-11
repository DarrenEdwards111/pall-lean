import GodMoveCircuitInterface
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCircuitUpgrade

/-!
# A linear-size actual circuit with exponential interface response rank

The existing verified bounded-fan-in compiler builds equality on two r-bit
blocks using exactly 4r+1 gates. Its actual two-block response table is the
2^r-dimensional identity. Thus polynomial circuit size, a fixed finite gate
library, and bounded local fan-in do not imply polynomial rank of this table.

This is a calibration of the interface factorization, not a substitution of
communication rank for the production N-Frame invariant or a SAT lower bound.
-/

namespace GodMoveEqualityCircuit

open GodMoveBooleanInterpolation GodMoveCircuitInterface
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- A tree of binary equality tests joined by binary AND gates. -/
def equalityTests {r : ℕ} : List (Fin r) → Trans (r + r)
  | [] => .cst true
  | i :: is => .bin (· && ·)
      (.bin (fun a b => decide (a = b)) (.var (Fin.castAdd r i)) (.var (Fin.natAdd r i)))
      (equalityTests is)

theorem equalityTests_volume {r : ℕ} (is : List (Fin r)) :
    volume (equalityTests is) = 4 * is.length + 1 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [equalityTests, volume, ih, List.length_cons]; omega

theorem equalityTests_eval {r : ℕ} (is : List (Fin r)) (x y : Assignment r) :
    eval (equalityTests is) (Fin.append x y) = true ↔ ∀ i ∈ is, x i = y i := by
  induction is with
  | nil => simp [equalityTests, eval]
  | cons i is ih =>
    simp only [equalityTests, eval, Fin.append_left, Fin.append_right]
    simp [ih]

def equalityTrans (r : ℕ) : Trans (r + r) := equalityTests (List.finRange r)

theorem equalityTrans_volume (r : ℕ) : volume (equalityTrans r) = 4 * r + 1 := by
  simp [equalityTrans, equalityTests_volume]

theorem equalityTrans_eval (r : ℕ) (x y : Assignment r) :
    eval (equalityTrans r) (Fin.append x y) = true ↔ x = y := by
  rw [equalityTrans, equalityTests_eval]
  simp [funext_iff]

/-- Actual gate-list compilation, with sharing allowed by the target type. -/
def equalityCircuit (r : ℕ) : List (CGate (r + r)) := compile 0 (equalityTrans r)

theorem equalityCircuit_length (r : ℕ) : (equalityCircuit r).length = 4 * r + 1 := by
  rw [equalityCircuit, compile_length, equalityTrans_volume]

/-- Correctness follows from the verified compiler's actual gate evaluation. -/
theorem equalityCircuit_output (r : ℕ) (x y : Assignment r) :
    output (equalityCircuit r) (Fin.append x y) = decide (x = y) := by
  have hc := compile_computes (equalityTrans r) (Fin.append x y)
  change output (equalityCircuit r) (Fin.append x y) = _ at hc
  rw [hc]
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using equalityTrans_eval r x y

/-- The response matrix is built from the compiled circuit's output. -/
def circuitResponse (r : ℕ) : Matrix (Assignment r) (Assignment r) ℚ :=
  fun x y => bit (output (equalityCircuit r) (Fin.append x y))

theorem circuitResponse_eq_equalityResponse (r : ℕ) :
    circuitResponse r = equalityResponse r := by
  ext x y
  simp [circuitResponse, equalityResponse, response, equalityFinish, equalityCircuit_output]

theorem circuitResponse_eq_one (r : ℕ) : circuitResponse r = 1 := by
  rw [circuitResponse_eq_equalityResponse, equalityResponse_eq_one]

theorem circuitResponse_rank (r : ℕ) : (circuitResponse r).rank = 2 ^ r := by
  rw [circuitResponse_eq_equalityResponse, equalityResponse_rank]

/-- The exponential rank occurs with an exact linear gate bound. -/
theorem linear_circuit_exponential_response (r : ℕ) :
    (equalityCircuit r).length = 4 * r + 1 ∧ (circuitResponse r).rank = 2 ^ r :=
  ⟨equalityCircuit_length r, circuitResponse_rank r⟩

/-- No eventual polynomial in the size of these actual compiled circuits
bounds their response rank across the displayed input cut. -/
theorem no_eventual_polynomial_response_rank_in_circuit_size :
    ¬ ∃ C d r0 : ℕ, ∀ r ≥ r0,
      (circuitResponse r).rank ≤ C * (equalityCircuit r).length ^ d := by
  rintro ⟨C, d, r0, hbound⟩
  apply no_eventual_polynomial_rank_in_ports
  refine ⟨C * 5 ^ d, d, max r0 1, ?_⟩
  intro r hr
  have hr0 : r0 ≤ r := (le_max_left _ _).trans hr
  have hr1 : 1 ≤ r := (le_max_right _ _).trans hr
  have hsize : (equalityCircuit r).length ≤ 5 * r := by
    rw [equalityCircuit_length]
    omega
  rw [← circuitResponse_eq_equalityResponse]
  calc
    _ ≤ C * (equalityCircuit r).length ^ d := hbound r hr0
    _ ≤ C * (5 * r) ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize d)
    _ = _ := by rw [mul_pow, mul_assoc]

end GodMoveEqualityCircuit

#print axioms GodMoveEqualityCircuit.equalityTests_volume
#print axioms GodMoveEqualityCircuit.equalityTests_eval
#print axioms GodMoveEqualityCircuit.equalityCircuit_length
#print axioms GodMoveEqualityCircuit.equalityCircuit_output
#print axioms GodMoveEqualityCircuit.circuitResponse_eq_one
#print axioms GodMoveEqualityCircuit.circuitResponse_rank
#print axioms GodMoveEqualityCircuit.linear_circuit_exponential_response
#print axioms GodMoveEqualityCircuit.no_eventual_polynomial_response_rank_in_circuit_size
