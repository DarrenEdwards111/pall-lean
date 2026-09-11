import GodMoveBooleanInterpolation
import GodMoveCompactGaugeCost
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Exact separation through a Boolean interface

A left circuit supplies r Boolean wires to a right circuit. Expanding the
interface into linear coordinates requires up to 2^r joint wire states,
not r coordinates. The response table has an exact factorization through
those states. Equality attains rank 2^r, so the exponential dependence is
necessary even for a simple function.

This matrix records communication across the cut. It is not substituted for
the production N-Frame invariant and asserts no SAT circuit lower bound.
-/

namespace GodMoveCircuitInterface

open GodMoveBooleanInterpolation
open scoped BigOperators

variable {A B : Type*}

/-- The left part chooses one joint state of its r output ports. -/
def selector {r : ℕ} (ports : A → Assignment r) : Matrix A (Assignment r) ℚ :=
  fun x s => if ports x = s then 1 else 0

/-- The right part evaluates on a supplied interface state and its own input. -/
def continuation {r : ℕ} (finish : Assignment r → B → Bool) :
    Matrix (Assignment r) B ℚ := fun s y => bit (finish s y)

def response {r : ℕ} (ports : A → Assignment r)
    (finish : Assignment r → B → Bool) : Matrix A B ℚ :=
  fun x y => bit (finish (ports x) y)

/-- Gluing has an exact linear expansion over joint states. The expansion is
a semantic identity; this theorem does not execute the exponential sum. -/
theorem response_factorization {r : ℕ} (ports : A → Assignment r)
    (finish : Assignment r → B → Bool) :
    response ports finish = selector ports * continuation finish := by
  classical
  ext x y
  simp [response, selector, continuation, Matrix.mul_apply]

variable [Fintype B]

/-- r bits permit 2^r response directions. A bound by r would require a
further linearity property and does not follow from the number of wires. -/
theorem response_rank_le_states {r : ℕ} (ports : A → Assignment r)
    (finish : Assignment r → B → Bool) :
    (response ports finish).rank ≤ 2 ^ r := by
  rw [response_factorization]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_le_card_width _).trans (assignment_count r).le)

/-- A preserved q-dimensional response minor gives a logarithmic wire
requirement through this argument, not a q-wire requirement. -/
theorem response_rank_requires_bits {r q : ℕ} (ports : A → Assignment r)
    (finish : Assignment r → B → Bool)
    (hq : q ≤ (response ports finish).rank) :
    Nat.clog 2 q ≤ r := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
  exact hq.trans (response_rank_le_states ports finish)

/-- A genuinely logarithmic Boolean interface is sufficient for a polynomial
response-rank bound. The width premise must be established from the circuit;
bounded fan-in or a finite gate alphabet does not establish it. -/
theorem response_rank_le_power_of_logarithmic_ports {r : ℕ}
    (ports : A → Assignment r) (finish : Assignment r → B → Bool)
    (n c : ℕ) (hn : n ≠ 0) (hr : r ≤ c * Nat.log 2 n) :
    (response ports finish).rank ≤ n ^ c := by
  calc
    _ ≤ 2 ^ r := response_rank_le_states ports finish
    _ ≤ 2 ^ (c * Nat.log 2 n) := Nat.pow_le_pow_right (by decide) hr
    _ = (2 ^ Nat.log 2 n) ^ c := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ n ^ c := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hn) c

/-- Equality compares an incoming r-bit interface with the right input. -/
def equalityFinish (r : ℕ) (s y : Assignment r) : Bool := decide (s = y)

def equalityResponse (r : ℕ) : Matrix (Assignment r) (Assignment r) ℚ :=
  response id (equalityFinish r)

theorem equalityResponse_eq_one (r : ℕ) : equalityResponse r = 1 := by
  ext x y
  simp [equalityResponse, response, equalityFinish, bit, Matrix.one_apply]

/-- The joint-state rank ceiling is attained exactly. -/
theorem equalityResponse_rank (r : ℕ) : (equalityResponse r).rank = 2 ^ r := by
  rw [equalityResponse_eq_one, Matrix.rank_one, assignment_count]

theorem two_bit_interface_rank : (equalityResponse 2).rank = 4 := by
  rw [equalityResponse_rank]
  norm_num

theorem no_rank_bound_by_number_of_ports :
    ¬ ∀ r : ℕ, (equalityResponse r).rank ≤ r := by
  intro h
  have htwo := h 2
  rw [two_bit_interface_rank] at htwo
  omega

/-- This is an asymptotic failure, not only a small boundary effect. -/
theorem no_eventual_polynomial_rank_in_ports :
    ¬ ∃ C d r0 : ℕ, ∀ r ≥ r0, (equalityResponse r).rank ≤ C * r ^ d := by
  rintro ⟨C, d, r0, h⟩
  apply GodMoveCompactGaugeCost.no_eventual_polynomial_choose_bound
  refine ⟨C, d, r0, ?_⟩
  intro r hr
  exact (Nat.choose_le_two_pow r (Nat.log 2 r)).trans
    (by simpa only [equalityResponse_rank] using h r hr)

end GodMoveCircuitInterface

#print axioms GodMoveCircuitInterface.response_factorization
#print axioms GodMoveCircuitInterface.response_rank_le_states
#print axioms GodMoveCircuitInterface.response_rank_requires_bits
#print axioms GodMoveCircuitInterface.response_rank_le_power_of_logarithmic_ports
#print axioms GodMoveCircuitInterface.equalityResponse_eq_one
#print axioms GodMoveCircuitInterface.equalityResponse_rank
#print axioms GodMoveCircuitInterface.two_bit_interface_rank
#print axioms GodMoveCircuitInterface.no_rank_bound_by_number_of_ports
#print axioms GodMoveCircuitInterface.no_eventual_polynomial_rank_in_ports
