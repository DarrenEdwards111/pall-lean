import GodMoveCircuitConnection
import GodMoveCircuitStorage

/-!
# Polynomial-clock compact sources have polynomial representation size

The pinned-query template has polynomial length in the original formula's
actual encoding length and the number `n` of assignment variables. Composing
that bound with a polynomial clock and the proved quartic simulator bound
gives uniform polynomial bounds for compact circuit gates, arithmetic DAG
syntax, and serialized circuit bits. The constants and exponents are
independent of the formula and `n`.

No SAT-correctness hypothesis is needed for these representation bounds.
The variable count remains explicit: no relationship between it and encoded
formula length is assumed. These results do not bound compiler execution
time, expanded Boolean normalization, or derivative rank.
-/

namespace GodMoveCircuitPolynomialSize

open GodMoveSymbolicPinnedInput GodMoveCircuitConnection GodMoveCircuitRuntimeCost
open PallLean.Paper93.DeepMath.PathB
open ComposableMachine CookLevinReduction CookLevinEmitCodec
open PvsNPSeparatingInvariant (PolyBounded)
open CookLevinEmitClockBounds3 (PB_const PB_id PB_add)

/-- An explicit bit codec preserves polynomial gate-count bounds. Input arity
is the external codec parameter, and is bounded here by the same size scale. -/
theorem encodeCircuit_polynomial_bound {n S C d : ℕ}
    (c : List (NFrameBoundaryTransducer.CGate n))
    (hS : 1 ≤ S) (hn : n ≤ S) (hc : c.length ≤ C * S ^ d) :
    (GodMoveCircuitStorage.encodeCircuit (GodMoveCircuitStorage.sanitize c)).length ≤
      (13 * (C + 2) ^ 2) * S ^ ((d + 1) * 2) := by
  have hpow : S ^ d ≤ S ^ (d + 1) := Nat.pow_le_pow_right hS (by omega)
  have hSle : S ≤ S ^ (d + 1) := by
    calc
      S = S ^ 1 := by rw [pow_one]
      _ ≤ S ^ (d + 1) := Nat.pow_le_pow_right hS (by omega)
  have hnp : n ≤ S ^ (d + 1) := hn.trans hSle
  have h1p : 1 ≤ S ^ (d + 1) := hS.trans hSle
  have hsp : c.length ≤ C * S ^ (d + 1) := hc.trans (Nat.mul_le_mul_left C hpow)
  have hall : n + c.length + 1 ≤ (C + 2) * S ^ (d + 1) := by nlinarith
  calc
    _ ≤ (9 + 2 * (n + c.length)) * c.length + 1 :=
      GodMoveCircuitStorage.encodeCircuit_sanitize_length_le c
    _ ≤ 13 * (n + c.length + 1) ^ 2 := by nlinarith
    _ ≤ 13 * ((C + 2) * S ^ (d + 1)) ^ 2 :=
      Nat.mul_le_mul_left 13 (Nat.pow_le_pow_left hall 2)
    _ = (13 * (C + 2) ^ 2) * S ^ ((d + 1) * 2) := by
      rw [mul_pow, ← pow_mul]
      ac_rfl

/-- The true query-encoding overhead is quadratic in the explicit parameters. -/
theorem inputTemplate_length_add_one_le (φ : Formula) (n : ℕ) :
    (inputTemplate φ n).length + 1 ≤
      13 * ((encodeFormula' φ).length + n + 1) ^ 2 := by
  have h := inputTemplate_length_le φ n
  nlinarith

/-- A polynomial bound survives substitution of the actual pinned-query
length, with constants uniform over formulas and assignment-variable counts. -/
theorem polynomial_after_inputTemplate {f : ℕ → ℕ} (hf : PolyBounded f) :
    ∃ C d : ℕ, ∀ (φ : Formula) (n : ℕ),
      f (inputTemplate φ n).length ≤ C * ((encodeFormula' φ).length + n + 1) ^ d := by
  obtain ⟨c, k, h⟩ := hf
  refine ⟨c * 13 ^ k, 2 * k, ?_⟩
  intro φ n
  calc
    _ ≤ c * ((inputTemplate φ n).length + 1) ^ k := h _
    _ ≤ c * (13 * ((encodeFormula' φ).length + n + 1) ^ 2) ^ k :=
      Nat.mul_le_mul_left c (Nat.pow_le_pow_left (inputTemplate_length_add_one_le φ n) k)
    _ = (c * 13 ^ k) * ((encodeFormula' φ).length + n + 1) ^ (2 * k) := by
      rw [mul_pow, ← pow_mul, mul_assoc]

theorem polynomial_clock_after_inputTemplate {T : ℕ → ℕ} (hT : PolyBounded T) :
    ∃ C d : ℕ, ∀ (φ : Formula) (n : ℕ),
      (inputTemplate φ n).length + T (inputTemplate φ n).length + 1 ≤
        C * ((encodeFormula' φ).length + n + 1) ^ d :=
  polynomial_after_inputTemplate (PB_add (PB_add PB_id hT) (PB_const 1))

/-- Polynomial clocks give uniformly polynomial gate count in original
encoded length plus the explicit number of assignment variables. -/
theorem compactCircuit_polynomial_size (M : Machine) {T : ℕ → ℕ}
    (hT : PolyBounded T) :
    ∃ C d : ℕ, ∀ (φ : Formula) (n : ℕ),
      (compactCircuit M T φ n).length ≤
        C * ((encodeFormula' φ).length + n + 1) ^ d := by
  obtain ⟨c, k, h⟩ := polynomial_clock_after_inputTemplate hT
  refine ⟨circuitConstant M * c ^ 4, k * 4, ?_⟩
  intro φ n
  calc
    _ ≤ circuitConstant M *
        ((inputTemplate φ n).length + T (inputTemplate φ n).length + 1) ^ 4 :=
      compactCircuit_length_le M T φ n
    _ ≤ circuitConstant M * (c * ((encodeFormula' φ).length + n + 1) ^ k) ^ 4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (h φ n) 4)
    _ = (circuitConstant M * c ^ 4) *
        ((encodeFormula' φ).length + n + 1) ^ (k * 4) := by
      rw [mul_pow, ← pow_mul, mul_assoc]

/-- The retained shared arithmetic syntax has a uniform polynomial size
bound when the actual machine clock is polynomially bounded. -/
theorem compactSource_polynomial_size (M : Machine) {T : ℕ → ℕ}
    (hT : PolyBounded T) :
    ∃ C d : ℕ, ∀ (φ : Formula) (n : ℕ),
      GodMoveCircuitArithmetization.representationCost (compactSource M T φ n) ≤
        C * ((encodeFormula' φ).length + n + 1) ^ d := by
  obtain ⟨c, k, h⟩ := polynomial_clock_after_inputTemplate hT
  refine ⟨25 * circuitConstant M * c ^ 4, k * 4, ?_⟩
  intro φ n
  calc
    _ ≤ 25 * circuitConstant M *
        ((inputTemplate φ n).length + T (inputTemplate φ n).length + 1) ^ 4 :=
      compactSource_cost_le M T φ n
    _ ≤ 25 * circuitConstant M * (c * ((encodeFormula' φ).length + n + 1) ^ k) ^ 4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (h φ n) 4)
    _ = (25 * circuitConstant M * c ^ 4) *
        ((encodeFormula' φ).length + n + 1) ^ (k * 4) := by
      rw [mul_pow, ← pow_mul]
      simp only [mul_assoc]

/-- The source circuit also has a uniform polynomial bound on its concrete
serialized bit length, including truth tables and natural-number references. -/
theorem encodedCompactCircuit_polynomial_size (M : Machine) {T : ℕ → ℕ}
    (hT : PolyBounded T) :
    ∃ C d : ℕ, ∀ (φ : Formula) (n : ℕ),
      (encodedCompactCircuit M T φ n).length ≤
        C * ((encodeFormula' φ).length + n + 1) ^ d := by
  obtain ⟨c, k, h⟩ := compactCircuit_polynomial_size M hT
  refine ⟨13 * (c + 2) ^ 2, (k + 1) * 2, ?_⟩
  intro φ n
  exact encodeCircuit_polynomial_bound (compactCircuit M T φ n)
    (by omega) (by omega) (h φ n)

end GodMoveCircuitPolynomialSize

#print axioms GodMoveCircuitPolynomialSize.inputTemplate_length_add_one_le
#print axioms GodMoveCircuitPolynomialSize.encodeCircuit_polynomial_bound
#print axioms GodMoveCircuitPolynomialSize.polynomial_after_inputTemplate
#print axioms GodMoveCircuitPolynomialSize.polynomial_clock_after_inputTemplate
#print axioms GodMoveCircuitPolynomialSize.compactCircuit_polynomial_size
#print axioms GodMoveCircuitPolynomialSize.compactSource_polynomial_size
#print axioms GodMoveCircuitPolynomialSize.encodedCompactCircuit_polynomial_size
