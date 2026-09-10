import GodMoveDirectVerifierCircuit
import GodMoveComputedWireRank

/-!
# A barrier for verifier invariants with a generic circuit upper bound

Every fixed CNF's assignment predicate already has a small Boolean circuit.
Consequently any invariant of its characteristic polynomial that has a
uniform polynomial upper bound for *all* circuit representations also has a
uniform polynomial upper bound on every such verifier target. This statement
does not assume SAT is easy: checking an assignment is a different task.

The obstruction is scoped to the stated generic circuit upper bound and a
quantity depending only on the normalized target. It does not disprove an
invariant that retains actual SAT-decider history or a lower bound for the
SAT decision predicate over encoded formulas.
-/

namespace GodMoveVerifierInvariantBarrier

open GodMoveBooleanInterpolation GodMoveCircuitConnection GodMoveDirectVerifierCircuit
open GodMoveComputedWireRank GodMoveFaithfulHandshake
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer (CGate)
open CookLevinReduction CookLevinEmitCodec

/-- The actual computed-wire rank is small on the unconditional direct
verifier program for every fixed formula. -/
theorem directVerifier_wireRank_le_encoded (n : ℕ) (φ : Formula) :
    wireRank (verifierCircuit n φ) ≤ (encodeFormula' φ).length :=
  (wireRank_le_length _).trans (verifierCircuit_length_le_encoded n φ)

theorem directVerifier_target_mem_wireSpace (n : ℕ) (φ : Formula) :
    verifierCharacteristic n φ ∈ wireSpace (verifierCircuit n φ) := by
  rw [← verifierCircuit_target n φ]
  exact circuitTarget_mem_wireSpace _

/-- Any circuit-cost bound on a target-only invariant transfers to every
fixed-formula characteristic, with no SAT correctness or runtime premise. -/
theorem verifierInvariant_le_encoded
    (I : (n : ℕ) → Poly n → ℕ) (C d : ℕ)
    (hupper : ∀ n (c : List (CGate n)),
      I n (circuitTarget c) ≤ C * (n + c.length + 1) ^ d)
    (n : ℕ) (φ : Formula) :
    I n (verifierCharacteristic n φ) ≤ C * (n + (encodeFormula' φ).length + 1) ^ d := by
  have h := hupper n (verifierCircuit n φ)
  rw [verifierCircuit_target] at h
  exact h.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left
    (by have := verifierCircuit_length_le_encoded n φ; omega) d))

/-- A stronger variant also permits dependence on the particular formula.
It still fails as a separation strategy if the generic upper bound applies
to every circuit representing that formula's verifier characteristic. -/
theorem formulaIndexedInvariant_le_encoded
    (I : (n : ℕ) → Formula → Poly n → ℕ) (C d : ℕ)
    (hupper : ∀ n (φ : Formula) (c : List (CGate n)),
      circuitTarget c = verifierCharacteristic n φ →
      I n φ (circuitTarget c) ≤ C * (n + (encodeFormula' φ).length + c.length + 1) ^ d)
    (n : ℕ) (φ : Formula) :
    I n φ (verifierCharacteristic n φ) ≤
      (C * 2 ^ d) * (n + (encodeFormula' φ).length + 1) ^ d := by
  have h := hupper n φ (verifierCircuit n φ) (verifierCircuit_target n φ)
  rw [verifierCircuit_target] at h
  have hsize : n + (encodeFormula' φ).length + (verifierCircuit n φ).length + 1 ≤
      2 * (n + (encodeFormula' φ).length + 1) := by
    have := verifierCircuit_length_le_encoded n φ
    omega
  calc
    _ ≤ C * (n + (encodeFormula' φ).length + (verifierCircuit n φ).length + 1) ^ d := h
    _ ≤ C * (2 * (n + (encodeFormula' φ).length + 1)) ^ d :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left hsize d)
    _ = (C * 2 ^ d) * (n + (encodeFormula' φ).length + 1) ^ d := by
      rw [mul_pow, mul_assoc]

/-- The generic upper bound cannot coexist with an unavoidable superpolynomial
lower bound on these characteristic targets, even allowing any formulas. -/
theorem no_targetOnly_verifier_separation :
    ¬ ∃ (I : (n : ℕ) → Poly n → ℕ) (C d : ℕ),
      (∀ n (c : List (CGate n)),
        I n (circuitTarget c) ≤ C * (n + c.length + 1) ^ d) ∧
      (∀ A b : ℕ, ∃ (n : ℕ) (φ : Formula),
        A * (n + (encodeFormula' φ).length + 1) ^ b < I n (verifierCharacteristic n φ)) := by
  rintro ⟨I, C, d, hupper, hlower⟩
  obtain ⟨n, φ, hhard⟩ := hlower C d
  exact (not_lt_of_ge (verifierInvariant_le_encoded I C d hupper n φ)) hhard

end GodMoveVerifierInvariantBarrier

#print axioms GodMoveVerifierInvariantBarrier.directVerifier_wireRank_le_encoded
#print axioms GodMoveVerifierInvariantBarrier.directVerifier_target_mem_wireSpace
#print axioms GodMoveVerifierInvariantBarrier.verifierInvariant_le_encoded
#print axioms GodMoveVerifierInvariantBarrier.formulaIndexedInvariant_le_encoded
#print axioms GodMoveVerifierInvariantBarrier.no_targetOnly_verifier_separation
