import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic

/-!
# Bit-cost model — foundations (PROVED)

Toward an *efficient* universal simulator: the `Code.evaln` fuel measure charges by the *magnitude* of
intermediate values, so the memoised DP — whose table is one giant `Nat` (`encodeList`, `≥ 2 ^ cells`,
`ComputationalDepthKleeneMemoBlowup`) — is super-polynomial there.  A faithful **bit-cost** model charges by
the *bit-length* of operands instead, under which addressable structure is cheap.

This file lays the primitive: `bitlen = Nat.size`, and the key lemma `bitlen_pair_le` — `Nat.pair` only
**doubles** bit-length (`bitlen (pair a b) ≤ 2 · bitlen (a+b+1)`), additive up to a constant factor, even
though it *squares* magnitude.  This is the sense in which pairing/addressing is cheap in bits, and the basis
for re-accounting the simulator's runtime.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BitCost

/-- Bit-length of a natural number (number of binary digits); `bitlen 0 = 0`. -/
def bitlen (n : ℕ) : ℕ := Nat.size n

theorem bitlen_mono {m n : ℕ} (h : m ≤ n) : bitlen m ≤ bitlen n := Nat.size_le_size h

theorem lt_two_pow_bitlen (n : ℕ) : n < 2 ^ bitlen n := Nat.lt_size_self n

/-- **`Nat.pair` at most doubles bit-length** — the foundational bit-cost primitive: pairing is cheap in
bits (additive, up to a factor 2), even though it squares magnitude. -/
theorem bitlen_pair_le (a b : ℕ) : bitlen (Nat.pair a b) ≤ 2 * bitlen (a + b + 1) := by
  rw [bitlen, Nat.size_le]
  have h1 : a + b + 1 < 2 ^ bitlen (a + b + 1) := lt_two_pow_bitlen _
  have h2 : Nat.pair a b ≤ (a + b + 1) * (a + b + 1) := by unfold Nat.pair; split <;> nlinarith
  calc Nat.pair a b ≤ (a + b + 1) * (a + b + 1) := h2
    _ < 2 ^ bitlen (a + b + 1) * 2 ^ bitlen (a + b + 1) := Nat.mul_lt_mul'' h1 h1
    _ = 2 ^ (2 * bitlen (a + b + 1)) := by rw [← pow_add]; ring_nf

end PallLean.Paper93.DeepMath.PathB.BitCost

#print axioms PallLean.Paper93.DeepMath.PathB.BitCost.bitlen_pair_le
