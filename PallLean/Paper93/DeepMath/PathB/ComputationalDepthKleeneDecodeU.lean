import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneUEncode

/-!
# Kleene interpreter project — number → `UCode` decode (PROVED)

To define `spec` (the intended table contents) we must map an encoded-code *number* `ec` back to a `UCode`.
`decodeU : ℕ → UCode` does this by tag-recursion mirroring `UCode.enc`, with well-founded recursion on `ec`
(the sub-payloads are `< ec` via the strict `Nat.unpair` bound `unpair_right_lt_of_fst`).  It is a left
inverse of `enc`:

  `unpair_right_lt_of_fst` — `1 ≤ (unpair ec).1 → (unpair ec).2 < ec`.
  `decodeU`, `decode_enc` — `decodeU (enc u) = u`.

So `spec N := encodeOpt (UCode.evaln k (decodeU ec) n)` (with `(k,ec,n)` decoded from the rank) reads the
right value at every valid config, while being total on all numbers.

## What is proved (clean axioms, no `sorry`)

* `unpair_right_lt_of_fst`, `decodeU`, `decode_enc`.

## Honest scope

The number→`UCode` decode + its inverse property.  The `spec` definition, `hbody`, the interpreter, and the
runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

/-- Strict `Nat.unpair` bound: a positive left component forces the right `< ec`. -/
theorem unpair_right_lt_of_fst (ec : ℕ) (h : 1 ≤ (Nat.unpair ec).1) : (Nat.unpair ec).2 < ec := by
  conv_rhs => rw [← Nat.pair_unpair ec]
  rcases he : Nat.unpair ec with ⟨a, b⟩
  rw [he] at h; simp only at h ⊢
  rw [Nat.pair]; split <;> nlinarith

/-- Decode a number to a `UCode` by tag-recursion (left inverse of `UCode.enc`). -/
noncomputable def decodeU (ec : ℕ) : UCode :=
  match h : (Nat.unpair ec).1 with
  | 0 => UCode.zero
  | 1 => UCode.succ
  | 2 => UCode.left
  | 3 => UCode.right
  | 4 => UCode.pair (decodeU (Nat.unpair (Nat.unpair ec).2).1) (decodeU (Nat.unpair (Nat.unpair ec).2).2)
  | 5 => UCode.comp (decodeU (Nat.unpair (Nat.unpair ec).2).1) (decodeU (Nat.unpair (Nat.unpair ec).2).2)
  | 6 => UCode.prec (decodeU (Nat.unpair (Nat.unpair ec).2).1) (decodeU (Nat.unpair (Nat.unpair ec).2).2)
  | 7 => UCode.rfind' (decodeU (Nat.unpair ec).2)
  | _ => UCode.zero
termination_by ec
decreasing_by
  · have hp := unpair_right_lt_of_fst ec (by omega); have := Nat.unpair_left_le (Nat.unpair ec).2; omega
  · have hp := unpair_right_lt_of_fst ec (by omega); have := Nat.unpair_right_le (Nat.unpair ec).2; omega
  · have hp := unpair_right_lt_of_fst ec (by omega); have := Nat.unpair_left_le (Nat.unpair ec).2; omega
  · have hp := unpair_right_lt_of_fst ec (by omega); have := Nat.unpair_right_le (Nat.unpair ec).2; omega
  · have hp := unpair_right_lt_of_fst ec (by omega); have := Nat.unpair_left_le (Nat.unpair ec).2; omega
  · have hp := unpair_right_lt_of_fst ec (by omega); have := Nat.unpair_right_le (Nat.unpair ec).2; omega
  · exact unpair_right_lt_of_fst ec (by omega)

/-- **`decodeU` is a left inverse of `enc` (proved).** -/
theorem decode_enc (u : UCode) : decodeU (UCode.enc u) = u := by
  induction u with
  | zero => conv_lhs => rw [UCode.enc, decodeU, Nat.unpair_pair]
  | succ => conv_lhs => rw [UCode.enc, decodeU, Nat.unpair_pair]
  | left => conv_lhs => rw [UCode.enc, decodeU, Nat.unpair_pair]
  | right => conv_lhs => rw [UCode.enc, decodeU, Nat.unpair_pair]
  | pair a b iha ihb =>
      conv_lhs => rw [UCode.enc, decodeU, Nat.unpair_pair]
      simp only [Nat.unpair_pair, iha, ihb]
  | comp a b iha ihb =>
      conv_lhs => rw [UCode.enc, decodeU, Nat.unpair_pair]
      simp only [Nat.unpair_pair, iha, ihb]
  | prec a b iha ihb =>
      conv_lhs => rw [UCode.enc, decodeU, Nat.unpair_pair]
      simp only [Nat.unpair_pair, iha, ihb]
  | rfind' a iha =>
      conv_lhs => rw [UCode.enc, decodeU, Nat.unpair_pair]
      simp only [Nat.unpair_pair, iha]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.decodeU
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.decode_enc
