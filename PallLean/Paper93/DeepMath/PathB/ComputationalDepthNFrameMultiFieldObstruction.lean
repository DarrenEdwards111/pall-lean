import Mathlib

/-!
# The multi-field / CRT obstruction: arithmetisation and lower bound cannot coexist

This file records — honestly — why the *multi-field* route does **not** cross the multi-prime composite-`MOD` barrier
(`MOD_6` / `ACC⁰[6]`), which is an open problem.  It is an obstruction, **not** a crossing.

The situation after C14–C15:
* **C14**: over a single field `F_ℓ`, a composite `MOD_m` (`m ∤ ℓ`) has *no* polynomial arithmetisation of the sum —
  the count is only visible mod `ℓ`.
* **C15**: over `F_ℓ` the char-matching modulus `MOD_ℓ` is a low-degree blind spot, so no single field makes all moduli
  of a multi-prime circuit hard.

The natural **multi-field / CRT response**: combine the characteristics.  By CRT, `MOD_6 = ([· ≡ 0 mod 2], [· ≡ 0 mod 3])`
arithmetises over the *product ring* `ZMod 6 ≅ F_2 × F_3` — recovering the arithmetisation C14 lacked over each single
field.

But the N-Frame lower bound (`nframeComplexity_omegaFn_univ_ge`, and the whole `sqfSpan` dimension argument) **requires a
field**: `NFrameComplexity` is defined only for `[Field F]`, because it is a `Module.finrank` of a span — linear
independence over a field.  The CRT object lives over `ZMod 6`, which is **not a field**:

  `zmod6_not_isField` — `¬ IsField (ZMod 6)` (`2 · 3 = 0` with `2, 3 ≠ 0`: zero divisors).

So the multi-field/CRT route trades one gap for another: it *gains* the arithmetisation (over `ZMod 6`) but *loses* the
field structure the lower-bound dimension argument needs.  **Neither the single field `F_ℓ` (arithmetisation fails, C14)
nor the product ring `ZMod 6` (field structure fails, here) supports both the arithmetisation and the field-based lower
bound at once.**  That is the precise technical heart of why the polynomial method — single- or multi-field — does not
prove multi-prime composite `MOD` lower bounds, and why `MOD_6` is open.

Crossing it genuinely requires a technique that does *not* reduce to a field-linear-algebra dimension count on a single
characteristic — e.g. Williams' algorithmic `NEXP ⊄ ACC⁰` route (a different arc entirely), or something new.  This file
does **not** claim a crossing; it isolates the obstruction.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameACC0

/-- **The CRT object is not a field (proved)**: `ZMod 6 ≅ F_2 × F_3`, where the multi-field/CRT arithmetisation of
`MOD_6` lives, has zero divisors (`2 · 3 = 0`, `2, 3 ≠ 0`) — so it is not a field, and the field-based N-Frame dimension
lower bound cannot run over it. -/
theorem zmod6_not_isField : ¬ IsField (ZMod 6) := by
  intro h
  have h2 : (2 : ZMod 6) ≠ 0 := by decide
  have h3 : (3 : ZMod 6) ≠ 0 := by decide
  obtain ⟨u, hu⟩ := h.mul_inv_cancel h2
  have hz : (2 : ZMod 6) * 3 = 0 := by decide
  apply h3
  calc (3 : ZMod 6) = u * (2 * 3) := by rw [← mul_assoc, mul_comm u 2, hu, one_mul]
    _ = u * 0 := by rw [hz]
    _ = 0 := mul_zero u

/-- More generally: `ZMod m` for composite `m` (here witnessed by a nontrivial factorisation `m = a * b` with
`a, b ≠ 0` in `ZMod m`) is not a field — the CRT product ring always has zero divisors. -/
theorem zmod_not_isField_of_zero_divisors (m : ℕ) (a b : ZMod m)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a * b = 0) : ¬ IsField (ZMod m) := by
  intro h
  obtain ⟨u, hu⟩ := h.mul_inv_cancel ha
  apply hb
  calc b = u * (a * b) := by rw [← mul_assoc, mul_comm u a, hu, one_mul]
    _ = u * 0 := by rw [hab]
    _ = 0 := mul_zero u

end PallLean.Paper93.DeepMath.PathB.NFrameACC0

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.zmod6_not_isField
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.zmod_not_isField_of_zero_divisors
