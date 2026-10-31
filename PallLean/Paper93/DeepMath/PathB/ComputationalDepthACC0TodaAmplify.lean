import Mathlib

/-!
# The Toda modulus-amplification polynomial — the integer-route seed (PROVED)

A genuine run at the **Beigel–Tarui integer wall** (exact-quasipoly for unbounded `AND`/`OR`).  The
exact polynomial route no-gos (degree `=` fan-in) and the exact symmetric collapse towers; the integer
escape is **Toda's modulus amplification**, whose irreducible core is built here.

The amplification polynomial `A(y) = 3y² − 2y³` fixes `0` and `1` and **doubles modular precision**: if
`y ≡ b (mod m)` for `b ∈ {0,1}`, then `A(y) ≡ b (mod m²)`.  Iterating `k` times turns a degree-`(p−1)`
"`≡ b (mod p)`" indicator into a degree-`(p−1)·3^k` "`≡ b (mod p^{2^k})`" indicator; taking
`p^{2^k}` past the count range makes it an **exact integer `{0,1}`-valued** polynomial of degree
`(p−1)·3^k`.  For `k ≈ log log N` this degree is `polylog` — the integer-route exact-quasipoly bypass of
the unbounded-`AND`/`OR` no-go.

This file proves the **doubling core**.

## What is proved (clean axioms, no `sorry`)

* `todaAmp_zero`, `todaAmp_one` — `A` fixes `0` and `1`.
* `todaAmp_dvd` — `m ∣ y ⇒ m² ∣ A(y)` (the `b = 0` doubling; `A(y) = y²(3−2y)`).
* `todaAmp_sub_one_dvd` — `m ∣ (y−1) ⇒ m² ∣ (A(y) − 1)` (the `b = 1` doubling; `A(y) − 1 = −(y−1)²(2y+1)`).
* `todaAmp_amplifies` — combined: `b ∈ {0,1}` and `m ∣ (y − b) ⇒ m² ∣ (A(y) − b)`.

## Honest scope

This is the **doubling core** of Toda's amplification — the one mechanism that lets a low-degree
modular indicator reach high modulus at polylog degree.  The full integer-route construction (the
`k`-fold iteration, composing it with the bottom-`AND` count, and the degree-`polylog`/quasipoly-support
bookkeeping that yields an *exact* `SYM∘AND` for unbounded `AND`/`OR`) is the remaining wall and is
**not** built here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TodaAmplify

/-- **Toda's modulus-amplification polynomial** `A(y) = 3y² − 2y³`. -/
def todaAmp (y : ℤ) : ℤ := 3 * y ^ 2 - 2 * y ^ 3

@[simp] theorem todaAmp_zero : todaAmp 0 = 0 := by simp [todaAmp]

@[simp] theorem todaAmp_one : todaAmp 1 = 1 := by simp [todaAmp]

/-- **The `b = 0` doubling (proved): `m ∣ y ⇒ m² ∣ A(y)`.**  `A(y) = y²(3−2y)`. -/
theorem todaAmp_dvd {m y : ℤ} (h : m ∣ y) : m ^ 2 ∣ todaAmp y := by
  have h2 : m ^ 2 ∣ y ^ 2 := pow_dvd_pow_of_dvd h 2
  have h3 : y ^ 2 ∣ todaAmp y := ⟨3 - 2 * y, by rw [todaAmp]; ring⟩
  exact h2.trans h3

/-- **The `b = 1` doubling (proved): `m ∣ (y−1) ⇒ m² ∣ (A(y) − 1)`.**  `A(y) − 1 = −(y−1)²(2y+1)`. -/
theorem todaAmp_sub_one_dvd {m y : ℤ} (h : m ∣ (y - 1)) : m ^ 2 ∣ (todaAmp y - 1) := by
  have h2 : m ^ 2 ∣ (y - 1) ^ 2 := pow_dvd_pow_of_dvd h 2
  have h3 : (y - 1) ^ 2 ∣ (todaAmp y - 1) := ⟨-(2 * y + 1), by rw [todaAmp]; ring⟩
  exact h2.trans h3

/-- **Modulus doubling for `b ∈ {0,1}` (proved): `m ∣ (y − b) ⇒ m² ∣ (A(y) − b)`.**  Each application of
`A` squares the modulus to which `y`'s `{0,1}` residue is preserved. -/
theorem todaAmp_amplifies {m y b : ℤ} (hb : b = 0 ∨ b = 1) (h : m ∣ (y - b)) :
    m ^ 2 ∣ (todaAmp y - b) := by
  rcases hb with rfl | rfl
  · simpa using todaAmp_dvd (by simpa using h)
  · exact todaAmp_sub_one_dvd h

/-!
**Toda amplification core proved.**  `A(y) = 3y² − 2y³` fixes `{0,1}` and squares the modulus precision
of a `{0,1}` residue.  Iterating reaches modulus `p^{2^k}` at degree `polylog` — the integer-route
bypass of the unbounded-`AND`/`OR` no-go.  The `k`-fold iteration + count composition + degree
bookkeeping (the full exact-quasipoly `SYM∘AND` for unbounded `AND`/`OR`) is the remaining wall, not
built.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0TodaAmplify

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TodaAmplify.todaAmp_amplifies
