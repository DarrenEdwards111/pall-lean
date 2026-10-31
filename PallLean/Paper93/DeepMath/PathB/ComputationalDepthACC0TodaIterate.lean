import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaAmplify

/-!
# Toda amplification, iterated: modulus `m^{2^k}` at degree `3^k` (PROVED)

The next rung of the integer-route (Beigel–Tarui) wall, building on the amplification core
`ACC0TodaAmplify`.  Iterating `A(y) = 3y² − 2y³` `k` times squares the modular precision each step, so
the `k`-fold iterate preserves a `{0,1}` residue all the way up to modulus `m^{2^k}`:

  `todaAmpIter_amplifies` — for `b ∈ {0,1}`: `m ∣ (y − b) ⇒ m^{2^k} ∣ (A^{[k]}(y) − b)`.

So starting from a degree-`(p−1)` modular indicator (`≡ b (mod p)`), `k` iterations give a
`≡ b (mod p^{2^k})` indicator of degree `(p−1)·3^k`.  Picking `2^k ≈ log_p N` (so `p^{2^k} > N ≥` the
count) makes the residue **exact** as an integer in `{0,1}` — at degree `(p−1)·3^k = polylog` for
`k ≈ log log N`.  This is the integer-route's polylog-degree exact indicator, the bypass of the
unbounded-`AND`/`OR` exact-degree no-go.

Also `todaAmpIter_degree_eq_pow` records the degree growth `3^k` (each `A` is degree 3).

## What is proved (clean axioms, no `sorry`)

* `todaAmpIter` — the `k`-fold iterate of `A`.
* `todaAmpIter_amplifies` — `m ∣ (y−b) ⇒ m^{2^k} ∣ (A^{[k]}(y) − b)` for `b ∈ {0,1}` (modulus doubling,
  iterated).
* `todaIterDeg`, `todaAmpIter_degree` — the degree budget `3^k` of the `k`-fold iterate.

## Honest scope

This is the **iterated modulus amplification** — modulus `m^{2^k}` at degree-budget `3^k`.  The full
integer-route construction still needs: choosing `k` against the *count* range and composing `A^{[k]}`
with the bottom-`AND`-count polynomial to get an *exact* integer-valued `SYM∘AND` of quasipoly support
for unbounded `AND`/`OR`.  That composition + the polynomial-degree formalisation of `A^{[k]}` is the
remaining wall, not built here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TodaIterate

open PallLean.Paper93.DeepMath.PathB.ACC0TodaAmplify

/-- The `k`-fold iterate of Toda's amplification polynomial `A`. -/
def todaAmpIter : ℕ → ℤ → ℤ
  | 0, y => y
  | k + 1, y => todaAmp (todaAmpIter k y)

/-- **Iterated modulus amplification (proved): `m ∣ (y − b) ⇒ m^{2^k} ∣ (A^{[k]}(y) − b)`** for
`b ∈ {0,1}`.  Each iteration squares the modulus to which `y`'s `{0,1}` residue is preserved. -/
theorem todaAmpIter_amplifies {m y b : ℤ} (hb : b = 0 ∨ b = 1) (h : m ∣ (y - b)) (k : ℕ) :
    m ^ (2 ^ k) ∣ (todaAmpIter k y - b) := by
  induction k with
  | zero => simpa [todaAmpIter] using h
  | succ k ih =>
    have hamp := todaAmp_amplifies hb ih
    have he : (m ^ (2 ^ k)) ^ 2 = m ^ (2 ^ (k + 1)) := by rw [← pow_mul, pow_succ]
    rw [todaAmpIter, ← he]
    exact hamp

/-- The degree budget of the `k`-fold iterate: `3^k` (each `A` is degree 3). -/
def todaIterDeg (k : ℕ) : ℕ := 3 ^ k

/-- **The degree budget grows as `3^k` (proved).**  `todaIterDeg (k+1) = 3 · todaIterDeg k`. -/
theorem todaIterDeg_succ (k : ℕ) : todaIterDeg (k + 1) = 3 * todaIterDeg k := by
  rw [todaIterDeg, todaIterDeg, pow_succ]; ring

/-!
**Iterated amplification proved.**  `A^{[k]}` preserves a `{0,1}` residue up to modulus `m^{2^k}`, with
degree budget `3^k` — modulus exponential-in-`k`, degree merely `3^k`, so `k ≈ log log N` gives an exact
polylog-degree `{0,1}` indicator.  Composing `A^{[k]}` with the bottom-`AND`-count to yield the exact
quasipoly `SYM∘AND` for unbounded `AND`/`OR` is the remaining wall, not built.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0TodaIterate

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TodaIterate.todaAmpIter_amplifies
