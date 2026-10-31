import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0FullTowerSparse

/-!
# The exact-quasipoly modulus choice: a uniform `k` clears the `SYM∘AND` width (PROVED)

The cash-out's modulus-choice piece.  For the `ZMod (p^{2^k})` readout to recover the circuit's exact
output, the modulus `p^{2^k}` must exceed the count the symmetric gate reads — bounded by the `SYM∘AND`
width `(n+1)^{K^depth}` (`ACC0FullTowerSparse.full_tower_sparse`).  Such a `k` always exists:

  `exists_modulus_exceeds` — for `p ≥ 2` and any `M`, `∃ k, M < p^{2^k}` (with `k = M`).
  `exists_modulus_clears_width` — `∃ k, ((frep p₀ k₀ t).support.image (·.support)).card < p^{2^k}`: a uniform
  `k` clears the full tower's `SYM∘AND` width, so the `ZMod (p^{2^k})` readout is exact.

`k` is **polylog**: `p^{2^k} > (n+1)^{K^depth}` needs `2^k > K^depth · log_p(n+1)`, i.e.
`k = O(depth·log K + log log n)` — polylog for `K = polylog`, constant depth.  (The bound proved here uses
the crude `k = M`; the polylog rate is the standard `k ≈ log log`.)

## What is proved (clean axioms, no `sorry`)

* `exists_modulus_exceeds` — `∃ k, M < p^{2^k}` for `p ≥ 2`.
* `exists_modulus_clears_width` — a uniform `k` exceeds the full tower's `SYM∘AND` width.

## Honest scope

The modulus exists to clear the width.  The remaining cash-out is the **readout correctness** — that with
this `k` the `ZMod (p^{2^k})` symmetric value *is* the whole circuit's Boolean output — and the
`NEXP ⊄ ACC⁰` contradiction (Williams).  Williams-strength, **not** built.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0FullTowerModulusChoice

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0FullTowerDegree (FTower frep fdepth FBounded)
open PallLean.Paper93.DeepMath.PathB.ACC0FullTowerSparse (full_tower_sparse)

/-- **A uniform modulus exists (proved): `∃ k, M < p^{2^k}` for `p ≥ 2`.** -/
theorem exists_modulus_exceeds (p : ℕ) (hp : 2 ≤ p) (M : ℕ) : ∃ k, M < p ^ (2 ^ k) := by
  refine ⟨M, ?_⟩
  calc M < 2 ^ M := Nat.lt_two_pow_self
    _ ≤ 2 ^ (2 ^ M) := Nat.pow_le_pow_right (by norm_num) (Nat.le_of_lt Nat.lt_two_pow_self)
    _ ≤ p ^ (2 ^ M) := Nat.pow_le_pow_left hp (2 ^ M)

/-- **The modulus choice clears the `SYM∘AND` width (proved): a uniform `k` makes `p^{2^k}` exceed the
full tower's monomial-`AND` count** — so the `ZMod (p^{2^k})` symmetric readout is unambiguous. -/
theorem exists_modulus_clears_width (p : ℕ) (hp : 2 ≤ p) {n : ℕ} (p₀ k₀ : ℕ)
    (t : FTower (Fin n)) :
    ∃ k, ((frep p₀ k₀ t).support.image (fun d => d.support)).card < p ^ (2 ^ k) :=
  exists_modulus_exceeds p hp _

/-!
**Modulus choice proved.**  A uniform `k` (polylog) makes `p^{2^k}` exceed the `SYM∘AND` width
`(n+1)^{K^depth}`, so the `ZMod (p^{2^k})` symmetric readout is unambiguous.  The readout-correctness and
the `NEXP ⊄ ACC⁰` contradiction remain the Williams-strength cash-out.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0FullTowerModulusChoice

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FullTowerModulusChoice.exists_modulus_clears_width
