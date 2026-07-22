import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA9n

/-!
# Shrinkage brick A9o: the Andreev DeMorgan formula lower bound

The squared shrinkage bound (A9n), combined with the counting bound (A6) and the
`dmsizeC ≤ lsize` bridge (A1), gives the Andreev DeMorgan formula lower bound:

* **`andreev_formula_lb_final` (proved)** — for parameters satisfying the range
  relations, the balance condition, and the counting condition, there is a
  `k`-bit hard function `f` such that EVERY DeMorgan formula computing
  `andreevStar f` (on `N = k·m` variables) has size `L` with
  `(B − 2r)²·N³ ≤ 4·L²·(N − r)³`.

With the standard parameter choice (`N − r ≈ 2k²`, `k ≈ log N`, `B` the counting
hardness), this reads `L ≳ N^{5/2}/polylog` — Andreev 1987, unconditional in the
formal sense that every hypothesis is a satisfiable parameter/counting relation,
no fences.  It is a DeMorgan-formula-size bound; its ceiling is `P ≠ NC¹`, not
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

open scoped Classical

/-- **THE ANDREEV DEMORGAN FORMULA LOWER BOUND (proved)**. -/
theorem andreev_formula_lb_final {k m : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (r B : ℕ)
    (hr : r + 2 ≤ k * m) (hmr : m ≤ r) (hcond : (2 * k - 1) * r ≤ m * (k * m - r))
    (hnum : (2 * B + 1) * (2 * k + 4) ^ (2 * B) < 2 ^ (2 ^ k)) :
    ∃ f : (Fin k → Bool) → Bool, ∀ t : DMTree (k * m),
      (∀ x, t.eval x = andreevStar hm f x) →
      (B - 2 * r) ^ 2 * (k * m) ^ 3 ≤ 4 * t.lsize ^ 2 * (k * m - r) ^ 3 := by
  obtain ⟨f, hf⟩ := exists_hard_card k B hnum
  refine ⟨f, fun t ht => ?_⟩
  have hsq := andreev_squared hm hk f r hr hmr hcond
  have hbridge : dmsizeC (andreevStar hm f) ≤ t.lsize := dmsizeC_le _ t ht
  have hB2 : (B - 2 * r) ^ 2 ≤ (dmsizeC f - 2 * r) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hL2 : dmsizeC (andreevStar hm f) ^ 2 ≤ t.lsize ^ 2 :=
    Nat.pow_le_pow_left hbridge 2
  calc (B - 2 * r) ^ 2 * (k * m) ^ 3
      ≤ (dmsizeC f - 2 * r) ^ 2 * (k * m) ^ 3 := Nat.mul_le_mul_right _ hB2
    _ ≤ 4 * dmsizeC (andreevStar hm f) ^ 2 * (k * m - r) ^ 3 := hsq
    _ ≤ 4 * t.lsize ^ 2 * (k * m - r) ^ 3 := by gcongr

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.andreev_formula_lb_final
