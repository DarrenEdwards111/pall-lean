import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA9l
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA9k

/-!
# Shrinkage brick A9m: the Andreev shrinkage inequality, UNCONDITIONAL

Wiring the falling-factorial inequality (A9l) into the capstone (A9k) removes
the last fence: the exact Andreev shrinkage inequality now holds with **no
unproved ingredients**, conditional only on parameter *relations* (`m ≤ r`,
`r + 2 ≤ k·m`, and the balance `(2k−1)·r ≤ m·(k·m − r)` — all satisfiable, e.g.
free-set size `k·m − r ≈ 2k²`):

* **`andreev_shrinkage_final` (proved)** —
  `bigN·dmsizeC f ≤ 2·shrinkP·dmsizeC(andreevStar f) + 2·r·bigN`, for every `f`.

The `AndreevShrinkage` fence I began this arc with is fully discharged.  The
entire Subbotovskaya/Andreev shrinkage argument is machine-checked.  What
remains for the numerical `n^{5/2}` is the `shrinkP/bigN` ratio bound and the
parameter instantiation (both pure arithmetic).  This is a DeMorgan-formula-size
result — its ceiling is `P ≠ NC¹`, not `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

open scoped Classical

/-- **THE ANDREEV SHRINKAGE INEQUALITY, UNCONDITIONAL (proved)** — no fences,
only parameter relations. -/
theorem andreev_shrinkage_final {k m : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (f : (Fin k → Bool) → Bool) (r : ℕ) (hr : r + 2 ≤ k * m) (hmr : m ≤ r)
    (hcond : (2 * k - 1) * r ≤ m * (k * m - r)) :
    bigN (k * m) r * dmsizeC f
      ≤ 2 * (shrinkP (k * m) r * dmsizeC (andreevStar hm f))
        + 2 * (r * bigN (k * m) r) := by
  refine andreev_shrinkage_of_perm hm hk f r hr hmr ?_
  exact two_k_perm_le k m r (k * m) hk hm hmr (by omega) hcond

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.andreev_shrinkage_final
