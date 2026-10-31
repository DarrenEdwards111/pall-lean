import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA9j

/-!
# Shrinkage brick A9k: the Andreev shrinkage inequality, conditional on one
falling-factorial inequality

The capstone of the discharge.  Combining the assembly (A9g) with the miss bound
(A9j), the exact Andreev shrinkage inequality holds for every `f`, conditional
ONLY on the clean `ℕ` falling-factorial inequality `2k·perm r m ≤ perm (k·m) m`
(together with the range conditions `m ≤ r` and `r + 2 ≤ k·m`):

* **`andreev_shrinkage_of_perm` (proved)** —
  `bigN·dmsizeC f ≤ 2·shrinkP·dmsizeC(andreevStar f) + 2·r·bigN`.

The original whole-shrinkage fence `AndreevShrinkage` has been reduced, through
A9a–A9j, to `2k·perm r m ≤ perm (k·m) m` — a standard statement about falling
factorials, true for the balanced parameters (free-set size `k·m − r ≈ k·log k`).
Everything else in the Subbotovskaya/Andreev shrinkage argument is now
machine-checked.  Nothing here is `P ≠ NP` — it is a DeMorgan-formula-size
result, capped below `NC¹`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

open scoped Classical

/-- **THE ANDREEV SHRINKAGE INEQUALITY, conditional on the falling-factorial
inequality (proved).** -/
theorem andreev_shrinkage_of_perm {k m : ℕ} (hm : 0 < m) (hk : 0 < k)
    (f : (Fin k → Bool) → Bool) (r : ℕ) (hr : r + 2 ≤ k * m) (hmr : m ≤ r)
    (hperm : 2 * k * perm r m ≤ perm (k * m) m) :
    bigN (k * m) r * dmsizeC f
      ≤ 2 * (shrinkP (k * m) r * dmsizeC (andreevStar hm f))
        + 2 * (r * bigN (k * m) r) :=
  andreev_shrinkage_of_miss hm hk f r hr (miss_bound_of_perm hm r hmr hperm)

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.andreev_shrinkage_of_perm
