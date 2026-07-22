import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA9f

/-!
# Shrinkage brick A9g: the shrinkage inequality, modulo one counting fact

Assembling A9e (union bound) with A9f (assembly) reduces the whole Andreev
shrinkage to a single pure permutation-counting inequality:

* **`bigN_le_two_hitCount` (proved)** — if the total miss count is at most half
  the sequences (`2·Σ_bi missCount ≤ bigN`), then good sequences are at least
  half (`bigN ≤ 2·hitCount`);
* **`andreev_shrinkage_of_miss` (proved)** — hence, modulo that counting fact,
  the exact Andreev shrinkage inequality
  `bigN·dmsizeC f ≤ 2·shrinkP·dmsizeC(andreevStar f) + 2·r·bigN` holds for every
  `f`.

**This is the honest endgame.** The entire Subbotovskaya/Andreev shrinkage
argument is now machine-checked except for `AndreevMissBound`, the standard
counting fact that `2·Σ_bi missCount ≤ bigN` — a permutation inequality
(`missCount bi r univ = 2^r·P(r,m)·P(n−m,r−m)` and `2k·P(r,m) ≤ P(n,m)` for the
right parameters).  This replaces the original whole-shrinkage fence
`AndreevShrinkage`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

open scoped Classical

/-- **Good sequences are at least half, given the miss bound (proved).** -/
theorem bigN_le_two_hitCount {k m : ℕ} (hm : 0 < m) (r : ℕ)
    (hmiss : 2 * (∑ bi : Fin k, missCount hm bi r (Finset.univ : Finset (Fin (k * m))))
      ≤ bigN (k * m) r) :
    bigN (k * m) r ≤ 2 * hitCount hm r (Finset.univ : Finset (Fin (k * m))) := by
  have hub := seqCount_le_hit_add_miss hm r (Finset.univ : Finset (Fin (k * m)))
  have hseq := seqCount_eq_bigN r (Finset.univ : Finset (Fin (k * m)))
  have hcard : (Finset.univ : Finset (Fin (k * m))).card = k * m := by
    rw [Finset.card_univ, Fintype.card_fin]
  rw [hcard] at hseq
  rw [hseq] at hub
  omega

/-- **THE ANDREEV SHRINKAGE INEQUALITY, modulo the miss bound (proved).** -/
theorem andreev_shrinkage_of_miss {k m : ℕ} (hm : 0 < m) (hk : 0 < k)
    (f : (Fin k → Bool) → Bool) (r : ℕ) (hr : r + 2 ≤ k * m)
    (hmiss : 2 * (∑ bi : Fin k, missCount hm bi r (Finset.univ : Finset (Fin (k * m))))
      ≤ bigN (k * m) r) :
    bigN (k * m) r * dmsizeC f
      ≤ 2 * (shrinkP (k * m) r * dmsizeC (andreevStar hm f))
        + 2 * (r * bigN (k * m) r) :=
  andreev_lb_of_count hm hk f r hr (bigN_le_two_hitCount hm r hmiss)

/- The single remaining unproved ingredient is the PER-PARAMETER miss bound
`2·Σ_bi missCount ≤ bigN` — a pure ℕ permutation-counting fact, TRUE for the
balanced parameters (free-set size `n − r ≈ 2k·log(2k)`) but FALSE in general
(e.g. `r = n`, where every block is missed).  It is therefore taken as a
per-`(k,m,r)` hypothesis (`hmiss` above), NOT a universal fence.  It reduces
(A9h/A9i) to the falling-factorial inequality `2k·perm r m ≤ perm n m`. -/

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.bigN_le_two_hitCount
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.andreev_shrinkage_of_miss
