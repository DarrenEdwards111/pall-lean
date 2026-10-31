import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA9e

/-!
# Shrinkage brick A9f: the assembly

The shrinkage telescope (upper bound, A5) meets the block-hitting lower bound
(A9d) at the Andreev function:

* **`andreev_core_ineq` (proved, unconditional)** — for every `f` and every
  restriction count `r ≤ n − 2`:
  `dmsizeC f · hitCount r univ ≤ shrinkP n r · dmsizeC(andreevStar f) + r · bigN n r`.
* **`andreev_lb_of_count` (proved)** — given the counting fact
  `bigN n r ≤ 2 · hitCount r univ` (good sequences are a constant fraction —
  the union-bound content, reduced in A9e to a permutation inequality):
  `bigN n r · dmsizeC f ≤ 2·shrinkP n r · dmsizeC(andreevStar f) + 2·r·bigN n r`.

This is the exact shrinkage inequality Andreev needs, with only the pure
counting fact `bigN ≤ 2·hitCount` (equivalently `Σ_bi missCount ≤ bigN/2`, a
standard permutation inequality) still to discharge.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

open scoped Classical

/-- **THE CORE INEQUALITY (proved, unconditional)**: shrinkage upper bound meets
block-hitting lower bound. -/
theorem andreev_core_ineq {k m : ℕ} (hm : 0 < m) (hk : 0 < k)
    (f : (Fin k → Bool) → Bool) (r : ℕ) (hr : r + 2 ≤ k * m) :
    dmsizeC f * hitCount hm r (Finset.univ : Finset (Fin (k * m)))
      ≤ shrinkP (k * m) r * dmsizeC (andreevStar hm f)
        + r * bigN (k * m) r := by
  -- lower bound via resSum_hit_ge (T = ∅)
  have hlow : dmsizeC f * hitCount hm r (Finset.univ : Finset (Fin (k * m)))
      ≤ resSum r Finset.univ (andreevStar hm f) := by
    have h := resSum_hit_ge hm hk f (dmsizeC f) (le_refl _) r Finset.univ ∅
      (fun _ => false) (Finset.disjoint_empty_right _)
    rwa [restrF_empty] at h
  -- upper bound via resSum_le on the minimal tree
  obtain ⟨t, hte, htl⟩ := Nat.sInf_mem (dmsizeC_set_nonempty (andreevStar hm f))
  have htl2 : t.lsize0 = dmsizeC (andreevStar hm f) := htl
  have hcard : (Finset.univ : Finset (Fin (k * m))).card = k * m := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hup := resSum_le r Finset.univ t (by rw [hcard]; exact hr)
    (fun i _ => Finset.mem_univ i)
  rw [hcard, htl2] at hup
  have hfe : (fun x => t.eval x) = andreevStar hm f := funext hte
  rw [hfe] at hup
  omega

/-- **THE CONDITIONAL LOWER BOUND (proved)**: given that good sequences are at
least half of all sequences, the exact Andreev shrinkage inequality. -/
theorem andreev_lb_of_count {k m : ℕ} (hm : 0 < m) (hk : 0 < k)
    (f : (Fin k → Bool) → Bool) (r : ℕ) (hr : r + 2 ≤ k * m)
    (hcount : bigN (k * m) r ≤ 2 * hitCount hm r (Finset.univ : Finset (Fin (k * m)))) :
    bigN (k * m) r * dmsizeC f
      ≤ 2 * (shrinkP (k * m) r * dmsizeC (andreevStar hm f))
        + 2 * (r * bigN (k * m) r) := by
  have hcore := andreev_core_ineq hm hk f r hr
  have h1 : dmsizeC f * bigN (k * m) r
      ≤ dmsizeC f * (2 * hitCount hm r (Finset.univ : Finset (Fin (k * m)))) :=
    Nat.mul_le_mul (le_refl _) hcount
  have h2 : dmsizeC f * (2 * hitCount hm r (Finset.univ : Finset (Fin (k * m))))
      = 2 * (dmsizeC f * hitCount hm r (Finset.univ : Finset (Fin (k * m)))) := by ring
  have h3 : dmsizeC f * bigN (k * m) r = bigN (k * m) r * dmsizeC f := by ring
  omega

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.andreev_core_ineq
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.andreev_lb_of_count
