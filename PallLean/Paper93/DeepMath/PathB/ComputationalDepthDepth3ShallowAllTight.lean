import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightSwitchingBudget
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PNormalize

/-!
# Tight switching, step 11: a restriction collapsing all gates, `F`-independently (branch `razborov-recoverRho-wip`)

The tight analogue of `exists_shallow_all` (foundation 6).  The crude version caps each gate's bad weight
at `(2p/(1-p))^s·(4^w+1)^F` and union-bounds to `#gates · cap < 1`; the `(4^w+1)^F` factor makes the
threshold `F`-dependent and the depth-3 assembly vacuous.  Here we swap that cap for the **`F`-independent**
`tight_switching_budget` cap `r^s/(1-r)` (`r = (2p/(1-p))·(2w) = 4pw/(1-p)`):

```
  #gates · r^s/(1-r) < 1   ⟹   ∃ ρ, ∀ g ∈ G, (canonicalDT g F ρ).depth < s.
```

The union-bound threshold is now `s ≳ log #gates` — *no `F` anywhere*.  The proof is exactly that of
`exists_shallow_all`: `1 = ∑_ρ pweight ≤ ∑_ρ ∑_g 1[deep] pweight = ∑_g ∑_ρ 1[deep] pweight ≤ ∑_g cap =
#gates·cap`, with the inner per-gate bound supplied by `tight_switching_budget` instead of
`descent_switching_le`, and the single-literal canonical tree `canonicalDT` in place of the block tree
`canonicalDTree`.

## The standing hypotheses (honest)

As in `tight_switching_budget`, the per-gate bound carries the *global* alive (`hnf`), leaf (`hleaf`) and
position (`hpos`) hypotheses — the empty-skip wall (`decodedSel_not_filter_invariant`).  So this is the
`F`-independent collapse-existence step *conditional on the empty-skip wall*; the conditionality is the
irreducible switching-lemma content, surfaced explicitly, not hidden.

* `exists_shallow_all_tight` — `#gates · r^s/(1-r) < 1 ⟹ ∃ ρ, ∀ g ∈ G, (canonicalDT g F ρ).depth < s`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **A restriction collapsing all gates, `F`-independently.**  Under the global alive/leaf/position
hypotheses (per gate) and the tight regime `r < 1`, if the `F`-independent union bound
`#gates · r^s/(1-r) < 1` holds, some restriction makes every gate's single-literal canonical tree shallow
(`depth < s`). -/
theorem exists_shallow_all_tight {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s : ℕ} [NeZero w] (G : Finset (List (Clause n)))
    (hnf : ∀ g ∈ G, ∀ ρ : Restriction n, ∀ U ∈ g,
      SwitchingCounting.termFalsified ρ U = false)
    (hleaf : ∀ g ∈ G, ∀ ρ : Restriction n,
      SwitchingCounting.anyTermSat g (deepestEnd g F ρ) = false)
    (hpos : ∀ g ∈ G, ∀ ρ : Restriction n, ∀ q ∈ deepestFullSeq g F ρ, q.1 < w)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ)) < 1)
    (hsmall : (G.card : ℚ)
        * (((2 * p / (1 - p)) * (2 * (w : ℚ))) ^ s
            / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ)))) < 1) :
    ∃ ρ : Restriction n, ∀ g ∈ G, (canonicalDT g F ρ).depth < s := by
  classical
  by_contra hcon
  push_neg at hcon
  set cap : ℚ := ((2 * p / (1 - p)) * (2 * (w : ℚ))) ^ s
    / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ))) with hcap
  have hpw_nonneg : ∀ ρ : Restriction n, 0 ≤ pweight p ρ :=
    fun ρ => pweight_nonneg hp0 (by linarith) ρ
  have key : (1 : ℚ) ≤ (G.card : ℚ) * cap := by
    calc (1 : ℚ) = ∑ ρ : Restriction n, pweight p ρ := (pweight_sum_eq_one p).symm
      _ ≤ ∑ ρ : Restriction n, ∑ g ∈ G,
            (if s ≤ (canonicalDT g F ρ).depth then pweight p ρ else 0) := by
        apply Finset.sum_le_sum
        intro ρ _
        obtain ⟨g, hg, hgρ⟩ := hcon ρ
        have hnn : ∀ g' ∈ G,
            (0 : ℚ) ≤ (if s ≤ (canonicalDT g' F ρ).depth then pweight p ρ else 0) := by
          intro g' _
          split
          · exact hpw_nonneg ρ
          · exact le_refl 0
        have hsingle := Finset.single_le_sum hnn hg
        rwa [if_pos hgρ] at hsingle
      _ = ∑ g ∈ G, ∑ ρ : Restriction n,
            (if s ≤ (canonicalDT g F ρ).depth then pweight p ρ else 0) := Finset.sum_comm
      _ ≤ ∑ _g ∈ G, cap := by
        apply Finset.sum_le_sum
        intro g hg
        rw [← Finset.sum_filter]
        exact tight_switching_budget hp0 hp3 (cs := g)
          (hnf g hg) (hleaf g hg) (hpos g hg) hr1
      _ = (G.card : ℚ) * cap := by rw [Finset.sum_const, nsmul_eq_mul]
  linarith

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.exists_shallow_all_tight
