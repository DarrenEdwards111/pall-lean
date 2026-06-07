import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockDepthBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingBridge

/-!
# Block-DT model, foundation 9: the quantitative holographic switching count (branch only)

Combining the holographic injection (`block_count`), the leaf-depth bound (`stars_blockEncode_le`), and
the shell cardinality (`card_stars_eq`), we get the quantitative count: a `K`-star, `s`-block bad set
injects into the **`≤ (K-s)`-star shell** times the label space.

* `card_stars_le` — `|{σ : stars σ ≤ m}| = ∑_{j≤m} C(n,j)·2^(n-j)`.
* `block_switching_count` — **the packaged theorem**:
  `|Bad| ≤ |{σ : stars σ ≤ K-s}| · |Labels|`,
  for any `Bad` of `K`-star, `s`-block restrictions whose stars-patterns lie in `Labels`.

Clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.

**Honest scope.**  `Labels` is the set of stars-patterns (`blockMasks` values).  This theorem leaves the
*size* of `Labels` as a parameter.  Bounding it by `(2^w)^s` (the canonical switching-count base, with
**no** `|cs|` factor) requires re-encoding `blockMasks` from global-variable masks to per-block in-clause
positions (`< w`) — the analogue of the depth-3 `PathLabel`/`card_pathLabels` machinery.  That is a
*construction*, not arithmetic, and is the one piece still open in this block-DT arc.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The number of restrictions with at most `m` stars: the sum of the shell cardinalities. -/
theorem card_stars_le (m : ℕ) :
    (Finset.univ.filter (fun σ : Restriction n => SwitchingCounting.stars σ ≤ m)).card
      = ∑ j ∈ Finset.range (m + 1), n.choose j * 2 ^ (n - j) := by
  classical
  have hdisj : (↑(Finset.range (m + 1)) : Set ℕ).PairwiseDisjoint
      (fun j => Finset.univ.filter (fun σ : Restriction n => SwitchingCounting.stars σ = j)) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro σ hi hj
    rw [Finset.mem_filter] at hi hj
    exact hij (hi.2.symm.trans hj.2)
  have hsum : (∑ j ∈ Finset.range (m + 1), n.choose j * 2 ^ (n - j))
      = ∑ j ∈ Finset.range (m + 1),
          (Finset.univ.filter (fun σ : Restriction n => SwitchingCounting.stars σ = j)).card := by
    apply Finset.sum_congr rfl
    intro j _; exact (SwitchingCounting.card_stars_eq j).symm
  rw [hsum, ← Finset.card_biUnion hdisj]
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_range]
  exact ⟨fun h => ⟨SwitchingCounting.stars σ, by omega, rfl⟩, fun ⟨j, hj, hσ⟩ => by omega⟩

/-- **The quantitative holographic switching count.**  A `K`-star, `s`-block bad set injects into the
`≤ (K-s)`-star shell times the label space. -/
theorem block_switching_count (cs : List (Clause n)) (F K s : ℕ)
    {Bad : Finset (Restriction n)} {Labels : Finset (List (Fin n → Bool))}
    (hstars : ∀ ρ ∈ Bad, SwitchingCounting.stars ρ = K)
    (hdepth : ∀ ρ ∈ Bad, (blockStream cs F ρ).length = s)
    (hL : ∀ ρ ∈ Bad, blockMasks cs F ρ ∈ Labels) :
    Bad.card
      ≤ (Finset.univ.filter (fun σ : Restriction n => SwitchingCounting.stars σ ≤ K - s)).card
        * Labels.card := by
  classical
  apply block_count cs F
  · intro ρ hρ
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h := stars_blockEncode_le cs F ρ
    rw [hstars ρ hρ, hdepth ρ hρ] at h
    exact h
  · exact hL

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.card_stars_le
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.block_switching_count
