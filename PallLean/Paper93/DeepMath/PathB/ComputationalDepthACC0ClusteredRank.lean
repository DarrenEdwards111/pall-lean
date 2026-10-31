import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SupportSpanRank

/-!
# Clustered supports — `cellRank ≤ d + r` (a corollary of the support-span theorem)

A support system is **clustered** with `d` cluster centers and variation rank `r` if every support indicator is a
cluster center plus a variation drawn from an `r`-dimensional space:

```
(i ∈ supports j)  =  (∑_a cc_{j,a} · center_a(i))  +  (∑_m cv_{j,m} · V_m(i))
```

Then the indicators all lie in the `(d+r)`-dimensional span of `{center_a} ∪ {V_m}`, so this is exactly
`SupportsInRankSpan supports (d+r)` (with `B = append center V`, `c = append cc cv`), and the support-span theorem
(`…ACC0SupportSpanRank.cellRank_le_of_span`) gives `cellRank ≤ d + r`.  "Many gates but few observer degrees of
freedom = #clusters + variation rank."

## What is proved (clean axioms, no `sorry`)

* `ClusteredSupports supports d r` — the clustered decomposition (centers `+` `r`-dim variations).
* **`clustered_supports_in_span`** — `ClusteredSupports supports d r ⇒ SupportsInRankSpan supports (d + r)`
  (assembled via `Fin.append` and the `finSumFinEquiv` sum-split).
* **`clustered_supports_low_rank`** — `ClusteredSupports supports d r ⇒ cellRank supports L ≤ d + r`.
* **`clustered_low_correlation`** — `ClusteredSupports supports d r`, `2^{d+r} < n` ⇒ `LowHolonomyCorrelation`.

## Honest scope

A cheap but genuine rank corollary: it caps observer rank by `#clusters + variation rank`, subsuming bounded-distinct
(`r = 0`) and equal supports (`d = 1, r = 0`).  Still a fragment of `ACC0ForcesLowCellRank` (general `ACC⁰` is not
clustered with small `d + r`).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ClusteredRank

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0SupportSpanRank

variable {k n : ℕ}

/-- **Clustered supports**: each indicator is a cluster center (`d` of them) plus an `r`-dimensional variation. -/
def ClusteredSupports (supports : Fin k → Finset (Fin n)) (d r : ℕ) : Prop :=
  ∃ (center : Fin d → (Fin n → ZMod 2)) (V : Fin r → (Fin n → ZMod 2))
    (cc : Fin k → Fin d → ZMod 2) (cv : Fin k → Fin r → ZMod 2),
    ∀ j i, (if i ∈ supports j then (1 : ZMod 2) else 0)
      = (∑ a, cc j a * center a i) + (∑ m, cv j m * V m i)

/-- **Clustered ⇒ low-dimensional support-span (proved): `SupportsInRankSpan supports (d + r)`.** -/
theorem clustered_supports_in_span (supports : Fin k → Finset (Fin n)) (d r : ℕ)
    (h : ClusteredSupports supports d r) : SupportsInRankSpan supports (d + r) := by
  obtain ⟨center, V, cc, cv, hdec⟩ := h
  refine ⟨Fin.append center V, fun j => Fin.append (cc j) (cv j), ?_⟩
  intro j i
  rw [hdec j i, ← Equiv.sum_comp finSumFinEquiv
        (fun m => Fin.append (cc j) (cv j) m * Fin.append center V m i),
      Fintype.sum_sum_type]
  congr 1
  · exact Finset.sum_congr rfl (fun a _ => by
      rw [finSumFinEquiv_apply_left, Fin.append_left, Fin.append_left])
  · exact Finset.sum_congr rfl (fun m _ => by
      rw [finSumFinEquiv_apply_right, Fin.append_right, Fin.append_right])

/-- **Clustered supports have cell rank `≤ d + r` (proved).** -/
theorem clustered_supports_low_rank (supports : Fin k → Finset (Fin n)) (d r : ℕ)
    (h : ClusteredSupports supports d r) (L : Finset (Fin n)) :
    cellRank supports L ≤ d + r :=
  cellRank_le_of_span supports L (d + r) (clustered_supports_in_span supports d r h)

/-- **Unconditional low correlation for clustered supports (proved): `2^{d+r} < n`, any gate count `k`.** -/
theorem clustered_low_correlation (supports : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool)
    (d r : ℕ) (h : ClusteredSupports supports d r) (hn : 2 ^ (d + r) < n) :
    LowHolonomyCorrelation supports g :=
  supportSpan_low_correlation supports g (d + r) (clustered_supports_in_span supports d r h) hn

end PallLean.Paper93.DeepMath.PathB.ACC0ClusteredRank

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ClusteredRank.clustered_supports_in_span
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ClusteredRank.clustered_supports_low_rank
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ClusteredRank.clustered_low_correlation
