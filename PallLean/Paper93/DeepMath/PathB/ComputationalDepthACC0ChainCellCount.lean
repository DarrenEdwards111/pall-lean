import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CellCountRoute

/-!
# Chain (nested) supports: few cells even at full rank — the class the rank route misses

Nested supports `S_1 ⊆ S_2 ⊆ … ⊆ S_k` can have **full cell rank** (the prefix indicators are linearly independent),
yet only `k + 1` distinct cell patterns: each coordinate's membership pattern is a *threshold* (an up-set of the
chain).  This is exactly observer/N-Frame territory — *cells* matter, not rank — and it is handled by the direct
cell-count route (`…ACC0CellCountRoute`), not the rank route.

The proof: for a chain, the membership sets `suppSet v = {j : v ∈ S_j}` are **pairwise comparable** (if `v ∈ S_j`,
`w ∈ S_{j'}` with `j ∉ suppSet w`, `j' ∉ suppSet v`, comparability of `S_j, S_{j'}` gives a contradiction).  Comparable
finsets of equal cardinality are equal, so the cardinality map is **injective** on the cell patterns — hence at most
`k + 1` of them.

## What is proved (clean axioms, no `sorry`)

* `ChainSupports` / `suppSet`; `suppSet_comparable` — the membership sets of a chain are pairwise comparable.
* **`chain_cellPatternCount_le`** — `ChainSupports supports ⇒ cellPatternCount supports L ≤ k + 1`.
* **`chain_low_correlation`** — `ChainSupports supports`, `k + 1 < |L|` ⇒ `LowHolonomyCorrelation` (via the cell-count
  bridge), *regardless of the cell rank*.

## Honest scope

A structured case the rank route is too crude for: nested supports have high rank but few cells.  Still a fragment
(a chain of `k` supports with `k + 1 < n`).  Forcing few cells for a general `ACC⁰` system under a restriction is the
open observer lemma (`ACC0ForcesLowCellCount`, `NP ⊄ ACC⁰`-strength).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ChainCellCount

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountRoute

variable {k n : ℕ}

/-- The supports form a **chain**: pairwise comparable under `⊆`. -/
def ChainSupports (supports : Fin k → Finset (Fin n)) : Prop :=
  ∀ i j, supports i ⊆ supports j ∨ supports j ⊆ supports i

/-- The membership set of a coordinate: the gates whose support contains it. -/
def suppSet (supports : Fin k → Finset (Fin n)) (v : Fin n) : Finset (Fin k) :=
  Finset.univ.filter (fun j => v ∈ supports j)

/-- **The membership sets of a chain are pairwise comparable (proved).** -/
theorem suppSet_comparable (supports : Fin k → Finset (Fin n)) (hch : ChainSupports supports)
    (v w : Fin n) : suppSet supports v ⊆ suppSet supports w ∨ suppSet supports w ⊆ suppSet supports v := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [Finset.not_subset] at h1 h2
  obtain ⟨j, hjv, hjnw⟩ := h1
  obtain ⟨j', hj'w, hj'nv⟩ := h2
  simp only [suppSet, Finset.mem_filter, Finset.mem_univ, true_and] at hjv hjnw hj'w hj'nv
  rcases hch j j' with hsub | hsub
  · exact hj'nv (hsub hjv)
  · exact hjnw (hsub hj'w)

/-- The one-set of a cell pattern is the coordinate's membership set (proved). -/
theorem oneSet_eq_suppSet (supports : Fin k → Finset (Fin n)) (v : Fin n) :
    (Finset.univ.filter (fun j => cellPatternVec supports v j = 1)) = suppSet supports v := by
  ext j
  simp only [suppSet, Finset.mem_filter, Finset.mem_univ, true_and, cellPatternVec]
  by_cases h : v ∈ supports j <;> simp [h]

/-- Equal membership sets give equal cell patterns (proved). -/
theorem cellPatternVec_eq_of_suppSet (supports : Fin k → Finset (Fin n)) (v w : Fin n)
    (h : suppSet supports v = suppSet supports w) :
    cellPatternVec supports v = cellPatternVec supports w := by
  have hiff : ∀ j, (v ∈ supports j) ↔ (w ∈ supports j) := by
    intro j
    have : j ∈ suppSet supports v ↔ j ∈ suppSet supports w := by rw [h]
    simpa only [suppSet, Finset.mem_filter, Finset.mem_univ, true_and] using this
  funext j
  simp only [cellPatternVec]
  by_cases hv : v ∈ supports j
  · rw [if_pos hv, if_pos ((hiff j).mp hv)]
  · rw [if_neg hv, if_neg (fun hw => hv ((hiff j).mpr hw))]

/-- **Chain supports have at most `k + 1` cell patterns (proved).**  The cardinality of the membership set is
injective on the (pairwise comparable) cell patterns, and lands in `{0,…,k}`. -/
theorem chain_cellPatternCount_le (supports : Fin k → Finset (Fin n))
    (hch : ChainSupports supports) (L : Finset (Fin n)) :
    cellPatternCount supports L ≤ k + 1 := by
  have hbound : cellPatternCount supports L
      ≤ (Finset.range (k + 1)).card := by
    apply Finset.card_le_card_of_injOn
      (fun p => (Finset.univ.filter (fun j : Fin k => p j = 1)).card)
    · intro p _
      simp only [Finset.mem_coe, Finset.mem_range]
      have h1 : (Finset.univ.filter (fun j : Fin k => p j = 1)).card ≤ k :=
        calc (Finset.univ.filter (fun j : Fin k => p j = 1)).card
            ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_filter_le _ _
          _ = k := by rw [Finset.card_univ, Fintype.card_fin]
      omega
    · intro p hp p' hp' hpc
      simp only [cellPatternImage, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hp hp'
      obtain ⟨v, _, rfl⟩ := hp
      obtain ⟨w, _, rfl⟩ := hp'
      simp only [oneSet_eq_suppSet] at hpc
      have hsuppeq : suppSet supports v = suppSet supports w := by
        rcases suppSet_comparable supports hch v w with hsub | hsub
        · exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hpc.symm)
        · exact (Finset.eq_of_subset_of_card_le hsub (le_of_eq hpc)).symm
      exact cellPatternVec_eq_of_suppSet supports v w hsuppeq
  rwa [Finset.card_range] at hbound

/-- **Chain supports fail to correlate when `k + 1 < |L|` (proved), regardless of cell rank.** -/
theorem chain_low_correlation (supports : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool)
    (hch : ChainSupports supports) (L : Finset (Fin n)) (hkL : k + 1 < L.card) :
    LowHolonomyCorrelation supports g :=
  cellCountCollapse_implies_low_correlation supports g L
    (lt_of_le_of_lt (chain_cellPatternCount_le supports hch L) hkL)

end PallLean.Paper93.DeepMath.PathB.ACC0ChainCellCount

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ChainCellCount.chain_cellPatternCount_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ChainCellCount.chain_low_correlation
