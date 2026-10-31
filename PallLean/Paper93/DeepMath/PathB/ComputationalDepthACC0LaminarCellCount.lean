import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ChainCellCount

/-!
# Laminar (nested-or-disjoint) supports: still `≤ k + 1` cells — the chain fragment, generalized

A **laminar** family is one where any two supports are nested *or disjoint* (chains are the special case with no
disjoint pairs).  Laminar support systems can have full cell rank, yet still only `k + 1` distinct cell patterns:

For a laminar family the supports *containing a fixed coordinate* `v` are pairwise nested (they share `v`, so cannot be
disjoint) — i.e. they form a chain, with a unique `⊆`-minimal member `m(v)`.  And then the whole membership set is
determined by that minimal support:

```
suppSet v = { i : supports i ⊇ supports (m(v)) }   (the up-set of m(v)),
```

so every realized cell pattern is the indicator of one of the `k` up-sets `U_j = {i : supports j ⊆ supports i}` (or
the empty pattern).  Hence at most `k + 1` distinct cells.  The cardinality-injection trick used for chains fails here
(laminar `suppSet`s are not pairwise comparable), so this is a genuine strengthening, proved via the minimal-support
up-set characterisation.

## What is proved (clean axioms, no `sorry`)

* `LaminarSupports` — pairwise nested-or-disjoint; **`chain_isLaminar`** — every chain is laminar.
* `laminar_suppSet_eq` — for a `⊆`-minimal-card `j ∈ suppSet v`, `suppSet v = {i : supports j ⊆ supports i}`.
* **`laminar_cellPatternCount_le`** — `LaminarSupports supports ⇒ cellPatternCount supports L ≤ k + 1`.
* **`laminar_low_correlation`** — `LaminarSupports supports`, `k + 1 < |L|` ⇒ `LowHolonomyCorrelation`, regardless of rank.

## Honest scope

A structured case strictly broader than chains, still too crude for the rank route (full rank, few cells).  Still a
fragment (`k` laminar supports with `k + 1 < n`).  Forcing few cells for a general `ACC⁰` system under a restriction is
the open observer lemma (`ACC0ForcesLowCellCount`).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0LaminarCellCount

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountRoute
open PallLean.Paper93.DeepMath.PathB.ACC0ChainCellCount

variable {k n : ℕ}

/-- The supports form a **laminar family**: pairwise nested or disjoint. -/
def LaminarSupports (supports : Fin k → Finset (Fin n)) : Prop :=
  ∀ i j, supports i ⊆ supports j ∨ supports j ⊆ supports i ∨ Disjoint (supports i) (supports j)

/-- **Every chain is laminar (proved).** -/
theorem chain_isLaminar (supports : Fin k → Finset (Fin n)) (hch : ChainSupports supports) :
    LaminarSupports supports :=
  fun i j => (hch i j).imp id Or.inl

/-- **The minimal-support up-set characterisation (proved).**  If `j ∈ suppSet v` has `⊆`-minimal-cardinality among the
supports containing `v`, then `suppSet v` is exactly the up-set `{i : supports j ⊆ supports i}`. -/
theorem laminar_suppSet_eq (supports : Fin k → Finset (Fin n)) (hlam : LaminarSupports supports)
    (v : Fin n) (j : Fin k) (hjmem : j ∈ suppSet supports v)
    (hjmin : ∀ i ∈ suppSet supports v, (supports j).card ≤ (supports i).card) :
    suppSet supports v = Finset.univ.filter (fun i => supports j ⊆ supports i) := by
  simp only [suppSet, Finset.mem_filter, Finset.mem_univ, true_and] at hjmem
  ext i
  simp only [suppSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hvi
    have hi : i ∈ suppSet supports v := by
      simp only [suppSet, Finset.mem_filter, Finset.mem_univ, true_and]; exact hvi
    rcases hlam i j with hij | hji | hdisj
    · have heq : supports i = supports j := Finset.eq_of_subset_of_card_le hij (hjmin i hi)
      intro x hx
      rw [heq]; exact hx
    · exact hji
    · exact absurd hjmem (Finset.disjoint_left.mp hdisj hvi)
  · intro hsub
    exact hsub hjmem

/-- **Laminar supports have at most `k + 1` cell patterns (proved).**  Every realized pattern is the indicator of an
up-set `U_j = {i : supports j ⊆ supports i}` (or the empty pattern), and there are `k` up-sets. -/
theorem laminar_cellPatternCount_le (supports : Fin k → Finset (Fin n))
    (hlam : LaminarSupports supports) (L : Finset (Fin n)) :
    cellPatternCount supports L ≤ k + 1 := by
  have hmaps : ∀ p ∈ L.image (cellPatternVec supports),
      (fun p => Finset.univ.filter (fun i : Fin k => p i = 1)) p
        ∈ insert (∅ : Finset (Fin k))
            (Finset.univ.image
              (fun j : Fin k => Finset.univ.filter (fun i => supports j ⊆ supports i))) := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨v, _, rfl⟩ := hp
    simp only [oneSet_eq_suppSet]
    rcases (suppSet supports v).eq_empty_or_nonempty with he | hne
    · rw [he]; exact Finset.mem_insert_self _ _
    · obtain ⟨j, hjmem, hjmin⟩ :=
        Finset.exists_min_image (suppSet supports v) (fun i => (supports i).card) hne
      rw [laminar_suppSet_eq supports hlam v j hjmem hjmin]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have hinj : Set.InjOn (fun p : Fin k → ZMod 2 => Finset.univ.filter (fun i : Fin k => p i = 1))
      ↑(L.image (cellPatternVec supports)) := by
    intro p hp p' hp' hpp
    rw [Finset.mem_coe, Finset.mem_image] at hp hp'
    obtain ⟨v, _, rfl⟩ := hp
    obtain ⟨w, _, rfl⟩ := hp'
    simp only [oneSet_eq_suppSet] at hpp
    exact cellPatternVec_eq_of_suppSet supports v w hpp
  have key : (L.image (cellPatternVec supports)).card
      ≤ (insert (∅ : Finset (Fin k))
          (Finset.univ.image
            (fun j : Fin k => Finset.univ.filter (fun i => supports j ⊆ supports i)))).card :=
    Finset.card_le_card_of_injOn _ hmaps hinj
  calc cellPatternCount supports L = (L.image (cellPatternVec supports)).card := rfl
    _ ≤ (insert (∅ : Finset (Fin k))
          (Finset.univ.image
            (fun j : Fin k => Finset.univ.filter (fun i => supports j ⊆ supports i)))).card := key
    _ ≤ (Finset.univ.image
            (fun j : Fin k => Finset.univ.filter (fun i => supports j ⊆ supports i))).card + 1 :=
        Finset.card_insert_le _ _
    _ ≤ k + 1 := by
        have hle : (Finset.univ.image
              (fun j : Fin k => Finset.univ.filter (fun i => supports j ⊆ supports i))).card ≤ k :=
          calc (Finset.univ.image
                  (fun j : Fin k => Finset.univ.filter (fun i => supports j ⊆ supports i))).card
              ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
            _ = k := by rw [Finset.card_univ, Fintype.card_fin]
        omega

/-- **Laminar supports fail to correlate when `k + 1 < |L|` (proved), regardless of cell rank.** -/
theorem laminar_low_correlation (supports : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool)
    (hlam : LaminarSupports supports) (L : Finset (Fin n)) (hkL : k + 1 < L.card) :
    LowHolonomyCorrelation supports g :=
  cellCountCollapse_implies_low_correlation supports g L
    (lt_of_le_of_lt (laminar_cellPatternCount_le supports hlam L) hkL)

end PallLean.Paper93.DeepMath.PathB.ACC0LaminarCellCount

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LaminarCellCount.chain_isLaminar
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LaminarCellCount.laminar_cellPatternCount_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LaminarCellCount.laminar_low_correlation
