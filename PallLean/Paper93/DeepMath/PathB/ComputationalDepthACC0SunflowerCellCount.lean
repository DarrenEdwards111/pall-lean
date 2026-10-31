import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0VCCellCount

/-!
# Sunflower (common-core) supports: wide overlap, yet `≤ k + 2` cells — a genuine overlapping fragment

A **sunflower** support system shares a common core and has pairwise-disjoint petals:

```
supports j = core ∪ petal j,      petal i, petal j  disjoint  (i ≠ j).
```

Every pair of supports *overlaps* in the whole core (so this is genuinely a *wide-overlap* family, **not** laminar:
`supports i ∩ supports j = core ≠ ∅` while neither is contained in the other).  Yet the gate-membership pattern of a
coordinate takes only one of `k + 2` shapes:

* a core coordinate lies in **every** support → pattern `univ`;
* a petal-`j₀` coordinate (not in the core) lies in support `j₀` **only** → pattern `{j₀}`;
* any other coordinate lies in **no** support → pattern `∅`.

So `cellPatternCount supports L ≤ k + 2`, and the predictor fails once `k + 2 < |L|`.  This is the canonical
"overlapping supports induce few coordinate-types" phenomenon — a direct instance of the N-Frame intuition that wide
overlap *helps*, and one the rank/laminar routes do not cover.

## What is proved (clean axioms, no `sorry`)

* `SunflowerSupports supports core petal` — common core, pairwise-disjoint petals.
* `sunflower_suppSet_core` / `_petal` / `_empty` — the three membership-set shapes.
* **`sunflower_cellPatternCount_le`** — `cellPatternCount supports L ≤ k + 2` (every cell is `univ`, a singleton, or `∅`).
* **`sunflower_low_correlation`** — `k + 2 < |L| ⇒ LowHolonomyCorrelation`, regardless of rank or survivor count.

## Honest scope

A clean structured instance of *wide overlap ⇒ few patterns*, genuinely outside laminar/low-rank.  But general
polynomially-many overlapping `MOD` supports need **not** be sunflower-structured — they can shatter large coordinate
sets (high observer VC dimension), in which case the cell count is *not* small.  So this confirms the phenomenon for a
structured overlap pattern; bounding the cell count for *arbitrary* overlapping `MOD` supports is the open
structural-concentration content (`NP ⊄ ACC⁰`-strength).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SunflowerCellCount

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountRoute
open PallLean.Paper93.DeepMath.PathB.ACC0ChainCellCount
open PallLean.Paper93.DeepMath.PathB.ACC0VCCellCount

variable {k n : ℕ}

/-- **Sunflower supports**: a common core with pairwise-disjoint petals. -/
def SunflowerSupports (supports : Fin k → Finset (Fin n)) (core : Finset (Fin n))
    (petal : Fin k → Finset (Fin n)) : Prop :=
  (∀ j, supports j = core ∪ petal j) ∧ (∀ i j, i ≠ j → Disjoint (petal i) (petal j))

/-- **Core coordinate ⇒ full pattern (proved).** -/
theorem sunflower_suppSet_core (supports : Fin k → Finset (Fin n)) (core : Finset (Fin n))
    (petal : Fin k → Finset (Fin n)) (hsf : SunflowerSupports supports core petal) (v : Fin n)
    (hv : v ∈ core) : suppSet supports v = Finset.univ := by
  ext j
  simp only [suppSet, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  rw [hsf.1 j]
  exact Finset.mem_union_left _ hv

/-- **Petal-`j₀` coordinate (not in core) ⇒ singleton pattern `{j₀}` (proved).** -/
theorem sunflower_suppSet_petal (supports : Fin k → Finset (Fin n)) (core : Finset (Fin n))
    (petal : Fin k → Finset (Fin n)) (hsf : SunflowerSupports supports core petal) (v : Fin n)
    (hvc : v ∉ core) (j₀ : Fin k) (hvp : v ∈ petal j₀) : suppSet supports v = {j₀} := by
  ext j
  simp only [suppSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [hsf.1 j, Finset.mem_union]
  constructor
  · rintro (hc | hp)
    · exact absurd hc hvc
    · by_contra hne
      exact (Finset.disjoint_left.mp (hsf.2 j j₀ hne) hp) hvp
  · rintro rfl
    exact Or.inr hvp

/-- **Coordinate outside core and all petals ⇒ empty pattern (proved).** -/
theorem sunflower_suppSet_empty (supports : Fin k → Finset (Fin n)) (core : Finset (Fin n))
    (petal : Fin k → Finset (Fin n)) (hsf : SunflowerSupports supports core petal) (v : Fin n)
    (hvc : v ∉ core) (hvp : ∀ j, v ∉ petal j) : suppSet supports v = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro j
  simp only [suppSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hsf.1 j, Finset.mem_union]
  push_neg
  exact ⟨hvc, hvp j⟩

/-- **Sunflower supports realize at most `k + 2` cells (proved).**  Every cell is the full set, a singleton, or `∅`. -/
theorem sunflower_cellPatternCount_le (supports : Fin k → Finset (Fin n)) (core : Finset (Fin n))
    (petal : Fin k → Finset (Fin n)) (hsf : SunflowerSupports supports core petal)
    (L : Finset (Fin n)) : cellPatternCount supports L ≤ k + 2 := by
  rw [← patternFamily_card supports L]
  have hsub : L.image (suppSet supports)
      ⊆ insert (Finset.univ : Finset (Fin k))
          (insert (∅ : Finset (Fin k))
            (Finset.univ.image (fun j : Fin k => ({j} : Finset (Fin k))))) := by
    intro S hS
    rw [Finset.mem_image] at hS
    obtain ⟨v, _, rfl⟩ := hS
    by_cases hvc : v ∈ core
    · rw [sunflower_suppSet_core supports core petal hsf v hvc]
      exact Finset.mem_insert_self _ _
    · by_cases hvp : ∃ j, v ∈ petal j
      · obtain ⟨j₀, hj₀⟩ := hvp
        rw [sunflower_suppSet_petal supports core petal hsf v hvc j₀ hj₀]
        exact Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j₀)))
      · push_neg at hvp
        rw [sunflower_suppSet_empty supports core petal hsf v hvc hvp]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  calc (L.image (suppSet supports)).card
      ≤ (insert (Finset.univ : Finset (Fin k))
          (insert (∅ : Finset (Fin k))
            (Finset.univ.image (fun j : Fin k => ({j} : Finset (Fin k)))))).card :=
        Finset.card_le_card hsub
    _ ≤ k + 2 := by
        have h1 : (Finset.univ.image (fun j : Fin k => ({j} : Finset (Fin k)))).card ≤ k := by
          refine le_trans Finset.card_image_le ?_
          simp
        have h2 := Finset.card_insert_le (∅ : Finset (Fin k))
          (Finset.univ.image (fun j : Fin k => ({j} : Finset (Fin k))))
        have h3 := Finset.card_insert_le (Finset.univ : Finset (Fin k))
          (insert (∅ : Finset (Fin k))
            (Finset.univ.image (fun j : Fin k => ({j} : Finset (Fin k)))))
        omega

/-- **Sunflower supports fail to correlate when `k + 2 < |L|` (proved), regardless of rank or survivor count.** -/
theorem sunflower_low_correlation (supports : Fin k → Finset (Fin n)) (core : Finset (Fin n))
    (petal : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool)
    (hsf : SunflowerSupports supports core petal) (L : Finset (Fin n)) (hkL : k + 2 < L.card) :
    LowHolonomyCorrelation supports g :=
  cellCountCollapse_implies_low_correlation supports g L
    (lt_of_le_of_lt (sunflower_cellPatternCount_le supports core petal hsf L) hkL)

end PallLean.Paper93.DeepMath.PathB.ACC0SunflowerCellCount

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SunflowerCellCount.sunflower_cellPatternCount_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SunflowerCellCount.sunflower_low_correlation
