import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CellCountHardRegime

/-!
# Exact characterization of the cell-count socket — and why it is *false* in the hard regime

This file settles the open cell-count socket `FullACC0ForcesLowCellCount` *exactly*, and the conclusion is a genuine
limitation finding rather than a crack.

**Key structural fact.** `cellPatternVec supports v` ranges over *all* gates and is **independent of the live set `L`**.
So two live coordinates `v, w ∈ L` collapse to the same cell in `L.image (cellPatternVec supports)` **iff their full
patterns are equal** — and any gate that *separates* `v, w` contains one of them, hence intersects `L`, hence
*survives*.  Therefore a restriction can **never merge** two patterns: it can only *drop* coordinates.  Consequently:

```
(∃ L, cellPatternCount supports L < |L|)   ⟺   globalCellCount supports < n
                                           ⟺   the membership map  v ↦ cellPatternVec supports v  is not injective.
```

In particular the **hard regime** forces `globalCellCount = n` (since `globalCellCount ≤ n` always and the hard regime
demands `n ≤ globalCellCount`), i.e. the membership map is injective — so **`FullACC0ForcesLowCellCount` is false there.**

## What is proved (clean axioms, no `sorry`)

* **`globalCellCount_le_n`** — `globalCellCount supports ≤ n`.
* **`forcesLowCellCount_iff_global_lt`** — `FullACC0ForcesLowCellCount supports ↔ globalCellCount supports < n`.
* **`forcesLowCellCount_iff_not_injective`** — `… ↔ ¬ Function.Injective (cellPatternVec supports)`.
* **`not_forcesLowCellCount_of_hardRegime`** — `HardRegime supports univ ⇒ ¬ FullACC0ForcesLowCellCount supports`.

## Honest consequence — the route's exact ceiling

The cell-count observer collapse fires *exactly* when two coordinates already share a global membership pattern (e.g.
`2^k < n` by pigeonhole, or the structured fragments: laminar/sunflower/low-VC all *force* such a collision).  It does
**not** fire in the hard regime, where every coordinate has a distinct pattern — and crucially, restriction gives **no**
extra power in this membership-only model, because it cannot merge distinct patterns.  So `StructuredOverlappingMOD →
∃ L, cellPatternCount < |L|` is *false* whenever the structured family is genuinely hard (injective patterns); no such
theorem can be proved, and attempting one would be proving a falsehood.

To realize the N-Frame intuition that a restriction *merges* surviving gates' projected patterns, the observer model
must be upgraded so that fixing variables makes gates **constant** (dropping out of the pattern) — a strictly richer
model than this membership map.  Bounding the merged count *in that richer model* is the genuine open content; this
file proves that the *current* invariant cannot reach it.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CellCountCharacterization

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountRoute
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountSwitching
open PallLean.Paper93.DeepMath.PathB.ACC0DirectCellConcentration
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountHardRegime

variable {k n : ℕ}

/-- **`globalCellCount supports ≤ n` (proved): the `n` coordinates realize at most `n` distinct patterns.** -/
theorem globalCellCount_le_n (supports : Fin k → Finset (Fin n)) : globalCellCount supports ≤ n := by
  unfold globalCellCount cellPatternCount cellPatternImage
  calc (Finset.univ.image (cellPatternVec supports)).card
      ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
    _ = n := by simp

/-- **Exact characterization (proved): the socket holds iff the global pattern count drops below `n`.**  Restriction
cannot merge patterns (a separating gate always survives), so a per-`L` collapse exists iff two coordinates already
share a global pattern. -/
theorem forcesLowCellCount_iff_global_lt (supports : Fin k → Finset (Fin n)) :
    FullACC0ForcesLowCellCount supports ↔ globalCellCount supports < n := by
  constructor
  · rintro ⟨L, hL⟩
    have hL' : cellPatternCount supports L < L.card := hL
    have hninjL : ¬ Set.InjOn (cellPatternVec supports) (↑L) := by
      intro hinj
      have hcard : cellPatternCount supports L = L.card := Finset.card_image_of_injOn hinj
      omega
    have hninjU : ¬ Set.InjOn (cellPatternVec supports) (↑(Finset.univ : Finset (Fin n))) := by
      intro hinj
      exact hninjL (hinj.mono (Finset.coe_subset.mpr (Finset.subset_univ L)))
    have h2 : (Finset.univ.image (cellPatternVec supports)).card
        ≠ (Finset.univ : Finset (Fin n)).card :=
      fun he => hninjU (Finset.card_image_iff.mp he)
    have h1 : globalCellCount supports ≠ n := by
      simpa [globalCellCount, cellPatternCount, cellPatternImage] using h2
    exact lt_of_le_of_ne (globalCellCount_le_n supports) h1
  · intro h
    exact low_global_forces_lowCellCount supports h

/-- **Equivalently (proved): the socket holds iff the membership map is not injective.** -/
theorem forcesLowCellCount_iff_not_injective (supports : Fin k → Finset (Fin n)) :
    FullACC0ForcesLowCellCount supports ↔ ¬ Function.Injective (cellPatternVec supports) := by
  rw [forcesLowCellCount_iff_global_lt]
  constructor
  · intro h hinj
    have hge : globalCellCount supports = n := by
      unfold globalCellCount cellPatternCount cellPatternImage
      rw [Finset.card_image_of_injOn hinj.injOn]
      simp
    omega
  · intro hninj
    rw [Function.not_injective_iff] at hninj
    obtain ⟨v, w, hfvw, hvw⟩ := hninj
    have hninjU : ¬ Set.InjOn (cellPatternVec supports) (↑(Finset.univ : Finset (Fin n))) := by
      intro hinj
      exact hvw (hinj (by simp) (by simp) hfvw)
    have h2 : (Finset.univ.image (cellPatternVec supports)).card
        ≠ (Finset.univ : Finset (Fin n)).card :=
      fun he => hninjU (Finset.card_image_iff.mp he)
    have h1 : globalCellCount supports ≠ n := by
      simpa [globalCellCount, cellPatternCount, cellPatternImage] using h2
    exact lt_of_le_of_ne (globalCellCount_le_n supports) h1

/-- **The socket is false in the hard regime (proved).**  The hard regime demands `n ≤ globalCellCount`, but
`globalCellCount ≤ n` always, so `globalCellCount = n` (injective patterns) and the socket fails. -/
theorem not_forcesLowCellCount_of_hardRegime (supports : Fin k → Finset (Fin n))
    (h : HardRegime supports Finset.univ) : ¬ FullACC0ForcesLowCellCount supports := by
  rw [forcesLowCellCount_iff_global_lt]
  have h2 : n ≤ globalCellCount supports := by simpa using h.2
  omega

end PallLean.Paper93.DeepMath.PathB.ACC0CellCountCharacterization

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CellCountCharacterization.globalCellCount_le_n
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CellCountCharacterization.forcesLowCellCount_iff_global_lt
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CellCountCharacterization.forcesLowCellCount_iff_not_injective
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CellCountCharacterization.not_forcesLowCellCount_of_hardRegime
