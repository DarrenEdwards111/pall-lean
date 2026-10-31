import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CellCountRoute

/-!
# Cell-count composition — `cellPatternCount` is submultiplicative under `append`

The cell-count analogue of the rank composition theorem, and the composition law the final N-Frame route needs.
When two support families are stacked (`Fin.append`), the append cell pattern is the *concatenation* of the two
patterns (`cellPatternVec (append A B) v = Fin.append (cellPatternVec A v) (cellPatternVec B v)`), and concatenation
is injective — so the number of distinct append cells is at most the *product* of the two cell counts:

```
cellPatternCount (append A B) L  ≤  cellPatternCount A L  *  cellPatternCount B L
```

Hence a cell-count collapse lifts through a layer once `cells₁ · cells₂ < |L|`.

## What is proved (clean axioms, no `sorry`)

* `cellPatternVec_append` — the append pattern is the concatenation of the two patterns.
* **`cellPatternCount_append_le`** — `cellPatternCount (append A B) L ≤ cellPatternCount A L * cellPatternCount B L`.
* **`cellCount_collapse_lifts`** — `cellPatternCount A L * cellPatternCount B L < |L| ⇒ CellCountCollapse (append A B) L`.
* **`cellCount_collapse_of_budget`** — the budget form: `cellPatternCount A L ≤ c₁`, `cellPatternCount B L ≤ c₂`,
  `c₁ * c₂ < |L| ⇒ CellCountCollapse (append A B) L`.

## Honest scope

This is the composition law for the sharpest observer invariant (cell count): depth composition multiplies cell
counts (vs the additive survivor count and the subadditive rank).  A layer that adds only `c₂` cells keeps the
composite within `c₁ · c₂`.  Whether a real `ACC⁰` layer keeps the cell count small is the open observer lemma
(`ACC0ForcesLowCellCount`).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CellCountComposition

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountRoute

variable {k₁ k₂ n : ℕ}

/-- **The append cell pattern is the concatenation of the two patterns (proved).** -/
theorem cellPatternVec_append (A : Fin k₁ → Finset (Fin n)) (B : Fin k₂ → Finset (Fin n)) (v : Fin n) :
    cellPatternVec (Fin.append A B) v
      = Fin.append (cellPatternVec A v) (cellPatternVec B v) := by
  funext j
  refine Fin.addCases (fun a => ?_) (fun b => ?_) j
  · simp only [cellPatternVec, Fin.append_left]
  · simp only [cellPatternVec, Fin.append_right]

/-- **Cell count is submultiplicative under `append` (proved).** -/
theorem cellPatternCount_append_le (A : Fin k₁ → Finset (Fin n)) (B : Fin k₂ → Finset (Fin n))
    (L : Finset (Fin n)) :
    cellPatternCount (Fin.append A B) L ≤ cellPatternCount A L * cellPatternCount B L := by
  unfold cellPatternCount cellPatternImage
  calc (L.image (cellPatternVec (Fin.append A B))).card
      ≤ (((L.image (cellPatternVec A)) ×ˢ (L.image (cellPatternVec B))).image
          (fun pr => Fin.append pr.1 pr.2)).card := by
        apply Finset.card_le_card
        intro p hp
        rw [Finset.mem_image] at hp
        obtain ⟨v, hv, rfl⟩ := hp
        rw [Finset.mem_image]
        refine ⟨(cellPatternVec A v, cellPatternVec B v), ?_, ?_⟩
        · rw [Finset.mem_product]
          exact ⟨Finset.mem_image_of_mem _ hv, Finset.mem_image_of_mem _ hv⟩
        · exact (cellPatternVec_append A B v).symm
    _ ≤ ((L.image (cellPatternVec A)) ×ˢ (L.image (cellPatternVec B))).card :=
        Finset.card_image_le
    _ = (L.image (cellPatternVec A)).card * (L.image (cellPatternVec B)).card :=
        Finset.card_product _ _

/-- **Cell-count collapse lifts through a layer (proved): `cells₁ · cells₂ < |L|`.** -/
theorem cellCount_collapse_lifts (A : Fin k₁ → Finset (Fin n)) (B : Fin k₂ → Finset (Fin n))
    (L : Finset (Fin n)) (h : cellPatternCount A L * cellPatternCount B L < L.card) :
    CellCountCollapse (Fin.append A B) L :=
  lt_of_le_of_lt (cellPatternCount_append_le A B L) h

/-- **The budget form (proved): a layer adding `≤ c₂` cells lifts the collapse if `c₁ · c₂ < |L|`.** -/
theorem cellCount_collapse_of_budget (A : Fin k₁ → Finset (Fin n)) (B : Fin k₂ → Finset (Fin n))
    (L : Finset (Fin n)) (c₁ c₂ : ℕ) (h₁ : cellPatternCount A L ≤ c₁)
    (h₂ : cellPatternCount B L ≤ c₂) (hbudget : c₁ * c₂ < L.card) :
    CellCountCollapse (Fin.append A B) L :=
  cellCount_collapse_lifts A B L
    (lt_of_le_of_lt (Nat.mul_le_mul h₁ h₂) hbudget)

end PallLean.Paper93.DeepMath.PathB.ACC0CellCountComposition

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CellCountComposition.cellPatternCount_append_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CellCountComposition.cellCount_collapse_lifts
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CellCountComposition.cellCount_collapse_of_budget
