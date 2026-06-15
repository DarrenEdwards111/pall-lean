import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CellCountRoute

/-!
# The refined (variable-fixing) observer model — restriction can merge patterns

The membership-only model (`cellPatternVec`) was proved to have a hard ceiling: a restriction can never merge two
distinct global patterns, because a gate separating two coordinates always contains one of them and hence survives
(`…ACC0CellCountCharacterization`).  This file builds the **richer** model the wall demands: a restriction is a partial
assignment `ρ : Fin n → Option Bool` (`none` = free), and a gate can become **constant** — and so drop out of the
observer pattern — even while it still contains a free coordinate.

We model the canonical `AND`-of-positive-literals gate: a gate is **active** under `ρ` iff *no* input is fixed to the
absorbing value `false` *and* it still has a free input.  A gate with a fixed-`false` input is constant (`false`)
regardless of its free inputs, so it neither varies nor separates free coordinates.  The **refined pattern** of a
coordinate is its membership vector over the *active* gates only:

```
refinedCellPatternVec ρ supports v  =  (j ↦ [ GateActive ρ supports j  ∧  v ∈ supports j ]).
```

The decisive new phenomenon (`refined_merge_of_inactive_separators`): if every gate that *separates* `v` and `w` has
been made *inactive* by `ρ`, then `v` and `w` share a refined cell — a merge the membership model provably could not
perform.  `refined_strictly_beats_membership` exhibits a concrete `supports, ρ, L` where the membership cell count
does **not** collapse (`¬ CellCountCollapse`) yet the refined one does (`RefinedCellCollapse`).

## What is proved (clean axioms, no `sorry`)

* `Restriction` / `freeSet` / `GateActive` / `refinedCellPatternVec` / `refinedCellPatternCount` / `RefinedCellCollapse`.
* **`exists_sameRefinedCell_of_collapse`** — refined collapse ⇒ two coordinates share a refined cell (pigeonhole).
* **`refined_merge_of_inactive_separators`** — the new merging power: inactive separators ⇒ equal refined patterns.
* **`refined_strictly_beats_membership`** — a concrete witness: `¬ CellCountCollapse` (membership cannot collapse) yet
  `RefinedCellCollapse` (the refined model does) — the strict gain over the membership ceiling.

## Honest scope

This is the structural core of the richer model and a *proof* that it strictly extends the membership invariant's
reach.  Two pieces remain, both explicitly open: (i) the **correlation bridge** — wiring `RefinedCellCollapse` into the
holonomy low-correlation bound (it follows by swap-invariance: same-refined-cell coordinates leave every active gate's
membership unchanged and every inactive gate constant, so the predictor cannot distinguish them — but this must be
formalized against the gate semantics in `ManyGateCorrelation`); and (ii) the **`MOD` obstruction** — `MOD`/symmetric
gates have *no* absorbing value (a `MOD` gate is constant only when its support is *entirely* fixed), so this merging
mechanism is far weaker for them, which is exactly why `ACC⁰` stays hard.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RefinedObserverModel

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountRoute

variable {k n : ℕ}

/-- A **restriction**: a partial assignment, `none` = free, `some b` = fixed to `b`. -/
abbrev Restriction (n : ℕ) := Fin n → Option Bool

/-- The free coordinates of a restriction. -/
def freeSet (ρ : Restriction n) : Finset (Fin n) := Finset.univ.filter (fun v => ρ v = none)

/-- A gate (`AND` of positive literals on its support) is **active** under `ρ` iff no input is fixed to the absorbing
value `false`, and it still reads a free input.  A gate with a fixed-`false` input is the constant `false`. -/
abbrev GateActive (ρ : Restriction n) (supports : Fin k → Finset (Fin n)) (j : Fin k) : Prop :=
  (∀ i ∈ supports j, ρ i ≠ some false) ∧ (∃ i ∈ supports j, ρ i = none)

/-- The **refined pattern** of a coordinate: its membership over the *active* gates only. -/
def refinedCellPatternVec (ρ : Restriction n) (supports : Fin k → Finset (Fin n)) (v : Fin n) :
    Fin k → ZMod 2 :=
  fun j => if GateActive ρ supports j ∧ v ∈ supports j then 1 else 0

/-- The number of distinct refined cells realized over a live set. -/
def refinedCellPatternCount (ρ : Restriction n) (supports : Fin k → Finset (Fin n))
    (L : Finset (Fin n)) : ℕ :=
  (L.image (refinedCellPatternVec ρ supports)).card

/-- **Refined cell collapse**: fewer refined cells than live coordinates. -/
def RefinedCellCollapse (ρ : Restriction n) (supports : Fin k → Finset (Fin n))
    (L : Finset (Fin n)) : Prop :=
  refinedCellPatternCount ρ supports L < L.card

/-- **The refined pigeonhole (proved): collapse ⇒ two coordinates share a refined cell.** -/
theorem exists_sameRefinedCell_of_collapse (ρ : Restriction n) (supports : Fin k → Finset (Fin n))
    (L : Finset (Fin n)) (h : RefinedCellCollapse ρ supports L) :
    ∃ v ∈ L, ∃ w ∈ L, v ≠ w ∧
      refinedCellPatternVec ρ supports v = refinedCellPatternVec ρ supports w := by
  obtain ⟨v, hv, w, hw, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to h (fun v hv => Finset.mem_image_of_mem _ hv)
  exact ⟨v, hv, w, hw, hne, heq⟩

/-- **The new merging power (proved): inactive separators merge.**  If every gate either treats `v, w` identically
(membership agrees) or is inactive under `ρ`, then `v` and `w` have the same refined pattern — even if they differ on
those inactive gates.  This is exactly what the membership model could *not* do. -/
theorem refined_merge_of_inactive_separators (ρ : Restriction n) (supports : Fin k → Finset (Fin n))
    (v w : Fin n)
    (h : ∀ j, (v ∈ supports j ↔ w ∈ supports j) ∨ ¬ GateActive ρ supports j) :
    refinedCellPatternVec ρ supports v = refinedCellPatternVec ρ supports w := by
  funext j
  simp only [refinedCellPatternVec]
  rcases h j with hmem | hinact
  · exact if_congr (and_congr_right (fun _ => hmem)) rfl rfl
  · rw [if_neg (fun hc => hinact hc.1), if_neg (fun hc => hinact hc.1)]

/-- **The refined model strictly beats the membership ceiling (proved).**  A concrete support system and restriction
where the membership cell count does **not** collapse (every coordinate keeps a distinct membership pattern) but the
refined one **does** — the restriction kills the separating gate via a fixed-`false` input it also reads. -/
theorem refined_strictly_beats_membership :
    ∃ (n k : ℕ) (supports : Fin k → Finset (Fin n)) (ρ : Restriction n) (L : Finset (Fin n)),
      ¬ CellCountCollapse supports L ∧ RefinedCellCollapse ρ supports L := by
  refine ⟨3, 1, (fun _ : Fin 1 => ({0, 2} : Finset (Fin 3))),
    (fun i => if i = 2 then some false else none), ({0, 1} : Finset (Fin 3)), ?_, ?_⟩
  · -- Membership cannot collapse: cellPatternVec 0 ≠ cellPatternVec 1, so ≥ 2 = |L| cells.
    have hne : cellPatternVec (fun _ : Fin 1 => ({0, 2} : Finset (Fin 3))) (0 : Fin 3)
             ≠ cellPatternVec (fun _ : Fin 1 => ({0, 2} : Finset (Fin 3))) (1 : Fin 3) := by decide
    have h2 : 2 ≤ cellPatternCount (fun _ : Fin 1 => ({0, 2} : Finset (Fin 3))) ({0, 1} : Finset (Fin 3)) := by
      have hsub : ({cellPatternVec (fun _ : Fin 1 => ({0, 2} : Finset (Fin 3))) 0,
                    cellPatternVec (fun _ : Fin 1 => ({0, 2} : Finset (Fin 3))) 1} : Finset (Fin 1 → ZMod 2))
          ⊆ ({0, 1} : Finset (Fin 3)).image (cellPatternVec (fun _ : Fin 1 => ({0, 2} : Finset (Fin 3)))) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_image_of_mem _ (by decide)
        · exact Finset.mem_image_of_mem _ (by decide)
      calc 2 = ({cellPatternVec (fun _ : Fin 1 => ({0, 2} : Finset (Fin 3))) 0,
                 cellPatternVec (fun _ : Fin 1 => ({0, 2} : Finset (Fin 3))) 1} : Finset (Fin 1 → ZMod 2)).card :=
              (Finset.card_pair hne).symm
        _ ≤ _ := Finset.card_le_card hsub
    simp only [CellCountCollapse, not_lt]
    rw [show ({0, 1} : Finset (Fin 3)).card = 2 from by decide]
    exact h2
  · -- Refined collapse: the only separating gate is inactive (it reads the fixed-`false` coordinate 2).
    have hmerge : refinedCellPatternVec (fun i => if i = 2 then some false else none)
                    (fun _ : Fin 1 => ({0, 2} : Finset (Fin 3))) 0
                = refinedCellPatternVec (fun i => if i = 2 then some false else none)
                    (fun _ : Fin 1 => ({0, 2} : Finset (Fin 3))) 1 :=
      refined_merge_of_inactive_separators (fun i => if i = 2 then some false else none)
        (fun _ : Fin 1 => ({0, 2} : Finset (Fin 3))) 0 1 (fun j => Or.inr (by fin_cases j; decide))
    simp only [RefinedCellCollapse, refinedCellPatternCount]
    rw [show ({0, 1} : Finset (Fin 3)) = insert 0 {1} from rfl,
        Finset.image_insert, Finset.image_singleton, hmerge,
        Finset.insert_eq_self.mpr (Finset.mem_singleton_self _),
        Finset.card_singleton, show ({0, 1} : Finset (Fin 3)).card = 2 from by decide]
    norm_num

end PallLean.Paper93.DeepMath.PathB.ACC0RefinedObserverModel

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RefinedObserverModel.exists_sameRefinedCell_of_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RefinedObserverModel.refined_merge_of_inactive_separators
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RefinedObserverModel.refined_strictly_beats_membership
