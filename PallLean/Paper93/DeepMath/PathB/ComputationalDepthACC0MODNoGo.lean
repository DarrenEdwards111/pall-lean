import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RefinedObserverModel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CellCountCharacterization

/-!
# The MOD no-go — the variable-fixing model gives *no* merging power for symmetric gates

The richer (variable-fixing) observer model merges patterns by *deactivating* a separating gate: an `AND` gate dies
when one of its inputs is fixed to the absorbing value `false`, dropping out of the pattern even while it still reads a
free coordinate (`…ACC0RefinedObserverModel`).  This file proves that mechanism is **inert for `MOD`/symmetric gates**.

A `MOD_q` gate `[∑_{i∈S} x_i ≡ c]` has **no absorbing value**: fixing one input changes the threshold but leaves the
gate varying as long as *any* input is free.  So a `MOD` gate is constant under `ρ` iff its support is *entirely*
fixed — i.e. it is active exactly when it reads a free coordinate:

```
MODGateActive ρ supports j  :=  ∃ i ∈ supports j, ρ i = none.
```

Consequently a gate that *separates* two **free** coordinates contains one of them — a free coordinate — so it is
**always active** and can never be deactivated.  The refined pattern of a free coordinate over the active `MOD` gates
is therefore *identical* to its membership pattern, and the whole richer model collapses back to the membership model
(which has the proved hard-regime ceiling, `…ACC0CellCountCharacterization`).  The variable-fixing model buys nothing
for `MOD` — exactly the textbook reason `AC⁰` switches under restriction but `ACC⁰` does not.

## What is proved (clean axioms, no `sorry`)

* `MODGateActive` / `modRefinedCellPatternVec` — the `MOD`-correct activity and refined pattern.
* **`mod_separating_gate_active`** — a gate separating two free coordinates is `MOD`-active (cannot be deactivated).
* **`modRefined_eq_membership_of_free`** — for a free coordinate the `MOD`-refined pattern *equals* the membership pattern.
* **`mod_refined_merge_iff_sameCell`** — two free coordinates share a `MOD`-refined cell **iff** they share a membership
  cell: the variable-fixing model gives *no* extra merging for `MOD`.
* **`mod_no_collapse_in_hardRegime`** — in the hard regime, the membership socket is false, and `MOD`-refinement does not
  rescue it: no free pair merges.

## Honest scope

This is a *negative* result localizing the `ACC⁰` barrier precisely: the merging that powers the refined route is an
`AND`/`OR` (absorbing-value) phenomenon with no `MOD` analogue.  It does not prove `ACC⁰` lower bounds — it proves that
*this* observer mechanism cannot, and pins the obstruction to `MOD`'s lack of an absorbing value.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0MODNoGo

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountRoute
open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0RefinedObserverModel

variable {k n : ℕ}

/-- **`MOD`-correct gate activity**: a symmetric (`MOD`) gate is non-constant under `ρ` exactly when it reads a free
coordinate (it has no absorbing value, so a single fixed input cannot pin it). -/
abbrev MODGateActive (ρ : Restriction n) (supports : Fin k → Finset (Fin n)) (j : Fin k) : Prop :=
  ∃ i ∈ supports j, ρ i = none

/-- The `MOD`-refined pattern: membership over the active (free-reading) `MOD` gates. -/
def modRefinedCellPatternVec (ρ : Restriction n) (supports : Fin k → Finset (Fin n)) (v : Fin n) :
    Fin k → ZMod 2 :=
  fun j => if MODGateActive ρ supports j ∧ v ∈ supports j then 1 else 0

/-- **A gate separating two free coordinates is `MOD`-active (proved).**  It contains one of the (free) coordinates, so
it reads a free input — hence it can never be deactivated.  This is the crux: the deactivation trick is unavailable. -/
theorem mod_separating_gate_active (ρ : Restriction n) (supports : Fin k → Finset (Fin n))
    (v w : Fin n) (j : Fin k) (hv : ρ v = none) (hw : ρ w = none)
    (hsep : ¬ (v ∈ supports j ↔ w ∈ supports j)) : MODGateActive ρ supports j := by
  by_cases hvj : v ∈ supports j
  · exact ⟨v, hvj, hv⟩
  · refine ⟨w, ?_, hw⟩
    by_contra hwj
    exact hsep (iff_of_false hvj hwj)

/-- **For a free coordinate the `MOD`-refined pattern equals the membership pattern (proved).**  Every gate a free
coordinate belongs to reads a free input, hence is active — so no gate drops out. -/
theorem modRefined_eq_membership_of_free (ρ : Restriction n) (supports : Fin k → Finset (Fin n))
    (v : Fin n) (hv : ρ v = none) :
    modRefinedCellPatternVec ρ supports v = cellPatternVec supports v := by
  funext j
  simp only [modRefinedCellPatternVec, cellPatternVec]
  by_cases hvj : v ∈ supports j
  · rw [if_pos ⟨⟨v, hvj, hv⟩, hvj⟩, if_pos hvj]
  · rw [if_neg (fun hc => hvj hc.2), if_neg hvj]

/-- **No merging gain for `MOD` (proved): two free coordinates share a `MOD`-refined cell iff they share a membership
cell.**  The variable-fixing model collapses to the membership model on the free coordinates. -/
theorem mod_refined_merge_iff_sameCell (ρ : Restriction n) (supports : Fin k → Finset (Fin n))
    (v w : Fin n) (hv : ρ v = none) (hw : ρ w = none) :
    modRefinedCellPatternVec ρ supports v = modRefinedCellPatternVec ρ supports w
      ↔ SameCell supports v w := by
  rw [modRefined_eq_membership_of_free ρ supports v hv,
      modRefined_eq_membership_of_free ρ supports w hw, sameCell_iff_pattern]

/-- **The `MOD` no-go in the hard regime (proved).**  In the hard regime the membership socket is false (every
coordinate has a distinct pattern), and `MOD`-refinement does not help: distinct free coordinates never share a
`MOD`-refined cell, so no collapse is created. -/
theorem mod_no_collapse_in_hardRegime (ρ : Restriction n) (supports : Fin k → Finset (Fin n))
    (hsep : ∀ v w, SameCell supports v w → v = w) (v w : Fin n)
    (hv : ρ v = none) (hw : ρ w = none) (hne : v ≠ w) :
    modRefinedCellPatternVec ρ supports v ≠ modRefinedCellPatternVec ρ supports w := by
  intro hmerge
  exact hne (hsep v w ((mod_refined_merge_iff_sameCell ρ supports v w hv hw).mp hmerge))

end PallLean.Paper93.DeepMath.PathB.ACC0MODNoGo

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MODNoGo.mod_separating_gate_active
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MODNoGo.modRefined_eq_membership_of_free
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MODNoGo.mod_refined_merge_iff_sameCell
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MODNoGo.mod_no_collapse_in_hardRegime
