import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CellCollapseRoute

/-!
# `collapse_lifts_through_layer` — cell collapse composes, under a controlled survivor budget

The N-Frame subcases so far discharged `FullACC0ForcesCellCollapse` for *flat* support systems.  This file handles
the **composition** direction: what happens to cell collapse when a layer is *stacked* on top.  In the
support/holonomy-predictor model, stacking a layer appends the new layer's gate-supports to the existing ones
(`Fin.append`).  The key structural fact is that **survivor counts add across the layer**:

```
survivingCount (append supp₁ supp₂) L  =  survivingCount supp₁ L  +  survivingCount supp₂ L
```

So the collapse condition `2^{#survivors} < |L|` becomes `2^{s₁ + s₂} < |L|` — it composes, but *multiplicatively in
the cell count*.  Collapse therefore **lifts through the layer exactly when the new layer adds few survivors**: with a
budget `δ` on the layer's survivors and slack `s₁ + δ < log₂|L|` in the base, the composite collapses.

## What is proved (clean axioms, no `sorry`)

* **`survivingCount_append`** — survivor counts are additive across an appended layer
  (`finSumFinEquiv` + `Fintype.sum_sum_type` + `Fin.append_left/right`).
* **`collapse_lifts_through_layer`** — `2^{s₁ + s₂} < |L| ⇒ CellCollapse (append supp₁ supp₂) L`.
* **`collapse_lifts_of_budget`** — the controlled-parameter form: layer survivors `≤ δ` and base slack
  `2^{s₁ + δ} < |L|` ⇒ collapse lifts.
* **`full_collapse_lifts`** — packaged as `FullACC0ForcesCellCollapse (append supp₁ supp₂)`.

## Honest scope — the budget is the wall

The lift is *conditional on the layer adding few survivors* (`survivingCount supp₂ L ≤ δ`, with `s₁ + δ < log₂|L|`).
That is exactly the "controlled parameters" regime.  When the new layer is a wide `MOD` layer that survives on most of
`L`, `δ` is large and the budget fails — the cell count `2^{s₁+s₂}` blows past `|L|`.  Supplying the *small* survivor
budget for a real `ACC⁰` layer under a restriction is precisely the switching/restriction lemma (blocked for naive
leaf-switching by the proved `MOD` no-go).  So this proves collapse *composes additively in survivors* and lifts
under budget — it does **not** supply the budget for full `ACC⁰`.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CollapseLift

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute

variable {n k₁ k₂ : ℕ}

/-- **Survivor counts are additive across an appended layer (proved).**  The supports of `append supp₁ supp₂` that
meet `L` are exactly those of `supp₁` plus those of `supp₂`. -/
theorem survivingCount_append (supp₁ : Fin k₁ → Finset (Fin n)) (supp₂ : Fin k₂ → Finset (Fin n))
    (L : Finset (Fin n)) :
    survivingCount (Fin.append supp₁ supp₂) L
      = survivingCount supp₁ L + survivingCount supp₂ L := by
  unfold survivingCount
  simp only [Finset.card_filter]
  rw [← Equiv.sum_comp finSumFinEquiv
        (fun j => if ¬ Disjoint (Fin.append supp₁ supp₂ j) L then (1 : ℕ) else 0),
      Fintype.sum_sum_type]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by rw [finSumFinEquiv_apply_left, Fin.append_left])
  · exact Finset.sum_congr rfl (fun i _ => by rw [finSumFinEquiv_apply_right, Fin.append_right])

/-- **Cell collapse lifts through a layer (proved): `2^{s₁ + s₂} < |L| ⇒ CellCollapse (append supp₁ supp₂) L`.** -/
theorem collapse_lifts_through_layer (supp₁ : Fin k₁ → Finset (Fin n))
    (supp₂ : Fin k₂ → Finset (Fin n)) (L : Finset (Fin n))
    (hbudget : 2 ^ (survivingCount supp₁ L + survivingCount supp₂ L) < L.card) :
    CellCollapse (Fin.append supp₁ supp₂) L := by
  show 2 ^ survivingCount (Fin.append supp₁ supp₂) L < L.card
  rw [survivingCount_append]
  exact hbudget

/-- **The controlled-parameter lift (proved): a layer adding `≤ δ` survivors lifts collapse if the base has slack.**
If `survivingCount supp₂ L ≤ δ` and `2^{s₁ + δ} < |L|`, the composite collapses. -/
theorem collapse_lifts_of_budget (supp₁ : Fin k₁ → Finset (Fin n))
    (supp₂ : Fin k₂ → Finset (Fin n)) (L : Finset (Fin n)) (δ : ℕ)
    (hlayer : survivingCount supp₂ L ≤ δ)
    (hbase : 2 ^ (survivingCount supp₁ L + δ) < L.card) :
    CellCollapse (Fin.append supp₁ supp₂) L :=
  collapse_lifts_through_layer supp₁ supp₂ L
    (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (Nat.add_le_add_left hlayer _)) hbase)

/-- **The lift packaged as the cell-collapse socket (proved).**  Under the survivor budget, the composite support
system `append supp₁ supp₂` forces cell collapse — the witness live set is `L`. -/
theorem full_collapse_lifts (supp₁ : Fin k₁ → Finset (Fin n)) (supp₂ : Fin k₂ → Finset (Fin n))
    (L : Finset (Fin n)) (δ : ℕ) (hlayer : survivingCount supp₂ L ≤ δ)
    (hbase : 2 ^ (survivingCount supp₁ L + δ) < L.card) :
    FullACC0ForcesCellCollapse (Fin.append supp₁ supp₂) :=
  ⟨L, collapse_lifts_of_budget supp₁ supp₂ L δ hlayer hbase⟩

end PallLean.Paper93.DeepMath.PathB.ACC0CollapseLift

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CollapseLift.survivingCount_append
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CollapseLift.collapse_lifts_through_layer
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CollapseLift.full_collapse_lifts
