import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SatMachine

/-!
# Survivor → cell-count: the speedup is governed by the active gates

The cell bound `|image(weightVec)| ≤ (n+1)^k` used *all* `k` gates.  But an **empty** support contributes a constant
`0` to `weightVec` — it does not distinguish inputs — so only the **active** (non-empty) supports matter.  This file
proves `|image(weightVec)| ≤ (n+1)^{#active}`, tying the speedup's cell count to the active‑gate count, which after a
restriction is exactly the **surviving**‑support count (killed gates become empty on the live set).

So the speedup cost `(n+1)^{#active}` is small precisely when few gates survive — the same survivor parameter the
correlation/restriction machinery (`…ACCSwitchingPipeline`, `…ACCCoreDecomposition`) controls.  This connects the
SAT‑speedup directly back to the core machinery: *few survivors ⇒ few cells ⇒ fast search*.

## What is proved (clean axioms, no `sorry`)

* `weightVec_eq_zero_of_empty` — an empty support gives a constant‑`0` coordinate.
* `image_card_le_active` — **`|image(weightVec)| ≤ (n+1)^{#active}`** (the cell count is governed by active gates).
* `cells_le_active` — the `cellSearch` step count is `≤ (n+1)^{#active}`.

## Honest scope

This refines the cell bound from all `k` gates to the active (= surviving, after restriction) gates — the genuine
link between the speedup parameter and the survivor machinery.  It is still the cell‑search cost model; it does not
build the full Turing‑machine `2^{n-n^ε}` analysis (the named Williams gap), and proves nothing about
`NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SatSurvivorCells

open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.ACC0SatTimeCost
open PallLean.Paper93.DeepMath.PathB.ACC0SatMachine

variable {n k : ℕ}

/-- The active supports: those that actually read a coordinate. -/
def activeSupports (supports : Fin k → Finset (Fin n)) : Finset (Fin k) :=
  Finset.univ.filter (fun j => supports j ≠ ∅)

/-- **An empty support gives a constant‑`0` cell coordinate (proved).** -/
theorem weightVec_eq_zero_of_empty (supports : Fin k → Finset (Fin n)) (x : Fin n → Bool) (j : Fin k)
    (h : supports j = ∅) : weightVec supports x j = 0 := by
  show weightOn (supports j) x = 0
  rw [h]
  simp [weightOn]

/-- **The cell count is governed by the active gates (proved): `|image(weightVec)| ≤ (n+1)^{#active}`.**  Inactive
(empty) supports give constant‑`0` coordinates, so the cell vector is determined by its active coordinates. -/
theorem image_card_le_active (supports : Fin k → Finset (Fin n)) :
    (Finset.univ.image (weightVec supports)).card ≤ (n + 1) ^ (activeSupports supports).card := by
  classical
  have hle : (Finset.univ.image (weightVec supports)).card
      ≤ (Fintype.piFinset (fun _ : {j : Fin k // supports j ≠ ∅} => Finset.range (n + 1))).card := by
    apply Finset.card_le_card_of_injOn (fun w (j : {j : Fin k // supports j ≠ ∅}) => w j.val)
    · intro w hw
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw)
      simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]
      intro j
      exact Nat.lt_succ_of_le (weightVec_le supports x j.val)
    · intro w1 hw1 w2 hw2 hf
      obtain ⟨x1, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw1)
      obtain ⟨x2, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw2)
      funext j
      by_cases hj : supports j = ∅
      · rw [weightVec_eq_zero_of_empty supports x1 j hj, weightVec_eq_zero_of_empty supports x2 j hj]
      · exact congrFun hf ⟨j, hj⟩
  have hcard : (Fintype.piFinset (fun _ : {j : Fin k // supports j ≠ ∅} => Finset.range (n + 1))).card
      = (n + 1) ^ (activeSupports supports).card := by
    rw [Fintype.card_piFinset]
    simp only [Finset.card_range, Finset.prod_const, Finset.card_univ, Fintype.card_subtype]
    rfl
  rw [hcard] at hle
  exact hle

/-- **The `cellSearch` step count is governed by the active gates (proved): `steps ≤ (n+1)^{#active}`.**  After a
restriction, `#active = #surviving`, so the speedup is fast exactly when few gates survive. -/
theorem cells_le_active (C : Depth2ModCircuit n k) :
    (cellSearch C).steps ≤ (n + 1) ^ (activeSupports C.supports).card :=
  image_card_le_active C.supports

end PallLean.Paper93.DeepMath.PathB.ACC0SatSurvivorCells

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatSurvivorCells.weightVec_eq_zero_of_empty
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatSurvivorCells.image_card_le_active
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatSurvivorCells.cells_le_active
