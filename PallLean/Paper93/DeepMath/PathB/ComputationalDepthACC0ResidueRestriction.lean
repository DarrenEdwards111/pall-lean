import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModResidueSpeedup

/-!
# Restriction ⇒ few surviving residue gates (the mixed-modulus survivor → cell-count)

Step 2 (`…ACC0BranchedResidue`) took the surviving gate family as given.  This file discharges it: it connects the
restriction machinery to the residue model, exactly as `…ACC0SatSurvivorCells` / `…ACC0SatRestrictionActive` did for
the cell-search model.

A `MOD` gate with **empty** support contributes a constant `0` residue (it reads nothing), so only the **active**
(non-empty support) gates matter; the residue-cell count is governed by them: `|image(modResVec)| ≤ ∏_{active} q_j`.
After restricting supports to a live set `L` (`restrictCircuit`), a gate is active iff its support **meets** `L`
(`¬ Disjoint`), i.e. it **survives**; gates disjoint from `L` are killed (empty restricted support, constant
residue).  So `|residue cells after restriction| ≤ ∏_{j surviving} q_j` — the mixed-modulus analogue of
`cells_restrict_le_surviving`, and the per-branch bound step 2 assumed.

## What is proved (clean axioms, no `sorry`)

* `modResVec_eq_zero_of_empty` — an empty support gives a constant-`0` residue coordinate.
* `residue_image_card_le_active` — **`|image(modResVec C)| ≤ ∏_{j active} q_j`** (governed by active gates).
* `residue_active_after_restriction` — active after restricting to `L` = surviving (`¬ Disjoint (S_j) L`).
* `residue_cells_le_surviving_moduli` — **`|residue cells (C↾L)| ≤ ∏_{j surviving} q_j`**.

## Honest scope

The genuine link between the restriction/survivor machinery and the residue speedup cost: few survivors ⇒ few
residue cells.  Combined with step 2's branched cost it gives `2^{#killed} · ∏_{surviving} q_j`.  Still the
unit-cost cell model; the branch-enumeration correctness is the proved `sat_branch_decompose`, and the
restriction-existence (a good live set `L` with few survivors) is the switching/core machinery
(`…ACCSwitchingPipeline`).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ResidueRestriction

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.ACC0ModResidueSpeedup

variable {n k : ℕ}

/-- The active gates: those whose support actually reads a coordinate. -/
def activeGates (gates : Fin k → ModGate n) : Finset (Fin k) :=
  Finset.univ.filter (fun j => (gates j).support ≠ ∅)

/-- **An empty support gives a constant-`0` residue coordinate (proved).** -/
theorem modResVec_eq_zero_of_empty (C : Depth2ModCircuit n k) (x : Fin n → Bool) (j : Fin k)
    (h : (C.gates j).support = ∅) : modResVec C x j = 0 := by
  show modQStatOn (C.gates j).support (C.gates j).modulus x = 0
  rw [h]
  simp [modQStatOn, weightOn]

/-- **The residue-cell count is governed by the active gates (proved): `|image(modResVec C)| ≤ ∏_{active} q_j`.**
Inactive (empty-support) gates give constant-`0` residue coordinates, so the residue vector is determined by its
active coordinates. -/
theorem residue_image_card_le_active (C : Depth2ModCircuit n k)
    (hpos : ∀ j, 0 < (C.gates j).modulus) :
    (Finset.univ.image (modResVec C)).card ≤ ∏ j ∈ activeGates C.gates, (C.gates j).modulus := by
  classical
  haveI : ∀ j, NeZero (C.gates j).modulus := fun j => ⟨(hpos j).ne'⟩
  have hle : (Finset.univ.image (modResVec C)).card
      ≤ (Fintype.piFinset (fun j : {j : Fin k // (C.gates j).support ≠ ∅} =>
            (Finset.univ : Finset (ZMod (C.gates j.val).modulus)))).card := by
    apply Finset.card_le_card_of_injOn
      (fun (w : (j : Fin k) → ZMod (C.gates j).modulus)
          (j : {j : Fin k // (C.gates j).support ≠ ∅}) => w j.val)
    · intro w _
      exact Fintype.mem_piFinset.mpr (fun _ => Finset.mem_univ _)
    · intro w1 hw1 w2 hw2 hf
      obtain ⟨x1, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw1)
      obtain ⟨x2, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw2)
      funext j
      by_cases hj : (C.gates j).support = ∅
      · rw [modResVec_eq_zero_of_empty C x1 j hj, modResVec_eq_zero_of_empty C x2 j hj]
      · exact congrFun hf ⟨j, hj⟩
  have hcard : (Fintype.piFinset (fun j : {j : Fin k // (C.gates j).support ≠ ∅} =>
          (Finset.univ : Finset (ZMod (C.gates j.val).modulus)))).card
      = ∏ j ∈ activeGates C.gates, (C.gates j).modulus := by
    rw [Fintype.card_piFinset]
    have hc : ∀ j : {j : Fin k // (C.gates j).support ≠ ∅},
        (Finset.univ : Finset (ZMod (C.gates j.val).modulus)).card = (C.gates j.val).modulus :=
      fun j => by rw [Finset.card_univ, ZMod.card]
    rw [Finset.prod_congr rfl (fun j _ => hc j)]
    exact (Finset.prod_subtype (activeGates C.gates)
      (fun j => by simp [activeGates]) (fun j => (C.gates j).modulus)).symm
  rw [hcard] at hle
  exact hle

/-- The circuit with each gate's support restricted to a live set `L` (same moduli and targets). -/
def restrictCircuit (C : Depth2ModCircuit n k) (L : Finset (Fin n)) : Depth2ModCircuit n k where
  gates := fun j =>
    { modulus := (C.gates j).modulus, support := (C.gates j).support ∩ L, target := (C.gates j).target }
  top := C.top

/-- **Active after restriction = surviving (proved): a gate is active in `C↾L` iff its support meets `L`.** -/
theorem residue_active_after_restriction (C : Depth2ModCircuit n k) (L : Finset (Fin n)) :
    activeGates (restrictCircuit C L).gates
      = Finset.univ.filter (fun j => ¬ Disjoint (C.gates j).support L) := by
  unfold activeGates restrictCircuit
  apply Finset.filter_congr
  intro j _
  rw [ne_eq, Finset.disjoint_iff_inter_eq_empty]

/-- **Restriction ⇒ few residue cells (proved): `|residue cells of C↾L| ≤ ∏_{j surviving} q_j`.**  The residue-cell
count after restricting to `L` is governed by the surviving gates (supports meeting `L`) — the per-branch bound the
branched residue cost (step 2) assumed. -/
theorem residue_cells_le_surviving_moduli (C : Depth2ModCircuit n k) (L : Finset (Fin n))
    (hpos : ∀ j, 0 < (C.gates j).modulus) :
    (Finset.univ.image (modResVec (restrictCircuit C L))).card
      ≤ ∏ j ∈ Finset.univ.filter (fun j => ¬ Disjoint (C.gates j).support L), (C.gates j).modulus := by
  have h := residue_image_card_le_active (restrictCircuit C L) hpos
  rw [residue_active_after_restriction] at h
  exact h

end PallLean.Paper93.DeepMath.PathB.ACC0ResidueRestriction

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ResidueRestriction.residue_image_card_le_active
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ResidueRestriction.residue_active_after_restriction
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ResidueRestriction.residue_cells_le_surviving_moduli
