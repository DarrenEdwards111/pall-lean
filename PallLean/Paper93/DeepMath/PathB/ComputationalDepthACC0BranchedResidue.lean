import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SatBranched
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModResidueSpeedup

/-!
# Branched residue cost: past the `∏ q_j < 2^n` base regime

`…ACC0ResidueMachine` runs the residue search in `≤ ∏ q_j` steps — a win only when `∏ q_j < 2^n` (few gates).  For
many gates `∏ q_j` exceeds `2^n`; branching rescues it, exactly as `…ACC0SatBranched` rescued the cell search.

Branch over a **killed** coordinate set `K`: SAT decomposes as an OR over the `2^{#killed}` assignments to `K`
(`…ACC0SatBranchCorrect.sat_branch_decompose`, proved).  On each branch only the **surviving** gates matter (a gate
whose support is fixed by `K` is constant on the branch, by `MOD`-gate locality), and the per-branch residue search
over the `r` surviving gates costs `≤ ∏_{j surviving} q_j`.  So

> total cost `= 2^{#killed} · ∏_{j surviving} q_j`,

which is `< 2^n` whenever `#killed + #live = n` and `∏_{j surviving} q_j < 2^{#live}`.  This is the residue analogue
of `branched_cost_le` / `branched_beats_bruteforce`, with the per-branch cost reduced from `(n+1)^r` (full counts)
to `∏ q_j` (residues, e.g. `6^r` for `MOD_6`) — a large gain, since `∏ q_j` is constant per gate.

## What is proved (clean axioms, no `sorry`)

* `branched_residue_cost_le` — `2^{#killed} · (per-branch residue cells) ≤ 2^{#killed} · ∏ q_j`.
* `branched_residue_regime` — `#killed + #live = n` and `∏ q_j < 2^{#live}` ⇒ `2^{#killed} · ∏ q_j < 2^n`.
* `branched_residue_beats_bruteforce` — combining: the branched residue search beats brute force.
* `branched_residue_mod6_beats_bruteforce` — the `MOD_6` instance (`∏ q_j = 6^r`).

## Honest scope

The *cost arithmetic* of branch-and-restrict for the residue model, with the per-branch cost the survivor residue
count `∏_{surviving} q_j` (the gain over the unbranched `∏_{all} q_j` and over the cell-search `(n+1)^r`).  The
structural justification that per-branch only survivors matter is `MOD`-gate locality; the branch-enumeration
correctness (SAT = OR over `2^{#killed}` branches) is the proved `sat_branch_decompose`.  The link
"restriction ⇒ these `r` gates are the survivors" is the next step (`residue_cells_le_surviving_moduli`).  Still the
unit-cost cell model; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BranchedResidue

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.ACC0SatBranched
open PallLean.Paper93.DeepMath.PathB.ACC0ModResidueSpeedup

variable {n : ℕ}

/-- **The branched residue cost is `≤ 2^{#killed} · ∏_{surviving} q_j` (proved).**  Per branch, only the `r`
surviving gates matter, so the residue search costs `≤ ∏_j q_j` (by `residue_cell_count_le` on the survivor
family). -/
theorem branched_residue_cost_le {r : ℕ} (killed : ℕ) (survGates : Fin r → ModGate n)
    (hpos : ∀ j, 0 < (survGates j).modulus) :
    branchedCost killed (Finset.univ.image (modResVec ⟨survGates, fun _ => false⟩)).card
      ≤ 2 ^ killed * ∏ j, (survGates j).modulus := by
  unfold branchedCost
  gcongr
  exact residue_cell_count_le ⟨survGates, fun _ => false⟩ hpos

/-- **The few-survivor residue regime arithmetic (proved): `#killed + #live = n` and `∏ q_j < 2^{#live}` ⇒
`2^{#killed} · ∏ q_j < 2^n`.** -/
theorem branched_residue_regime {r : ℕ} (killed live : ℕ) (survGates : Fin r → ModGate n)
    (hsum : killed + live = n) (hcell : (∏ j, (survGates j).modulus) < 2 ^ live) :
    2 ^ killed * (∏ j, (survGates j).modulus) < 2 ^ n := by
  calc 2 ^ killed * (∏ j, (survGates j).modulus)
      < 2 ^ killed * 2 ^ live := by
        apply mul_lt_mul_of_pos_left hcell
        positivity
    _ = 2 ^ n := by rw [← pow_add, hsum]

/-- **The branched residue search beats brute force (proved): in the few-survivor regime, the branched cost is
`< 2^n`.**  Combining the per-branch residue bound with the regime arithmetic — `#killed + #live = n` and
`∏ q_j < 2^{#live}`. -/
theorem branched_residue_beats_bruteforce {r : ℕ} (killed live : ℕ) (survGates : Fin r → ModGate n)
    (hpos : ∀ j, 0 < (survGates j).modulus) (hsum : killed + live = n)
    (hcell : (∏ j, (survGates j).modulus) < 2 ^ live) :
    branchedCost killed (Finset.univ.image (modResVec ⟨survGates, fun _ => false⟩)).card < 2 ^ n :=
  lt_of_le_of_lt (branched_residue_cost_le killed survGates hpos)
    (branched_residue_regime killed live survGates hsum hcell)

/-- **The `MOD_6` instance (proved): `#killed + #live = n` and `6^r < 2^{#live}` ⇒ branched cost `< 2^n`.**  With
`r` surviving `MOD_6` gates the per-branch residue cost is `6^r`, so the branched search beats brute force whenever
`#killed + r·log₂6 < n` — far past the unbranched `6^k < 2^n` regime. -/
theorem branched_residue_mod6_beats_bruteforce {r : ℕ} (killed live : ℕ) (survGates : Fin r → ModGate n)
    (h6 : ∀ j, (survGates j).modulus = 6) (hsum : killed + live = n) (hcell : 6 ^ r < 2 ^ live) :
    branchedCost killed (Finset.univ.image (modResVec ⟨survGates, fun _ => false⟩)).card < 2 ^ n := by
  have hprod : (∏ j, (survGates j).modulus) = 6 ^ r := by
    rw [Finset.prod_congr rfl (fun j _ => h6 j), Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine branched_residue_beats_bruteforce killed live survGates
    (fun j => by rw [h6 j]; norm_num) hsum ?_
  rw [hprod]; exact hcell

end PallLean.Paper93.DeepMath.PathB.ACC0BranchedResidue

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BranchedResidue.branched_residue_cost_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BranchedResidue.branched_residue_regime
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BranchedResidue.branched_residue_beats_bruteforce
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BranchedResidue.branched_residue_mod6_beats_bruteforce
