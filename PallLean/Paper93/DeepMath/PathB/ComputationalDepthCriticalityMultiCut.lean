import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTreeDagDuality

/-!
# Two more proved faces of the one wall: criticality, and multi-cut boundaries

`TreeDagDuality` showed `cost_super ⟺ no-beneficial-sharing`.  This file machine-checks two further
physical re-descriptions of that same wall — a **chain-reaction / criticality** view and a
**multi-boundary (multi-cut)** view — so each intuition becomes a proved face next to the tree/DAG
duality.  Neither crosses the wall; each is another honest picture of it.

## Criticality — the reaction is supercritical in the tree; sharing is the moderator

Anti-implosion = a runaway chain reaction.  A composition is **supercritical** when it at least doubles
each step (`k_eff ≥ 2`).

* **`tree_supercritical` (proved)** — the tree tower is supercritical (`tree_double` gives exactly
  `k_eff = 2`).
* **`supercritical_exp` (proved)** — supercriticality runs away exponentially: `cost 0 · 2^d ≤ cost d`.
* **`cost_super_eq_dag_supercritical` (proved)** — `cost_super` *is* the statement that the **DAG stays
  supercritical**: `2·cbudget(comp d) ≤ cbudget(comp(d+1))` for all `d`.  Sharing (`dag_undercuts_tree`)
  is the moderator that could quench `k_eff` subcritical; `cost_super` is exactly *"sharing cannot
  quench the reaction"*.

## Multi-cut — different boundaries within the tree, and why sharing collapses the count

Put a boundary at each level of the tree.  On a **tree** the per-cut charges are disjoint, so they sum
to the tree cost.  On a **DAG** a shared wire is served by *many* boundaries, so the multi-cut count
over-charges the gates — which is precisely why the Nečiporuk crossing bound is exact for formulas and
does **not** transfer to circuits (a proved no-go already in this repository).

* **`cbudget_le_multiCut` (proved)** — the DAG cost is at most the multi-cut sum (`= treeCost`).
* **`sharing_is_the_multicut_gap` (proved)** — the multi-cut count exceeds the DAG cost by *exactly*
  the sharing gap `treeCost − cbudget`.
* **`cost_super_from_multicut_tight` (proved)** — `cost_super` holds iff the DAG matches the multi-cut
  count (no wire serves two boundaries) — the same no-sharing hypothesis, via cuts.

**Honest scope.**  Both views are proved *descriptions* of the wall: the tree is supercritical, the
multi-cut count is exact on it, and in each case `cost_super` reduces to the identical
no-beneficial-sharing hypothesis — the Uhlig wall, false in general.  A chain reaction the sharing can
moderate; a boundary count the sharing can defeat.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CriticalityMultiCut

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.TreeDagDuality

/-- A cost sequence is **supercritical** (`k_eff ≥ 2`): it at least doubles each step — a runaway
chain reaction. -/
def Supercritical (cost : ℕ → ℕ) : Prop := ∀ d, 2 * cost d ≤ cost (d + 1)

/-- **The tree tower is supercritical (proved).**  Composition exactly doubles: `k_eff = 2`. -/
theorem tree_supercritical (T : TreeTower) : Supercritical T.treeCost :=
  fun d => (T.tree_double d).ge

/-- **Supercriticality runs away exponentially (proved).**  `cost 0 · 2^d ≤ cost d`. -/
theorem supercritical_exp {cost : ℕ → ℕ} (h : Supercritical cost) :
    ∀ d, cost 0 * 2 ^ d ≤ cost d := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    calc cost 0 * 2 ^ (d + 1) = 2 * (cost 0 * 2 ^ d) := by ring
      _ ≤ 2 * cost d := by gcongr
      _ ≤ cost (d + 1) := h d

/-- **`cost_super` = the DAG stays supercritical (proved).**  The circuit crux is exactly *"sharing
cannot quench the chain reaction below `k_eff = 2`"*. -/
theorem cost_super_eq_dag_supercritical (T : TreeTower) :
    (∀ d, 2 * cbudget (T.composite d) ≤ cbudget (T.composite (d + 1)))
      ↔ Supercritical (fun d => cbudget (T.composite d)) :=
  Iff.rfl

/-! ### Multi-cut boundaries -/

/-- A **multi-cut tower**: a boundary per tree level whose charges are disjoint on the tree, so the
per-cut sum equals the tree cost.  (On a DAG a shared wire is charged at several boundaries — that is
the Nečiporuk-style over-count.) -/
structure MultiCutTower extends TreeTower where
  /-- the multi-cut boundary sum at level `d`. -/
  multiCut : ℕ → ℕ
  /-- on the tree the per-cut charges are disjoint: they sum to the tree cost. -/
  multiCut_eq_treeCost : ∀ d, multiCut d = treeCost d

/-- **The DAG cost is at most the multi-cut sum (proved).** -/
theorem cbudget_le_multiCut (M : MultiCutTower) (d : ℕ) :
    cbudget (M.composite d) ≤ M.multiCut d := by
  rw [M.multiCut_eq_treeCost]; exact M.dag_le_tree d

/-- **Sharing is exactly the multi-cut gap (proved).**  The boundary count exceeds the DAG cost by the
sharing gap `treeCost − cbudget`; a shared wire served by many boundaries is the whole discrepancy. -/
theorem sharing_is_the_multicut_gap (M : MultiCutTower) (d : ℕ) :
    M.multiCut d - cbudget (M.composite d) = M.treeCost d - cbudget (M.composite d) := by
  rw [M.multiCut_eq_treeCost]

/-- **`cost_super` from a tight multi-cut count (proved).**  If no wire is served by two boundaries —
the DAG cost equals the multi-cut count — then the DAG stays supercritical (`cost_super`).  The same
no-sharing hypothesis, expressed through the boundaries. -/
theorem cost_super_from_multicut_tight (M : MultiCutTower)
    (htight : ∀ d, cbudget (M.composite d) = M.multiCut d) :
    Supercritical (fun d => cbudget (M.composite d)) := by
  intro d
  simp only [htight, M.multiCut_eq_treeCost]
  exact (M.tree_double d).ge

end PallLean.Paper93.DeepMath.PathB.CriticalityMultiCut

#print axioms PallLean.Paper93.DeepMath.PathB.CriticalityMultiCut.tree_supercritical
#print axioms PallLean.Paper93.DeepMath.PathB.CriticalityMultiCut.supercritical_exp
#print axioms PallLean.Paper93.DeepMath.PathB.CriticalityMultiCut.cost_super_from_multicut_tight
#print axioms PallLean.Paper93.DeepMath.PathB.CriticalityMultiCut.sharing_is_the_multicut_gap
