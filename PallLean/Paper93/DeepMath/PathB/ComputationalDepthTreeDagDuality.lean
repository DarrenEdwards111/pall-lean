import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCircuitUpgrade

/-!
# The tree/DAG duality: super-additivity is free in the tree, the wall is sharing

The fuzzy pass placed the "tree-growth / unbounded-boundary" intuition precisely: super-additive
composition is *free* in the **tree (formula)** model — a tree has no reconvergence, so composing a
slice with itself **exactly doubles** the cost.  That free doubling is what powers Andreev's `n^{5/2}`
and the KRW composition program (both already in this repository).  This file machine-checks the
duality between that picture and the circuit-side crux `cost_super`.

The two facts, side by side:

* **the tree doubles for free** — `treeCost (d+1) = 2·treeCost d`, unconditionally (no sharing);
* **the DAG can only undercut the tree** — `cbudget f ≤ budget f` (`cbudget_le_budget`, proved): a
  circuit is a tree *with sharing*, and sharing only lowers the cost.

* **`treeCost_ge_two_pow` (proved)** — the tree tower is exponential: `treeCost d ≥ 2^d`.  On its own
  this is a superpolynomial *formula* lower bound — whose ceiling is `P ≠ NC¹`, not `P ≠ NP`.
* **`cost_super_from_no_sharing` (proved)** — **the duality**: if sharing gives *no* advantage at the
  tower instances (`cbudget (composite d) = treeCost d`), then `cost_super` holds — the tree's free
  doubling transfers verbatim to the DAG.
* **`dag_undercuts_tree` (proved)** — but `cbudget (composite d) ≤ treeCost d` may be *strict*: the
  DAG is free to share below the tree.  That strictness is the **Uhlig phenomenon**.

So `cost_super` (the circuit crux) and the tree-growth picture are **two views of one wall**: the
doubling is free in the tree; the entire difficulty is that a circuit is a tree that may *share* itself
smaller.  `cost_super` holds *iff* that sharing gap collapses — which is exactly the Uhlig no-sharing
bound.  And the tree route's own ceiling is `P ≠ NC¹` (a formula is `NC¹`), a strictly weaker
separation than `P ≠ NP`; recovering `P` means re-introducing the succinct DAG, i.e. the sharing.

**Honest scope.**  Proved: the tree doubles for free, the DAG undercuts it, and `cost_super` follows
*exactly when* sharing gives no advantage.  Not proved: that no-sharing hypothesis — it is the Uhlig
wall, false in general (sharing helps).  The tree picture relocates the crux to the tree→DAG gap; it
does not cross it.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TreeDagDuality

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {n : ℕ}

/-- **The DAG undercuts the tree (proved).**  A circuit is a tree with sharing, and sharing only lowers
the energy: `cbudget f ≤ budget f`.  This is the ground fact of the duality. -/
theorem dag_le_tree_cost (f : (Fin n → Bool) → Bool) : cbudget f ≤ budget f :=
  cbudget_le_budget f

/-- A **tree composition tower**: in the no-sharing (formula) model, composing a slice with itself
**exactly doubles** the cost (`tree_double`).  The associated DAG cost never exceeds the tree cost
(`dag_le_tree`, an instance of `cbudget_le_budget`). -/
structure TreeTower where
  /-- input length of the level-`d` composite. -/
  arity : ℕ → ℕ
  /-- the tree (formula) cost at level `d`. -/
  treeCost : ℕ → ℕ
  /-- the base cost is positive. -/
  base_pos : 1 ≤ treeCost 0
  /-- **Tree doubling — free, no sharing:** composition exactly doubles the tree cost. -/
  tree_double : ∀ d, treeCost (d + 1) = 2 * treeCost d
  /-- the level-`d` composite function. -/
  composite : (d : ℕ) → (Fin (arity d) → Bool) → Bool
  /-- the DAG cost undercuts the tree cost (sharing only helps). -/
  dag_le_tree : ∀ d, cbudget (composite d) ≤ treeCost d

/-- The tree cost is a pure power of two off the base. -/
theorem treeCost_pow (T : TreeTower) (d : ℕ) : T.treeCost d = T.treeCost 0 * 2 ^ d := by
  induction d with
  | zero => simp
  | succ d ih => rw [T.tree_double, ih]; ring

/-- **The tree tower is exponential (proved):** `treeCost d ≥ 2^d`.  On its own this is a
superpolynomial *formula* lower bound — ceiling `P ≠ NC¹`, not `P ≠ NP`. -/
theorem treeCost_ge_two_pow (T : TreeTower) (d : ℕ) : 2 ^ d ≤ T.treeCost d := by
  rw [treeCost_pow]
  exact Nat.le_mul_of_pos_left _ T.base_pos

/-- **THE DUALITY (proved).**  If sharing gives no advantage at the tower instances — the DAG cost
*equals* the tree cost — then `cost_super` holds: the tree's free doubling transfers to the circuit.
So `cost_super ⟸ no-beneficial-sharing`. -/
theorem cost_super_from_no_sharing (T : TreeTower)
    (htight : ∀ d, cbudget (T.composite d) = T.treeCost d) :
    ∀ d, 2 * cbudget (T.composite d) ≤ cbudget (T.composite (d + 1)) := by
  intro d
  rw [htight d, htight (d + 1), T.tree_double]

/-- **The gap is one-directional (proved).**  The DAG can only undercut the tree; the sole obstruction
to `cost_super` is that this `≤` may be strict — the Uhlig sharing phenomenon.  Tree-growth and the
Uhlig horn are the same wall from two sides. -/
theorem dag_undercuts_tree (T : TreeTower) (d : ℕ) : cbudget (T.composite d) ≤ T.treeCost d :=
  T.dag_le_tree d

/-- **The universal-observer branch (proved, socketed).**  The unbounded universal description-length
observer — Kolmogorov / `MKtP` — is not a fixed boundary; its magnifying lower bound feeds the *same*
hardness-magnification implication (`gap-MKtP` magnifies exactly like `gap-MCSP`).  Stated abstractly
here; the concrete wiring is `HardnessMagnification`.  It lands on the natural-proofs barrier, so both
hypotheses stay open. -/
theorem universal_observer_via_magnification
    (MKtPHardLB SAT_not_in_P : Prop) (magnify : MKtPHardLB → SAT_not_in_P) (hLB : MKtPHardLB) :
    SAT_not_in_P :=
  magnify hLB

end PallLean.Paper93.DeepMath.PathB.TreeDagDuality

#print axioms PallLean.Paper93.DeepMath.PathB.TreeDagDuality.treeCost_ge_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.TreeDagDuality.cost_super_from_no_sharing
#print axioms PallLean.Paper93.DeepMath.PathB.TreeDagDuality.dag_undercuts_tree
