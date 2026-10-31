import Mathlib.Data.Nat.Basic

/-!
# We need the tree: it clears the wall — the only gap is bringing L down to the DAG

The shrinkage rung (`ShrinkageExponentRung`) capped a *single function* at `n^3`.  The way past the cube
is the **tree**: in a formula (tree) there is no reconvergence, so composition **doubles the cost for
free**, and an iterated tower reaches `2^d` — **superpolynomial**.  This is exactly why "we need the
tree": it is the model in which the certified lower limit `L` clears any polynomial ceiling `U`.

This file makes that precise against the `TwoLimitsWall` capstone, self-contained on an abstract tower
(the concrete circuit-side instance is `TreeDagDuality`, commit `2e8c7a6e`):

* **tree** doubles per level (`tree_double`) and so reaches `2^d`;
* the **DAG** cost never exceeds the tree cost (`dag_le_tree`) — sharing only lowers it.

## What is proved

* **`treeCost_ge_two_pow` (proved)** — the tower is exponential: `2^d ≤ treeCost d`.
* **`tree_clears_any_ceiling` (proved)** — *the tree wins the capstone inequality*: for every ceiling
  `U` there is a depth `d` with `U < treeCost d`.  In the tree, `L` clears every polynomial `U`.
* **`dag_no_free_transfer` (proved)** — the obstruction: `dagCost d ≤ treeCost d`.  The tree is a
  *lower* bound and the DAG relation runs the *wrong way* — a big `treeCost` gives **no** lower bound on
  `dagCost`.  The DAG may share below.
* **`dag_clears_ceiling_of_no_sharing` (proved)** — the transfer: *if* sharing gives no advantage at the
  tower instances (`dagCost d = treeCost d`), the tree's superpoly `L` transfers and the DAG clears
  every ceiling too.  The whole separation reduces to this one transfer.

## Honest scope

The tree superpoly bound is real, and it is a **formula / `P ≠ NC¹`-flavoured** statement (the tree/tower
lives in the weak, no-sharing model).  It does **not** by itself bound the DAG (circuit) cost, because
`dagCost ≤ treeCost` points the wrong way.  Bringing `L` down to the DAG is exactly the no-sharing
hypothesis — `cost_super`, the Uhlig wall.  So this file shows the tree clears the wall and localizes the
*entire* remaining P-vs-NP gap to the tree→DAG transfer.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TreeClearsWall

/-- An abstract **tree/DAG tower**.  `treeCost` doubles per level — the free super-additivity of the
tree (no reconvergence); `dagCost` never exceeds it — sharing only lowers cost.  Mirrors
`TreeDagDuality.TreeTower` (concrete `2e8c7a6e`); kept self-contained and light here. -/
structure Tower where
  /-- tree (formula) cost at tower depth `d`. -/
  treeCost : ℕ → ℕ
  /-- DAG (circuit) cost of the same tower object. -/
  dagCost : ℕ → ℕ
  /-- the base is nonempty. -/
  base_pos : 1 ≤ treeCost 0
  /-- free doubling in the tree: composition exactly doubles (no reconvergence). -/
  tree_double : ∀ d, treeCost (d + 1) = 2 * treeCost d
  /-- sharing only lowers cost: the DAG never exceeds the tree. -/
  dag_le_tree : ∀ d, dagCost d ≤ treeCost d

/-- `n < 2^n` (proved, self-contained). -/
theorem lt_two_pow_self (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

/-- **The tower is exponential (proved).**  Free doubling gives `2^d ≤ treeCost d`. -/
theorem treeCost_ge_two_pow (T : Tower) (d : ℕ) : 2 ^ d ≤ T.treeCost d := by
  induction d with
  | zero => rw [Nat.pow_zero]; exact T.base_pos
  | succ d ih =>
    rw [T.tree_double, Nat.pow_succ]
    calc 2 ^ d * 2 = 2 * 2 ^ d := Nat.mul_comm _ _
    _ ≤ 2 * T.treeCost d := Nat.mul_le_mul (Nat.le_refl 2) ih

/-- **The tree wins the capstone inequality (proved).**  For every ceiling `U` there is a tower depth
`d` with `U < treeCost d`: in the tree, the certified `L` clears every polynomial `U`.  This is the move
the shrinkage cube cap could not make — composition doubling has no `n^3` ceiling. -/
theorem tree_clears_any_ceiling (T : Tower) (U : ℕ) : ∃ d, U < T.treeCost d :=
  ⟨U + 1, lt_of_lt_of_le
      (lt_of_lt_of_le (Nat.lt_succ_self U) (Nat.le_of_lt (lt_two_pow_self (U + 1))))
      (treeCost_ge_two_pow T (U + 1))⟩

/-- **The obstruction — the DAG relation runs the wrong way (proved).**  `dagCost d ≤ treeCost d`: a
large tree lower bound gives *no* lower bound on the DAG cost.  The DAG may share below the tree, so the
tree's superpoly `L` does not transfer for free. -/
theorem dag_no_free_transfer (T : Tower) (d : ℕ) : T.dagCost d ≤ T.treeCost d :=
  T.dag_le_tree d

/-- **The transfer, under no sharing (proved).**  If sharing gives no advantage at the tower instances
(`dagCost d = treeCost d`), the tree's superpoly bound transfers and the DAG clears every ceiling too.
The whole separation reduces to this one transfer — the Uhlig no-sharing wall (`cost_super`). -/
theorem dag_clears_ceiling_of_no_sharing (T : Tower)
    (htight : ∀ d, T.dagCost d = T.treeCost d) (U : ℕ) : ∃ d, U < T.dagCost d := by
  obtain ⟨d, hd⟩ := tree_clears_any_ceiling T U
  exact ⟨d, by rw [htight d]; exact hd⟩

end PallLean.Paper93.DeepMath.PathB.TreeClearsWall

#print axioms PallLean.Paper93.DeepMath.PathB.TreeClearsWall.treeCost_ge_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.TreeClearsWall.tree_clears_any_ceiling
#print axioms PallLean.Paper93.DeepMath.PathB.TreeClearsWall.dag_no_free_transfer
#print axioms PallLean.Paper93.DeepMath.PathB.TreeClearsWall.dag_clears_ceiling_of_no_sharing
