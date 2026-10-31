import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDictionaryExactness

/-!
# Batching and resisting both live on the DAG — the tree is the shared doubling baseline

Darren: "batching beats doubling on the tree, SAT resists on the DAG."  The intuition is right but the
labels are flipped, and fixing them lands exactly on the goal.

The **tree** (formula) has no sharing: `treeCost = 2^d`, it *always* doubles — batching can never beat
doubling *on the tree*, because the tree *is* the doubling baseline.  Batching (sharing) is a **DAG**
phenomenon (`dagCost ≤ treeCost`), and *resisting* is a DAG phenomenon too.  Both live on the DAG; they
are its two possible behaviours.

* **`sharingTower`** (from `DictionaryExactness`) — the DAG **batches**: `dagCost = 1 ≪ 2^d = treeCost`.
  An *easy* function whose circuit shares everything.
* **`resistTower`** (here) — the DAG **resists**: `dagCost = treeCost = 2^d`.  This is what `SAT` looks
  like *if C3 holds* — no sharing, `cbudget = 2^d`.

## What is proved

* **`easy_batches`** — on the DAG, batching wins for the easy tower: `dagCost 1 < treeCost 1`.
* **`hard_resists`** — on the DAG, the hard tower resists: `dagCost = treeCost` at every level (the exact
  dictionary = no-sharing = C3).
* **`resist_is_superpoly`** — the resisting DAG is `2^d`: if SAT resists, `cbudget(SAT) = 2^d` — the
  separation.
* **`same_tree`** — both towers have the **same** tree (`2^d`).  The tree does not distinguish easy from
  hard; the entire distinction is on the DAG.

## The corrected intuition

"Batching wins for easy functions on the DAG (`sharingTower`); SAT **resists on the DAG**
(`resistTower`)."  That is correct, and *SAT resisting on the DAG is exactly C3 = `cost_super` = `P ≠ NP`*
— the goal.  The tree is the shared baseline both share; it settles nothing.  Which world SAT is in —
batch or resist — is the open question.  Proving it resists is proving the separation.

**Honest scope.**  `resistTower` is the *hypothesis* C3 made into a concrete tower (it assumes
`dagCost = 2^d`); it does not prove SAT is that tower.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BatchVsResist

open PallLean.Paper93.DeepMath.PathB.TreeClearsWall
open PallLean.Paper93.DeepMath.PathB.DictionaryExactness

/-- The **resisting** tower: `dagCost = treeCost = 2^d` — no sharing, the DAG resists batching.  This is
what `SAT` would be if C3 holds: `cbudget(SAT) = 2^d`. -/
def resistTower : Tower where
  treeCost := fun d => 2 ^ d
  dagCost := fun d => 2 ^ d
  base_pos := Nat.le_of_eq (Nat.pow_zero 2).symm
  tree_double := fun d => by rw [Nat.pow_succ, Nat.mul_comm (2 ^ d) 2]
  dag_le_tree := fun d => Nat.le_refl _

/-- **On the DAG, batching wins for the easy tower (proved).**  `dagCost 1 = 1 < 2 = treeCost 1`: the
circuit shares everything — an easy function. -/
theorem easy_batches : sharingTower.dagCost 1 < sharingTower.treeCost 1 := by decide

/-- **On the DAG, the hard tower resists (proved).**  `dagCost d = treeCost d` at every level — the exact
dictionary = no-sharing = C3.  This is what `SAT` resisting looks like. -/
theorem hard_resists : ∀ d, resistTower.dagCost d = resistTower.treeCost d :=
  fun _ => rfl

/-- **The resisting DAG is superpolynomial (proved).**  `2^d ≤ dagCost d`.  So if `SAT` resists batching
(`SAT = resistTower`), then `cbudget(SAT) = 2^d` — the separation. -/
theorem resist_is_superpoly (d : ℕ) : 2 ^ d ≤ resistTower.dagCost d :=
  Nat.le_refl _

/-- **Both towers share the same tree (proved).**  `sharingTower.treeCost = resistTower.treeCost = 2^d`.
The tree does not distinguish easy from hard — the entire distinction is on the DAG (batch vs resist).
"Batching beats doubling on the tree" is a category error: the tree always doubles. -/
theorem same_tree (d : ℕ) : sharingTower.treeCost d = resistTower.treeCost d :=
  rfl

end PallLean.Paper93.DeepMath.PathB.BatchVsResist

#print axioms PallLean.Paper93.DeepMath.PathB.BatchVsResist.easy_batches
#print axioms PallLean.Paper93.DeepMath.PathB.BatchVsResist.hard_resists
#print axioms PallLean.Paper93.DeepMath.PathB.BatchVsResist.resist_is_superpoly
#print axioms PallLean.Paper93.DeepMath.PathB.BatchVsResist.same_tree
