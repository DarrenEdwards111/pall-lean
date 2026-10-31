import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMirrorRestricted

/-!
# What `MirrorRestricted` actually proves about cost — and where it stops short of `cost_super`

A claimed "proof of `cost_super`" pointed at `MirrorRestricted` (`6d579af9`) as the base of a doubling
tower.  This file machine-checks EXACTLY what that construction's cost fact is, and proves the three
reasons it does not reach `cost_super` for SAT.  Every claim here is a theorem; the point is to put the
gap on the record, not to argue it.

## What `MirrorRestricted` genuinely proves

`concrete_mirror_readonce` / `sat_resonates_readonce`: `2^d ≤ gates (harmonics sq base d)`, where

* `gates` is the **formula (tree) gate-count**: `gates (node a b) = gates a + gates b + 1` — every
  subtree is written out in full, NO sharing;
* `sq t = node t t` writes **two literal copies** of `t`;
* `harmonics sq base d` is the `d`-fold self-composition — a tree of size `~2^d`.

So the honest fact is: *a `d`-fold doubled tree has at least `2^d` tree-gates.*  Machine-checked, real,
and — as shown below — a statement about the no-sharing measure on a `d`-growing object.

## The three gaps to `cost_super` (all proved here)

1. **Wrong measure — it is `gates` (tree), not `cbudget` (circuit).**  `gates_sq`: `gates (sq t) =
   2·gates t + 1`.  The doubling is an ARTIFACT of writing two copies.  We model the same tower under
   sharing (`dagTowerCost`, one gate per doubling) and prove it is **linear**: `dagTowerCost b₀ d =
   b₀ + d`.  `tree_tower_doubling` (tree cost doubles) vs `shared_tower_no_doubling` (shared cost
   cannot) is the crux: the tower's doubling IS the no-sharing assumption, not a proof of it — exactly
   `cost_super`'s wall (Uhlig) restated.  `concrete_separation`: on a fixed base the same tower has
   shared cost `11` while its tree cost is `≥ 2^{10} = 1024`.

2. **Wrong direction of the inequality.**  A lower bound on `gates` gives NO lower bound on `cbudget`,
   because `cbudget ≤ gates` (sharing only helps).  `lower_bound_does_not_transfer` proves the general
   shape: `a ≤ b` (here `cbudget ≤ gates`) plus `k ≤ b` (the `2^d` bound on `gates`) is consistent with
   `a` arbitrarily small — the bound does not descend.

3. **Not SAT, and not a fixed family.**  `bound_holds_for_arbitrary_base`: the `2^d` bound holds for
   ANY `base` with `1 ≤ gates base` — nothing satisfiability-specific.  And the bounded object
   `harmonics sq base d` GROWS with `d` (`tree_tower_doubling` shows its size ~doubles each step), so
   `2^d` bounds an exponentially-large object, not `cbudget` of a fixed-length SAT slice.

## Verdict

`MirrorRestricted` proves a genuine, machine-checked lower bound — for the TREE measure, in the
no-sharing regime, on a growing object, for an arbitrary base.  That is the easy side of the wall
(`[[project_cost_super_dichotomy]]`): `cost_super` for `cbudget` requires the doubling to survive
sharing, and this construction's doubling provably does NOT.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MirrorRestrictedCostAudit

open PallLean.Paper93.DeepMath.PathB.SupportLens
open PallLean.Paper93.DeepMath.PathB.Resonance
open PallLean.Paper93.DeepMath.PathB.SATResonatesReadOnce

variable {n : ℕ}

/-! ### Gap 1: the doubling is a no-sharing (tree) artifact -/

/-- **The tree doubling, exact (proved).**  `gates (sq t) = 2·gates t + 1`: gluing two copies
duplicates the gate count because both copies are written out. -/
theorem gates_sq (t : F n) : gates (sq t) = 2 * gates t + 1 := by
  have h : gates (sq t) = gates t + gates t + 1 := rfl
  omega

/-- The tree tower's cost obeys the doubling recurrence `g(d+1) = 2·g(d) + 1`. -/
theorem gates_harmonics_succ (base : F n) (d : ℕ) :
    gates (harmonics sq base (d + 1)) = 2 * gates (harmonics sq base d) + 1 := by
  have h : harmonics sq base (d + 1) = sq (harmonics sq base d) := rfl
  rw [h, gates_sq]

/-- **The SAME tower under sharing**: each self-composition `sq` is computed ONCE (one extra gate),
so the cost adds `1` per level instead of doubling. -/
def dagTowerCost (b₀ : ℕ) : ℕ → ℕ
  | 0 => b₀
  | d + 1 => dagTowerCost b₀ d + 1

/-- **The shared tower cost is LINEAR (proved).**  `dagTowerCost b₀ d = b₀ + d`. -/
theorem dagTowerCost_eq (b₀ d : ℕ) : dagTowerCost b₀ d = b₀ + d := by
  induction d with
  | zero => rfl
  | succ d ih => show dagTowerCost b₀ d + 1 = b₀ + (d + 1); rw [ih]; omega

/-- **The tree tower doubles (proved).**  `2·g(d) ≤ g(d+1)` — the resonance step, in the tree
measure. -/
theorem tree_tower_doubling (base : F n) (d : ℕ) :
    2 * gates (harmonics sq base d) ≤ gates (harmonics sq base (d + 1)) := by
  rw [gates_harmonics_succ]; omega

/-- **The shared tower CANNOT double (proved).**  Once the tower has `≥ 2` gates, `2·c ≤ c+1` fails —
so the doubling law is FALSE under sharing.  This is precisely `cost_super`'s content: the doubling
holds iff sharing is forbidden. -/
theorem shared_tower_no_doubling (b₀ d : ℕ) (h : 2 ≤ dagTowerCost b₀ d) :
    ¬ (2 * dagTowerCost b₀ d ≤ dagTowerCost b₀ (d + 1)) := by
  show ¬ (2 * dagTowerCost b₀ d ≤ dagTowerCost b₀ d + 1)
  omega

/-- A fixed base: `node (var 0) (var 0)`, one gate. -/
def base1 : F 1 := F.node (F.var 0) (F.var 0)

/-- **Concrete separation (proved).**  On `base1`, the same tower at depth `10` has shared cost `11`
but tree cost `≥ 1024` — linear vs exponential, from sharing alone. -/
theorem concrete_separation :
    dagTowerCost (gates base1) 10 < 2 ^ 10 ∧ 2 ^ 10 ≤ gates (harmonics sq base1 10) := by
  refine ⟨?_, sat_resonates_readonce base1 (by decide) 10⟩
  rw [dagTowerCost_eq]; decide

/-! ### Gap 2: a lower bound on `gates` does not transfer to `cbudget` -/

/-- **Lower bounds do not descend through `≤` (proved).**  Since `cbudget ≤ gates` (sharing only
helps), a lower bound `k ≤ gates` on the tree measure is fully consistent with `cbudget` being
STRICTLY below `k`: there are values with `cbudget ≤ gates`, `k ≤ gates`, yet `cbudget < k`.  So the
`2^d` bound on `gates` gives no lower bound whatsoever on `cbudget`. -/
theorem lower_bound_does_not_transfer :
    ∃ cbudgetVal gatesVal k : ℕ, cbudgetVal ≤ gatesVal ∧ k ≤ gatesVal ∧ cbudgetVal < k :=
  ⟨0, 2 ^ 10, 2 ^ 10, Nat.zero_le _, le_refl _, by decide⟩

/-! ### Gap 3: arbitrary base, growing object -/

/-- **The bound holds for ANY base (proved).**  `2^d ≤ gates (harmonics sq base d)` needs only
`1 ≤ gates base` — nothing SAT-specific; `base` is an arbitrary nontrivial formula. -/
theorem bound_holds_for_arbitrary_base (base : F n) (hbase : 1 ≤ gates base) (d : ℕ) :
    2 ^ d ≤ gates (harmonics sq base d) :=
  sat_resonates_readonce base hbase d

/-- The bounded object grows with `d`: its gate count at least doubles each level, so `2^d` bounds an
exponentially-large formula, not `cbudget` of a fixed-length slice. -/
theorem bounded_object_grows (base : F n) (d : ℕ) :
    2 * gates (harmonics sq base d) ≤ gates (harmonics sq base (d + 1)) :=
  tree_tower_doubling base d

end PallLean.Paper93.DeepMath.PathB.MirrorRestrictedCostAudit

#print axioms PallLean.Paper93.DeepMath.PathB.MirrorRestrictedCostAudit.gates_sq
#print axioms PallLean.Paper93.DeepMath.PathB.MirrorRestrictedCostAudit.dagTowerCost_eq
#print axioms PallLean.Paper93.DeepMath.PathB.MirrorRestrictedCostAudit.shared_tower_no_doubling
#print axioms PallLean.Paper93.DeepMath.PathB.MirrorRestrictedCostAudit.concrete_separation
#print axioms PallLean.Paper93.DeepMath.PathB.MirrorRestrictedCostAudit.bound_holds_for_arbitrary_base
#print axioms PallLean.Paper93.DeepMath.PathB.MirrorRestrictedCostAudit.lower_bound_does_not_transfer
