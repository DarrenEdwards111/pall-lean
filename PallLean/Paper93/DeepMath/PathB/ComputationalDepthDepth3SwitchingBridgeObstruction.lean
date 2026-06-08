import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalDepthStars
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CircuitBudget

/-!
# Block-DT model, foundation 32: the switching-bridge obstruction (honest analysis) (branch only)

This file records, precisely, why the probabilistic two-model bridge does **not** close with the pieces
built so far — an honest no-go, in the spirit of the arc's earlier negative results, rather than a faked
closure.

## The two objects

* **`blockStream cs F σ`** (bricks 1–13) — descends by `killTerm`, which sets *every* free variable of the
  active term to the value that **falsifies** its literal (`killTerm`: `pos v ↦ false`, `neg v ↦ true`).
  So `blockStream` is the *single* "all-literals-false" path; `blockStream.length` is the number of
  blocks on that one path.  The switching **count** (`block_switching_count_tight`,
  `block_switching_prob_closed`) bounds `{ρ : blockStream.length = s}`.

* **`canonicalDTree cs w F σ`** (bricks 26–32) — at each active term it queries *all* its free variables
  and branches over *all* `2^|free|` assignments, recursing on every falsifying leaf with that leaf's own
  restriction.  `canonicalDTree.depth` is the *max* over all branches.

## The obstruction

`killTerm`'s "all-false" assignment is exactly **one** falsifying leaf of `canonicalDTree`'s block.  So
the `blockStream` path is a *single branch* of the branching `canonicalDTree`, hence

> `blockStream.length ≤ canonicalDTree.depth`   (the count's quantity is a **lower** bound).

A *lower* bound on the depth is useless for proving the tree **shallow**.  The switching count therefore
cannot upper-bound `canonicalDTree.depth`, and the hoped-for bridge
"`blockStream` short ⇒ `canonicalDTree` shallow ⇒ parity contradiction" does **not** hold with these
objects.  Independently, the deterministic depth of `canonicalDTree` is `= stars σ` for parity
(`canonicalDTree_depth_le_stars` ∧ `canonicalDTree_depth_ge_of_parity`), confirming no single-restriction
contradiction.

## What a correct bridge would require

Either (a) re-found Håstad's encoding/count on the *branching* canonical tree — counting restrictions
whose **tree depth** (not one path) is `≥ s` — or (b) define the refined Håstad canonical tree whose
depth equals the encoding length, and prove that equals `blockStream.length`.  Both are substantial,
research-level formalizations (the full multi-round switching lemma, not in Mathlib).  They are named
here precisely rather than asserted.

## What *is* fully proved (clean axioms, no `sorry`)

* the switching **count** and its closed Håstad **probability** bound (bricks 1–13, 20);
* the circuit-collapse union bound + restriction operation (bricks 13, 22);
* the **DT↔CNF/DNF swap**, **depth-reduction**, and circuit datatype (bricks 14–17);
* the **parity** lower bound (absolute + relativized) (bricks 18, 21);
* the **adaptive canonical tree**: eval-correct, `depth ≤ F·w`, `depth ≤ stars σ`, `depth ≥ stars σ` for
  parity (bricks 26–32);
* the unconditional **depth-2** parity size bound `dnf_parity_size_bound` (brick 24).

AC⁰ ceiling throughout; not P≠NP-strength.  No `sorry`, no `native_decide`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

-- The deterministic switching theory (the boundary of what closes cleanly):
#check @canonicalDTree_eval                 -- adaptive tree computes the DNF on the subcube
#check @canonicalDTree_depth_le             -- depth ≤ F · w
#check @canonicalDTree_depth_le_stars       -- depth ≤ stars σ  (tight, w-free)
#check @canonicalDTree_depth_ge_of_parity   -- parity ⇒ depth ≥ stars σ  (matches ⇒ no contradiction)
#check @shallow_canonical_not_parity        -- depth < stars σ ⇒ ≠ parity  (consumes a "shallow" the count cannot supply)
#check @DTree.dnf_parity_size_bound         -- unconditional depth-2 parity size bound

-- The probabilistic count (about the single killTerm path, a *lower* bound on canonical depth):
#check @block_switching_count_tight
#check @block_switching_prob_closed
#check @circuit_collapse_budget

end PallLean.Paper93.DeepMath.PathB.Depth3
