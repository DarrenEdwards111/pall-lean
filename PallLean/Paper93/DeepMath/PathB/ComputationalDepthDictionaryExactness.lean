import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHolographicDuality

/-!
# Can we "make the dictionary exact"? Not as a theorem — it is false in general, and C3 for SAT

Darren: make the dictionary exact — prove `dagCost = treeCost` (no-sharing, batching can't beat
doubling).  This file is the honest answer, machine-checked: exactness is **not** a provable general
fact, and for the SAT tower it **is** `P ≠ NP`.

## Reason 1 — the dictionary is provably NOT exact in general

`sharingTower` is a tower where sharing *wins*: `dagCost d = 1` (constant) while `treeCost d = 2^d`.  It
satisfies every tower axiom (`dagCost ≤ treeCost`, free doubling), yet the dictionary is strictly
one-way.  This is Uhlig mass production, abstractly — the DAG shares everything below the tree.

* **`dictionary_can_be_strict` (proved)** — `∃ T d, dagCost d < treeCost d`.  So "the dictionary is
  exact" is **false as a general theorem**; it cannot simply be proved, because there are towers where it
  fails.

## Reason 2 — exactness for the SAT tower is C3 = cost_super = P ≠ NP

* **`exactness_iff_no_sharing` (proved)** — the dictionary is exact (`dagCost = treeCost`) iff the tower
  has no beneficial sharing.  For the SAT tower that is `cost_super` = C3 = the separation itself.  So
  "make the dictionary exact *there*" is *prove P ≠ NP* — the open wall, not a step toward it.

## Honest scope

Making the dictionary exact is therefore either **refuted** (as a general statement — `sharingTower`) or
**equal to P ≠ NP** (for the SAT tower).  There is no third reading in which it is a lemma I can
discharge.  I will not fabricate a proof of the SAT case, because it is exactly the open problem — the
whole map converges on it.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DictionaryExactness

open PallLean.Paper93.DeepMath.PathB.TreeClearsWall
open PallLean.Paper93.DeepMath.PathB.TunnelTransfer

/-- A tower where **sharing wins**: `dagCost d = 1` while `treeCost d = 2^d`.  Uhlig mass production,
abstractly — the DAG shares everything below the tree.  Witness that exactness can fail. -/
def sharingTower : Tower where
  treeCost := fun d => 2 ^ d
  dagCost := fun _ => 1
  base_pos := Nat.le_of_eq (Nat.pow_zero 2).symm
  tree_double := fun d => by rw [Nat.pow_succ, Nat.mul_comm (2 ^ d) 2]
  dag_le_tree := fun d => Nat.one_le_pow d 2 (by decide)

/-- **The dictionary is not exact in general (proved).**  There is a tower with `dagCost d < treeCost d`
strictly — sharing genuinely wins.  So exactness is false as a general theorem and cannot simply be
proved. -/
theorem dictionary_can_be_strict : ∃ (T : Tower) (d : ℕ), T.dagCost d < T.treeCost d :=
  ⟨sharingTower, 1, by decide⟩

/-- **Exactness for a tower IS no-sharing = cost_super (proved).**  The dictionary is exact
(`dagCost = treeCost`, equivalently `Tunnel`) iff the tower has no beneficial sharing.  For the SAT tower
this is C3 = `cost_super` = `P ≠ NP`.  Making the dictionary exact there is proving the separation. -/
theorem exactness_iff_no_sharing (T : Tower) :
    Tunnel T ↔ ∀ d, T.dagCost d = T.treeCost d :=
  tunnel_iff_no_sharing T

end PallLean.Paper93.DeepMath.PathB.DictionaryExactness

#print axioms PallLean.Paper93.DeepMath.PathB.DictionaryExactness.dictionary_can_be_strict
#print axioms PallLean.Paper93.DeepMath.PathB.DictionaryExactness.exactness_iff_no_sharing
