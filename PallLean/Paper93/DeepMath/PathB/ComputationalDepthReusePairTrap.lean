import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDictionaryExactness

/-!
# Counting pairs across the reuse — it survives, but it over-counts

The tension: a *valid* count (`≤ cbudget`) collapses under reuse (support); can we count pairs in a way
that **survives** reuse?  Yes — count pairs of **occurrences** (leaf positions), not pairs of distinct
variables.  Occurrences double even when inputs are shared.  This file builds that lens and shows what
goes wrong.

Model the occurrence count by `treeCost` (the tree/formula leaf count, which doubles by `tree_double`
even under reuse).  "Pairs across the reuse" is then `pairAcrossReuse = treeCost²`.

## What is proved

* **`pairAcrossReuse_grows` (proved)** — it **survives reuse**: `2^d ≤ pairAcrossReuse T d`.  Counting
  occurrence-pairs keeps growing through the tower regardless of sharing.
* **`pairAcrossReuse_overcounts` (proved)** — but it **over-counts**: on the sharing tower the
  occurrence-pair count is `4` while the actual circuit cost is `1`.  So `pairAcrossReuse > dagCost` — it
  is **not** `≤ cbudget`, hence not a valid lens.

## The two-sided trap

Now both walls are on the table, proved:

* **valid counts collapse** — support (`LensTension`): `μ ≤ cbudget`, but reuse makes it stop doubling.
* **reuse-surviving counts over-count** — occurrence-pairs (here): they double through reuse, but they
  count *occurrences* (the tree), which sharing collapses, so `μ > cbudget`.

A count that survives reuse counts the **unfolded tree**; a count valid for the circuit must respect
**sharing**.  These pull opposite ways.  A measure that is *both* — reuse-surviving **and** `≤ cbudget` —
cannot be a raw occurrence/variable count: it must measure the function's **intrinsic** structure, not
its syntax.  That is KW communication complexity / the KRW program — the open problem.

**Honest scope.**  Proved: counting pairs across reuse survives but over-counts, closing the two-sided
trap.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ReusePairTrap

open PallLean.Paper93.DeepMath.PathB.TreeClearsWall
open PallLean.Paper93.DeepMath.PathB.DictionaryExactness

/-- Counting **pairs across the reuse** = pairs of occurrences (leaf positions).  The occurrence count is
`treeCost` (it doubles under reuse via `tree_double`); the pair count is its square. -/
def pairAcrossReuse (T : Tower) (d : ℕ) : ℕ := T.treeCost d * T.treeCost d

/-- **It survives reuse (proved).**  `2^d ≤ pairAcrossReuse T d`: counting occurrence-pairs keeps growing
through the tower no matter how inputs are shared. -/
theorem pairAcrossReuse_grows (T : Tower) (d : ℕ) : 2 ^ d ≤ pairAcrossReuse T d := by
  have h : 2 ^ d ≤ T.treeCost d := treeCost_ge_two_pow T d
  have h1 : 1 ≤ T.treeCost d := le_trans (Nat.one_le_two_pow) h
  have h2 : T.treeCost d * 1 ≤ T.treeCost d * T.treeCost d := Nat.mul_le_mul (Nat.le_refl _) h1
  calc 2 ^ d ≤ T.treeCost d := h
    _ = T.treeCost d * 1 := (Nat.mul_one _).symm
    _ ≤ pairAcrossReuse T d := h2

/-- **But it over-counts — not a valid lens (proved).**  On the sharing tower the occurrence-pair count
is `4` while the actual circuit cost is `1`: `dagCost 1 = 1 < 4 = pairAcrossReuse`.  A reuse-surviving
count exceeds `cbudget`, because it counts occurrences (the tree), which sharing collapses. -/
theorem pairAcrossReuse_overcounts :
    ∃ (T : Tower) (d : ℕ), T.dagCost d < pairAcrossReuse T d :=
  ⟨sharingTower, 1, by decide⟩

end PallLean.Paper93.DeepMath.PathB.ReusePairTrap

#print axioms PallLean.Paper93.DeepMath.PathB.ReusePairTrap.pairAcrossReuse_grows
#print axioms PallLean.Paper93.DeepMath.PathB.ReusePairTrap.pairAcrossReuse_overcounts
