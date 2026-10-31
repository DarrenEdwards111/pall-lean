import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSupportLens

/-!
# The lens tension: superadditivity needs disjoint inputs, non-triviality needs reuse

`SupportLens` built a real lens that is valid and superadditive, yet caps at `n`.  This file pins *why*
the two properties fight — the tension runs through **input reuse**, which is exactly batching.

The support count doubles **only on disjoint inputs**.  The deficit from doubling is exactly the shared
inputs:

* **`sharing_deficit` (proved)** — inclusion–exclusion: `|support(node a b)| + |shared| = |support a| +
  |support b|`.  The support "loses" precisely the shared inputs.
* **`sharing_breaks_doubling` (proved)** — if the two copies share *any* input, the support **fails** to
  double: `|support(node a b)| < |support a| + |support b|`.
* **`support_fails_when_shared` (proved)** — the simplest witness: two copies of the same variable share
  it, so the support is `1`, not `2`.

## The frontier, made concrete

- To make the lens **superadditive**, the tower step must use **disjoint** inputs — but then the input
  size doubles too, and the bound (`2^d`) is only linear in `n`.  Trivial.
- To make the bound **super-polynomial in `n`**, the tower must be **input-efficient** — it must **reuse**
  inputs — and by `sharing_breaks_doubling` the support then fails to double.  The lens loses
  superadditivity exactly where it would matter.

Input reuse is mass production / batching.  So the lens tension *is* the wall: a measure superadditive on
an **input-efficient** (reusing) tower must not lose the shared inputs — it must see structure that
survives reuse, which raw input-counting cannot.  Khrapchenko (pairs) and shrinkage buy a polynomial past
this and then cap.  A lens that survives reuse past the cap is the open object.

**Honest scope.**  Proved: the support lens's superadditivity is broken by exactly the input reuse that
makes a tower non-trivial.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.LensTension

open PallLean.Paper93.DeepMath.PathB.SupportLens

/-- **The deficit is exactly the shared inputs (proved).**  Inclusion–exclusion: the support of a
composition plus the shared inputs equals the sum of the two supports.  Doubling loses precisely the
overlap. -/
theorem sharing_deficit {n : ℕ} (a b : F n) :
    (support (F.node a b)).card + (support a ∩ support b).card
      = (support a).card + (support b).card := by
  show (support a ∪ support b).card + (support a ∩ support b).card = _
  exact Finset.card_union_add_card_inter _ _

/-- **Sharing breaks doubling (proved).**  If the two copies share any input, the support fails to double.
Input reuse is exactly the deficit. -/
theorem sharing_breaks_doubling {n : ℕ} (a b : F n) (hshared : (support a ∩ support b).Nonempty) :
    (support (F.node a b)).card < (support a).card + (support b).card := by
  have h := sharing_deficit a b
  have hpos : 0 < (support a ∩ support b).card := Finset.card_pos.mpr hshared
  omega

/-- **The simplest witness (proved).**  Two copies of the same variable share it, so the support is `1`,
not `2` — superadditivity fails under the most basic reuse. -/
theorem support_fails_when_shared :
    ∃ (n : ℕ) (a b : F n),
      (support (F.node a b)).card < (support a).card + (support b).card := by
  refine ⟨1, F.var 0, F.var 0, sharing_breaks_doubling _ _ ?_⟩
  simp [support]

end PallLean.Paper93.DeepMath.PathB.LensTension

#print axioms PallLean.Paper93.DeepMath.PathB.LensTension.sharing_deficit
#print axioms PallLean.Paper93.DeepMath.PathB.LensTension.sharing_breaks_doubling
#print axioms PallLean.Paper93.DeepMath.PathB.LensTension.support_fails_when_shared
