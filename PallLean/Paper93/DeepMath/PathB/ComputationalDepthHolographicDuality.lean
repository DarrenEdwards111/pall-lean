import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTunnelTransfer

/-!
# C3 and the God-Move as two sides of one coin — the duality is real, but the dictionary is one-way

Darren's move: don't *break* C3, *transform* it.  C3 is the 2D boundary; the God-Move is gravity bending
it into the 3D bulk (the holographic projection = the transfer); two sides of one coin (AdS/CFT).

The duality is genuine — and its **exact shape** is the whole point.  In AdS/CFT the boundary↔bulk
dictionary is an *exact bijection*: a hard boundary quantity can be *read off* an easy bulk computation.
Here the dictionary is a **one-way inequality**, and that is precisely why the transformation cannot
compute C3.

* bulk = the tree tower (`treeCost`, `= 2^d` for free);
* boundary = the circuit floor (`dagCost`, `= cbudget`);
* the dictionary = `dagCost ≤ treeCost`.

## What is proved

* **`dictionary_one_way`** — `dagCost d ≤ treeCost d`.  The boundary is bounded by the bulk, but **not
  conversely** — the map is not a bijection.  The bulk's free `2^d` gives **no** lower bound on the
  boundary floor (the DAG may share below).
* **`exact_dictionary_iff_no_sharing`** — the dictionary is **exact / invertible** (bulk determines
  boundary, `treeCost ≤ dagCost` too) **iff** `dagCost = treeCost`, the no-sharing hypothesis =
  `cost_super` = C3.  So the coin *flips* — you read C3 off the bulk — **exactly when C3 already holds**.

## Honest scope

"Two sides of one coin" is correct: C3 and the transfer are **equivalent** (`gauge ⟺ C3`,
`tunnel ⟺ no-sharing`).  But a duality between equivalent statements is a restatement, not a proof.  And
unlike AdS/CFT, the dictionary here is a one-way `≤`: gravity bends 2D→3D fine (the bulk `2^d` is free),
but the projection 3D→2D is **lossy** — it recovers the boundary floor only under no-sharing, which is
C3.  So the transformation is *usable* precisely when C3 holds; it cannot *produce* C3.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.HolographicDuality

open PallLean.Paper93.DeepMath.PathB.TreeClearsWall
open PallLean.Paper93.DeepMath.PathB.TunnelTransfer

/-- **The holographic dictionary is one-way (proved).**  `dagCost d ≤ treeCost d`: the boundary (DAG) is
bounded by the bulk (tree), but not conversely.  Unlike an exact AdS/CFT dictionary this map is not
invertible — the bulk's free `2^d` gives no lower bound on the boundary floor. -/
theorem dictionary_one_way (T : Tower) (d : ℕ) : T.dagCost d ≤ T.treeCost d :=
  T.dag_le_tree d

/-- **The dictionary is exact iff no-sharing = C3 (proved).**  The map is *invertible* — the bulk
determines the boundary (`treeCost ≤ dagCost` as well) — **iff** `dagCost = treeCost` everywhere, the
no-sharing hypothesis (`cost_super` = C3).  So the coin flips (C3 is readable off the bulk) exactly when
C3 already holds; the transformation is usable ⟺ C3, and cannot produce it. -/
theorem exact_dictionary_iff_no_sharing (T : Tower) :
    Tunnel T ↔ ∀ d, T.dagCost d = T.treeCost d :=
  tunnel_iff_no_sharing T

/-- **The bulk bound alone gives no boundary bound (proved).**  The bulk is superpoly for free
(`2^d ≤ treeCost d`), yet with only the one-way dictionary this yields nothing about the boundary floor:
the projection back is lossy.  Recovering a boundary lower bound needs the exact dictionary
(`exact_dictionary_iff_no_sharing`), i.e. C3. -/
theorem bulk_free_boundary_open (T : Tower) (d : ℕ) : 2 ^ d ≤ T.treeCost d :=
  treeCost_ge_two_pow T d

end PallLean.Paper93.DeepMath.PathB.HolographicDuality

#print axioms PallLean.Paper93.DeepMath.PathB.HolographicDuality.dictionary_one_way
#print axioms PallLean.Paper93.DeepMath.PathB.HolographicDuality.exact_dictionary_iff_no_sharing
#print axioms PallLean.Paper93.DeepMath.PathB.HolographicDuality.bulk_free_boundary_open
