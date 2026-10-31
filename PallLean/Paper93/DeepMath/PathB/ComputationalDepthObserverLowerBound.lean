import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverBoundary
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRouteFProbe

/-!
# Observer boundary entropy — the LOWER-bound principle (the reverse direction)

`ComputationalDepthObserverBoundary` proved the *upper/easy* direction (`B = O(log n) ⇒ poly rank`).  This
file proves the *lower/hard-direction principle*: **many distinguishable boundary continuations force large
boundary entropy.**  Together they give a two-sided characterization — and locate exactly what a separation
would still require.

## Proved

* `observer_boundary_lower_bound` — a fooling set of `K` distinguishable continuations (`K ≤ rank`) forces
  `B ≥ log₂ K`.  (The converse of `lowBoundary_poly_rank`, via `rank ≤ 2^B`.)
* `foolingSet_forces_boundary` — `K ≤ 2^B ⇒ log₂ K ≤ B`.
* `equality_forces_boundary` — concrete: the size-`4` identity / EQUALITY communication matrix
  (`RouteFProbe.identity_full_rank`) forces `B ≥ 2`.  The principle bites.

So the invariant is now a **two-sided theorem**: `B` tracks `log₂` of the (fixed-cut) rank both ways.

## What a separation still needs — and the sharp obstruction

The principle gives `B ≥ log₂ K` *at a fixed cut/decomposition*.  To separate, one needs

> `B ≥ ω(log n)` for SAT under **every** admissible decomposition,

which is the open all-decompositions lower bound (`= CookLevinFrontierHyp`, `P`-vs-`NP`-strength).  And the
fixed-cut version is **provably insufficient**: **EQUALITY** on `k+k` bits has a `2^k` fooling set, so
`B ≥ k` at that cut (`equality_forces_boundary`, `k=2` instance) — yet EQUALITY has an `O(k)`-size circuit,
hence *low* boundary under its natural bit-pairing decomposition.  So **high fixed-cut boundary does not
imply hard**; only high *minimum-over-decompositions* boundary does, and proving that for SAT is the open
content.

This is Option A (communication route) made precise: the rank/communication lower bound is provable at a
cut (the principle), but the machine *chooses* the decomposition, so a single cut never suffices — exactly
why the separation does not fall out of the principle.  Nothing here asserts the SAT lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.ObserverBoundary

open PallLean.Paper93.DeepMath.PathB

/-- **Observer boundary LOWER bound (the reverse principle).**  If a faithful observer must distinguish `K`
boundary continuations (a fooling set: `K ≤ rank`), then its boundary entropy is `≥ log₂ K`. -/
theorem observer_boundary_lower_bound (K rank B : ℕ) (hfool : K ≤ rank) (hrank : rank ≤ 2 ^ B) :
    Nat.log 2 K ≤ B := by
  have hKB : K ≤ 2 ^ B := le_trans hfool hrank
  calc Nat.log 2 K ≤ Nat.log 2 (2 ^ B) := Nat.log_mono_right hKB
    _ = B := Nat.log_pow (by norm_num) B

/-- A fooling set of size `K` forces `B ≥ log₂ K`. -/
theorem foolingSet_forces_boundary (K B : ℕ) (hfool : K ≤ 2 ^ B) : Nat.log 2 K ≤ B :=
  observer_boundary_lower_bound K (2 ^ B) B hfool (le_refl _)

/-- **Concrete:** the size-`4` identity / EQUALITY communication matrix forces `B ≥ 2`.  (Its rank is `4`
by `RouteFProbe.identity_full_rank`; a `4`-distinguishable boundary cannot be resolved below `B = 2`.)
EQUALITY is nonetheless trivially computable — so this fixed-cut bound is *not* a hardness proof. -/
theorem equality_forces_boundary (B : ℕ)
    (hrank : RouteFProbe.f2rank [[true,false,false,false],[false,true,false,false],
              [false,false,true,false],[false,false,false,true]] ≤ 2 ^ B) :
    2 ≤ B := by
  have h4 : (4 : ℕ) ≤ 2 ^ B := by rwa [RouteFProbe.identity_full_rank] at hrank
  have := foolingSet_forces_boundary 4 B h4
  simpa using this

end PallLean.Paper93.DeepMath.PathB.ObserverBoundary

#print axioms PallLean.Paper93.DeepMath.PathB.ObserverBoundary.observer_boundary_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverBoundary.equality_forces_boundary
