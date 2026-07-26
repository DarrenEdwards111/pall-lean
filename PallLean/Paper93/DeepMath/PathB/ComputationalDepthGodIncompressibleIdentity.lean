import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGodMoveNoShare
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthIncompressibleCertificate

/-!
# The checked identity: the God-Move IS the incompressible certificate

The map links the God-Move-no-share card and the incompressible-certificate card as "the same object, two
altitudes."  Here that link becomes a **machine-verified identity**: the God's non-sharing bound
(`godCost ≤ pCost`) and the incompressible certificate's superadditivity (`2·single ≤ batch`) are the
*same proposition* under the dictionary `k = 2`, `b = single`, `pCost = batch`.

Both are instances of one kernel — `IndependentSumBound whole k part := k·part ≤ whole` — the composite
cost is at least the independent sum of the parts.  The only difference is **provenance**:

* the **God** has the bound *for free* (`god_needs_no_sharing`: unbounded ⟹ no reason to compress);
* the **bounded observer** must be *supplied* the bound's two inputs (the `IncompressiblePair` fields:
  disjoint witnesses + per-copy incompressibility — the inputs SAT withholds).

The distance between "free" and "supplied" is `cost_super`.

## What is proved

* **`god_gives_bound`** — the God-view (`overlap = 0`) is `IndependentSumBound pCost k b`.
* **`incompressible_gives_bound`** — the certificate is `IndependentSumBound batch 2 single`.
* **`two_altitudes_same_bound`** — the identity: under the dictionary, `godCost ≤ pCost` **↔**
  `2·single ≤ batch` — literally the same proposition.
* **`god_move_is_the_certificate`** — the God's free bound *produces* the certificate's exact conclusion:
  a God-view with `k = 2`, `b = single` gives `2·single ≤ pCost`.  The God-Move yields the incompressible
  certificate.

## Honest scope

This is a definitional identity (like `curvature_is_cost_super`): it proves the two constructions are one
object, not that either is achievable for SAT.  The God holds it by nature; the bounded observer must
supply the two inputs, and for SAT's tower both are `cost_super`.  Same object, two altitudes; the altitude
between them is the wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.GodIncompressibleIdentity

open PallLean.Paper93.DeepMath.PathB.GodMoveNoShare
open PallLean.Paper93.DeepMath.PathB.IncompressibleCertificate

/-- The shared kernel of both certificates: the composite cost `whole` is at least the independent sum of
`k` parts of size `part`.  Superadditivity = no sharing. -/
def IndependentSumBound (whole k part : ℕ) : Prop := k * part ≤ whole

/-- **The God-view is an independent-sum bound (proved).**  In the God-view (`overlap = 0`) the observer
pays the full independent sum: `IndependentSumBound pCost k b`.  The God has it for free. -/
theorem god_gives_bound (G : GodDecomposition) (h0 : G.overlap = 0) :
    IndependentSumBound G.pCost G.k G.b :=
  god_needs_no_sharing G h0

/-- **The incompressible certificate is an independent-sum bound (proved).**  The two-copy certificate is
`IndependentSumBound batch 2 single`.  The bounded observer must supply its two inputs. -/
theorem incompressible_gives_bound (batch single : ℕ) (C : IncompressiblePair batch single) :
    IndependentSumBound batch 2 single :=
  incompressible_pair_superadditive batch single C

/-- **The checked identity (proved).**  Under the dictionary `k = 2`, `b = single`, `pCost = batch`, the
God's non-sharing bound and the incompressible certificate's superadditivity are the *same proposition*:
`godCost G ≤ pCost ↔ 2·single ≤ batch`.  Same object, two altitudes. -/
theorem two_altitudes_same_bound (G : GodDecomposition) (batch single : ℕ)
    (hk : G.k = 2) (hb : G.b = single) (hp : G.pCost = batch) :
    (godCost G ≤ G.pCost) ↔ (2 * single ≤ batch) := by
  have e : godCost G = 2 * single := by
    show G.k * G.b = 2 * single
    rw [hk, hb]
  rw [e, hp]

/-- **The God-Move produces the certificate (proved).**  A God-view with `k = 2`, `b = single`, no overlap
yields the incompressible certificate's exact conclusion `2·single ≤ pCost`.  The God-Move *is* the
incompressible certificate — held for free at the unbounded altitude. -/
theorem god_move_is_the_certificate (G : GodDecomposition) (single : ℕ)
    (hk : G.k = 2) (hb : G.b = single) (h0 : G.overlap = 0) :
    2 * single ≤ G.pCost := by
  have h := god_needs_no_sharing G h0
  have e : godCost G = 2 * single := by
    show G.k * G.b = 2 * single
    rw [hk, hb]
  rw [e] at h
  exact h

end PallLean.Paper93.DeepMath.PathB.GodIncompressibleIdentity

#print axioms PallLean.Paper93.DeepMath.PathB.GodIncompressibleIdentity.two_altitudes_same_bound
#print axioms PallLean.Paper93.DeepMath.PathB.GodIncompressibleIdentity.god_move_is_the_certificate
