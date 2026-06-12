import PallLean.Paper93.DeepMath.PathB.ComputationalDepthForcingFamilyMin

/-!
# Expander amplification of a forcing family (the Lagrangian's `−𝐀` term, proved)

The Lagrangian (`SCOPE_NFRAME_OBSERVER_LAGRANGIAN.md`) ranks "spend the expander amplification gain `−𝐀`" as
the move that enlarges a structured forcing class.  This file realizes `−𝐀` concretely: **tensoring
forcing families amplifies the threshold additively.**  Each factor is an expander-forced instance; the
product's `min`-boundary is the **sum** of the factors' thresholds — so combining `k` expander-forced
structures amplifies the forced boundary `k`-fold, while every decomposition in the product class stays
forced (the `min` does not drop).

## Proved (clean axioms, no `sorry`)

* `ForcingFamily.prod` — the product (tensor) of two forcing families: decompositions are pairs, boundary is
  the **sum** of component boundaries (independent structures), threshold is the **sum** of thresholds.
* `ForcingFamily.prod_threshold_le_min` — the amplified bound: `F.threshold + G.threshold ≤ (F.prod G).min`.
* `hardF_prod_amplified` — instantiated on the proved `hardF` address-block family: two independent copies
  give `min ≥ 2·(2^b − 1)` — the threshold amplified.

## Reading

`−𝐀` is the gain that pays for boundary cost: an expander forces each factor (`hardF`'s address-block bound is
the multiplexer's expander-derived subfunction count; expander-Tseitin's is `c·t`), and the product
*amplifies* the forced boundary additively.  This is the formal content of "expander amplification spreads
the bound": more forced structure, higher `min`, with the structured class strictly enlarged (the product
class) and the `min` still super-logarithmic.  It does **not** reach all-decompositions — the product class is
still structured — so the open quantifier is not crossed.
-/

namespace PallLean.Paper93.DeepMath.PathB.ForcingFamily

variable {ι κ : Type*}

/-- **Product (tensor) of two forcing families.**  A decomposition of the combined structure picks one from
each factor; its boundary is the sum of the two component boundaries (independent structures), and the
threshold is the sum of the two thresholds. -/
def ForcingFamily.prod (F : ForcingFamily ι) (G : ForcingFamily κ) : ForcingFamily (ι × κ) where
  decompositions := F.decompositions ×ˢ G.decompositions
  nonempty := F.nonempty.product G.nonempty
  boundary := fun p => F.boundary p.1 + G.boundary p.2
  threshold := F.threshold + G.threshold
  forced := by
    intro p hp
    rw [Finset.mem_product] at hp
    exact Nat.add_le_add (F.forced p.1 hp.1) (G.forced p.2 hp.2)

/-- **Amplification: the product's `min` is at least the sum of the thresholds.**  Combining two
expander-forced structures amplifies the forced boundary additively. -/
theorem ForcingFamily.prod_threshold_le_min (F : ForcingFamily ι) (G : ForcingFamily κ) :
    F.threshold + G.threshold ≤ (F.prod G).minBoundary :=
  (F.prod G).threshold_le_min

end PallLean.Paper93.DeepMath.PathB.ForcingFamily

namespace PallLean.Paper93.DeepMath.PathB.ForcingFamilyAmplify

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.NecHard
open PallLean.Paper93.DeepMath.PathB.ObserverNeciporuk
open PallLean.Paper93.DeepMath.PathB.ForcingFamily

variable {b m : ℕ}

/-- **Amplification on the proved `hardF` family.**  Two independent copies of the `hardF` address-block
forcing family give `min ≥ 2·(2^b − 1)` — the threshold amplified two-fold (each factor's `2^b − 1` summed).
Iterating `k` copies amplifies to `k·(2^b − 1)`. -/
theorem hardF_prod_amplified (hm : 0 < m) (F G : BFormula (nn b m))
    (hF : ∀ x, BFormula.eval F x = hardF x) (hG : ∀ x, BFormula.eval G x = hardF x) :
    (Dsize b - 1) + (Dsize b - 1)
      ≤ ((hardFAddressFamily hm F hF).prod (hardFAddressFamily hm G hG)).minBoundary :=
  ForcingFamily.prod_threshold_le_min (hardFAddressFamily hm F hF) (hardFAddressFamily hm G hG)

end PallLean.Paper93.DeepMath.PathB.ForcingFamilyAmplify

#print axioms PallLean.Paper93.DeepMath.PathB.ForcingFamily.ForcingFamily.prod_threshold_le_min
#print axioms PallLean.Paper93.DeepMath.PathB.ForcingFamilyAmplify.hardF_prod_amplified
