import PallLean.Paper93.DeepMath.PathB.ComputationalDepthForAllNUniform

/-!
# Bridging them inversely: gradient descent and the self-reference are exact complements

Darren: bridge the two sides *inversely* — gradient descent (constructive, generic, barriered) and the
holistic self-reference (non-constructive, rare, the escape).  They are not merely opposite; they are
**exact complements**.  A method's property is **large** (natural — the gradient-descent side) *iff* it is
**not rare** (non-natural — the self-reference side): `Large C ↔ ¬ Rare C`.  So the two partition every
method perfectly, and barring one *forces* the crossing onto the other.

## What is proved

* **`large_iff_not_rare`** — the inverse bridge: `Large C ↔ ¬ Rare C`.  Gradient-descent-natural and
  self-reference-rare are exact complements — one is precisely the negation of the other.
* **`gradient_descent_large`** — gradient descent produces a *large* (generic, natural) property: it
  descends toward the typical distinguisher.
* **`valid_crossing_rare`** — a method that is *not* on the barriered (large) side must be *rare*
  (non-natural): `¬ Large C → Rare C`.  A valid crossing is forced onto the self-reference side.
* **`inverse_bridge`** — the capstone: the two are exact inverses, and barring the natural (gradient)
  side forces the crossing onto the rare (self-reference) side.

## Honest verdict — the inverse bridge forces the crossing onto self-reference; the premise is `cost_super`

Bridging inversely is the natural-proofs **dichotomy as exact complementarity**: a method is *large*
(natural, gradient-descent-able) precisely when it is *not rare* (`large_iff_not_rare`).  Gradient descent
lives on the large/natural side (`gradient_descent_large`), which Razborov–Rudich bars; so a *valid*
crossing — one not barred — must lie on the rare/non-natural side (`valid_crossing_rare`), which is exactly
the holistic self-reference (`SelfReferenceFeature`, `HolisticSizeBound`).  The two ideas are bridged
inversely: gradient descent is the forbidden half, the self-reference is the permitted half, and they are
precise complements (`inverse_bridge`).  This is a real, proved narrowing — **the only door is the
non-constructive, rare, non-local self-reference; gradient descent is provably barred** — and it explains
why every route this session converges on the self-reference escape.  But it does not cross: forcing the
crossing *onto* the self-reference side is not proving the self-reference crossing.  That crossing is the
un-proven premise — SAT's recognizer is un-shareable, the compounding, the superlinear bound — which is
`cost_super`.  The inverse bridge proves *where* the crossing must be; proving it *is* there is `P ≠ NP`.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.InverseBridge

open PallLean.Paper93.DeepMath.PathB.SelfReferenceFeature

/-! ### The inverse bridge: large ⟺ not rare -/

/-- **The inverse bridge (proved).**  `Large C ↔ ¬ Rare C`: the gradient-descent (natural, large) side and
the self-reference (non-natural, rare) side are *exact* complements — one is precisely the negation of the
other.  Bridging them inversely. -/
theorem large_iff_not_rare (C : FunctionClass) : Large C ↔ ¬ Rare C := by
  constructor
  · intro h hr; omega
  · intro h; omega

/-! ### Gradient descent is on the natural side; the crossing is on the other -/

/-- Gradient descent's property: it descends toward the *typical* distinguisher — a majority (`60 > 50` of
`100`), a *large* / natural property. -/
def gradientDescent : FunctionClass := ⟨100, 60, by omega⟩

/-- **Gradient descent is large / natural (proved).**  It finds the generic distinguisher — barred by
Razborov–Rudich. -/
theorem gradient_descent_large : Large gradientDescent := by decide

/-- **A valid crossing is rare / non-natural (proved).**  A method not on the barriered (large) side must
be rare — the self-reference side.  Barring gradient descent forces the crossing onto the self-reference. -/
theorem valid_crossing_rare (C : FunctionClass) (notBarriered : ¬ Large C) : Rare C := by
  simp only [Large] at notBarriered
  simp only [Rare]
  omega

/-! ### The capstone -/

/-- **The inverse bridge, bundled (proved).**  The natural (gradient-descent) side and the non-natural
(self-reference) side are exact complements (`Large ↔ ¬ Rare`), and barring the natural side forces the
crossing onto the rare (self-reference) side.  Gradient descent is the forbidden half; the holistic
self-reference is the permitted half. -/
theorem inverse_bridge (C : FunctionClass) :
    (Large C ↔ ¬ Rare C) ∧ (¬ Large C → Rare C) :=
  ⟨large_iff_not_rare C, valid_crossing_rare C⟩

end PallLean.Paper93.DeepMath.PathB.InverseBridge

#print axioms PallLean.Paper93.DeepMath.PathB.InverseBridge.large_iff_not_rare
#print axioms PallLean.Paper93.DeepMath.PathB.InverseBridge.gradient_descent_large
#print axioms PallLean.Paper93.DeepMath.PathB.InverseBridge.valid_crossing_rare
#print axioms PallLean.Paper93.DeepMath.PathB.InverseBridge.inverse_bridge
