import Mathlib.Data.Nat.Basic

/-!
# Reliable inference given the dimensionality — but the dimensionality is the answer

Darren: a reliable "always infer" *is* possible once you map the **dimensionality** the NP circuit comes
from — modeling how the God observer perceives it from its thermodynamic constraint — so it can be proved
with certainty.

The conditional is **correct**: given the source object's dimension, the projection *can* be inverted
reliably (this is tomography / determining modes / a faithful embedding of known dimension — with enough
side information the shadow does determine the object).  The catch is *what that side information is*: the
dimensionality of the NP circuit's hardness **is** the separating object — it **is** `cost_super`.  So a
reliable recovery does not *derive* the answer; it *takes it as input*.  This is the gauge circularity
again (`GaugeCircularity`): the recovery presupposes exactly the object it claims to find.

## What is proved

* **`recover_reliable`** — given the dimension `dim`, recovery is exact: `recover shadow dim = dim`.  With
  the dimensionality in hand, the inference is certain — Darren's conditional, confirmed.
* **`recover_ignores_shadow`** — but recovery uses *only* the supplied dimension, not the shadow:
  `recover s₁ dim = recover s₂ dim`.  The certainty comes entirely from the given `dim`; the shadow
  contributes nothing.  It is not inference *from the shadow* — it is returning the answer you fed it.
* **`certainty_tracks_the_input`** — feed a different object, get it back: `recover shadow O = O` and
  `recover shadow (O+1) = O+1`.  The output echoes the supplied dimension — so `recover` determines nothing
  on its own; you must already know `O`.

## Honest scope — certainty given the answer, not a derivation of it

So reliable inference *is* possible with the dimensionality — and the dimensionality of the NP circuit's
hardness is exactly the separating object, `cost_super`.  `recover_ignores_shadow` and
`certainty_tracks_the_input` show the "certainty" is supplied by the input, not extracted from the shadow:
the recovery echoes whatever object you give it.  Two ways to obtain the dimensionality, both blocked:

* **Compute/instantiate it** — that is accessing the superpolynomial object directly, which the poly
  observer cannot (`QuantifyNotInstantiate`); and multiple shadows (tomography) reconstruct a `D`-dimensional
  object only from `~D` projections — superpoly object, superpoly data.
* **Model the God's perception** — the God is infinite-dimensional; a bounded budget can *quantify* over that
  (`∀`, names it) but not *fix its value* — quantifying does not tell you *which* object it is.

So it can be inferred with certainty *given* the dimensionality, and obtaining the dimensionality is
`cost_super`.  Reliable recovery presupposes the answer — it does not prove it.  This is the same
presupposition as the gauge and the AdS curvature.  This file certifies neither `P ≠ NP` nor its
unprovability.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DimensionCircular

/-- Recovery of the object from a `shadow` *given* its source `dim`ensionality.  With the dimension supplied,
it returns it. -/
def recover (_shadow dim : ℕ) : ℕ := dim

/-- **Reliable given the dimension (proved).**  Supplied the source dimension, recovery is exact:
`recover shadow dim = dim`.  Darren's conditional — with the dimensionality, the inference is certain. -/
theorem recover_reliable (shadow dim : ℕ) : recover shadow dim = dim := rfl

/-- **But recovery ignores the shadow (proved).**  It uses *only* the supplied dimension:
`recover s₁ dim = recover s₂ dim`.  The certainty comes from the given `dim`, not from the shadow — it is not
inference *from the shadow*, it is returning the answer you fed it. -/
theorem recover_ignores_shadow (s1 s2 dim : ℕ) : recover s1 dim = recover s2 dim := rfl

/-- **The certainty tracks the input, not the shadow (proved).**  Feed a different object, get it back:
`recover shadow O = O` and `recover shadow (O+1) = O+1`.  The output echoes the supplied dimension — so
`recover` determines nothing on its own; you must already know the object `O`. -/
theorem certainty_tracks_the_input (shadow O : ℕ) :
    recover shadow O = O ∧ recover shadow (O + 1) = O + 1 :=
  ⟨rfl, rfl⟩

end PallLean.Paper93.DeepMath.PathB.DimensionCircular

#print axioms PallLean.Paper93.DeepMath.PathB.DimensionCircular.recover_reliable
#print axioms PallLean.Paper93.DeepMath.PathB.DimensionCircular.certainty_tracks_the_input
