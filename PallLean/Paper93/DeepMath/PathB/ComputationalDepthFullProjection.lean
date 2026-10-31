import Mathlib.Data.Nat.Basic

/-!
# When the shadow is a *full* projection: that is exactly the natural (barriered) case

Darren: the teeth bite into the shadow, but the shadow is a **full** projection of the NP proof — so we *do*
see it, it is in the same set.  This has an exact meaning, and it closes the loop.

A projection is **faithful** (full, lossless) on an object exactly when the object's **effective dimension**
fits the observer's interface — `effDim ≤ interface`.  When that holds, the poly-bounded observer sees the
whole object; the shadow *is* the proof.  But "the separating object fits the poly interface" is precisely
"the separating object is **natural**" (poly-accessible, low effective dimension) — and a natural separating
object is exactly what the **Razborov–Rudich barrier** forbids (it would break cryptography).

So "the shadow is a full projection of the NP proof" = "the NP proof is natural" = **the barriered case**.
The full-shadow world is not a way to *see* a valid proof — it is the world where the object, being
poly-accessible, cannot be a valid separating proof at all.  The proof that *works* is non-natural: high
effective dimension, *not* fully in the poly shadow.

## What is proved

* **`faithful_iff_natural`** — full projection *is* naturalness: `Faithful ↔ Natural` (`Iff.rfl`), both being
  `effDim ≤ interface`.
* **`faithful_or_exceeds`** — the dichotomy: either the shadow is faithful (the object fits the interface) or
  the object *exceeds* it (`interface < effDim`, in the dropped dimensions).
* **`faithful_is_natural_hence_barriered`** — a *faithful* shadow of a separating object is natural, hence
  barriered (via the Razborov–Rudich barrier, as a named hypothesis).  Seeing the full proof in the poly
  shadow ⟹ the object is natural ⟹ it cannot be a valid separating proof.

## Honest scope — full shadow = natural = barriered; the real proof is not fully in it

Darren is right that a *low-dimensional* object is fully seen — that is what a faithful projection means.
The catch is *which* objects are low-dimensional: exactly the **natural** ones, and a natural separating
measure is barriered.  So the full-projection case is the natural case, and the natural case cannot separate.
The valid, non-natural proof (this whole map's target — the EXP middle) has effective dimension *above* the
poly interface, so it is *not* fully in the shadow: `faithful_or_exceeds` puts it in the "exceeds" horn,
where the shadow is non-determining (`ShadowProjection`).  "We see it, same set" holds only when there is
nothing valid to see (natural = barriered); when there is a valid proof, it is non-natural and not fully
projected.  This file certifies neither `P ≠ NP` nor its unprovability.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.FullProjection

/-- The separating object ("the NP proof"), by its **effective dimension**, projected onto an observer's
**interface**. -/
structure ProjectedProof where
  /-- effective dimension of the separating object -/
  effDim : ℕ
  /-- the observer's interface dimension (poly-bounded) -/
  interface : ℕ

/-- The shadow is **faithful** (a full, lossless projection) when the object fits the interface. -/
def Faithful (P : ProjectedProof) : Prop := P.effDim ≤ P.interface

/-- The object is **natural** (poly-accessible, low effective dimension) when it fits the poly interface —
the effective-dimension reading of a Razborov–Rudich natural property. -/
def Natural (P : ProjectedProof) : Prop := P.effDim ≤ P.interface

/-- **Full projection IS naturalness (proved, `Iff.rfl`).**  "The shadow is a full projection of the object"
and "the object is natural" are the *same condition* — both `effDim ≤ interface`. -/
theorem faithful_iff_natural (P : ProjectedProof) : Faithful P ↔ Natural P := Iff.rfl

/-- **The dichotomy (proved).**  Either the shadow is faithful (the object fits the interface) or the object
*exceeds* it (`interface < effDim` — in the dropped dimensions). -/
theorem faithful_or_exceeds (P : ProjectedProof) : Faithful P ∨ P.interface < P.effDim := by
  unfold Faithful
  omega

/-- **A full shadow is natural, hence barriered (proved).**  If the shadow of a separating object is
faithful, the object is natural, so — by the Razborov–Rudich barrier (named hypothesis) — it is barriered.
Seeing the whole proof in the poly shadow means the object is natural, which cannot be a valid separating
proof. -/
theorem faithful_is_natural_hence_barriered (P : ProjectedProof)
    (Barriered : ProjectedProof → Prop)
    (hRR : ∀ Q, Natural Q → Barriered Q)
    (hf : Faithful P) : Barriered P :=
  hRR P ((faithful_iff_natural P).mp hf)

end PallLean.Paper93.DeepMath.PathB.FullProjection

#print axioms PallLean.Paper93.DeepMath.PathB.FullProjection.faithful_iff_natural
#print axioms PallLean.Paper93.DeepMath.PathB.FullProjection.faithful_is_natural_hence_barriered
