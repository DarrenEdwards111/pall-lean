import Mathlib.Data.Nat.Basic

/-!
# The shadow: the bounded observer verifies a lower-dimensional projection of the God's proof

Darren's refinement: when the expander's teeth slip, they don't lose *all* information — a **restricted**
bound survives, proportional to what the observer's thermodynamic interface can maintain.  Flatland: a 2D
being sees the 2D *shadow* of a 3D cube.  What it *can* see, the teeth bite into — so p-vs-np1 verifies the
**lower-dimensional shadow** of the God's infinite-dimensional proof.

This is right, and it is exactly a **projection** bound.  The catch is what a projection preserves — and
what it can never recover.

## The model

The God's full bound has dimension `fullDim` (the whole separation).  The observer's interface maintains
`interfaceDim` dimensions.  What it verifies is the **shadow** — the projection onto its interface,
`shadow = min interfaceDim fullDim`.

## What is proved

* **`teeth_bite_shadow`** — the shadow is a genuine part of the full bound: `shadow ≤ fullDim`.  The teeth
  really do bite into what the observer can see.
* **`shadow_verifiable`** — and the observer can hold it: `shadow ≤ interfaceDim` — it fits the interface.
* **`god_full_bound`** — infinite interface (`fullDim ≤ interfaceDim`) ⟹ `shadow = fullDim`: the God sees
  the whole proof.
* **`bounded_shadow_capped`** — a bounded interface (`interfaceDim ≤ fullDim`) ⟹ `shadow = interfaceDim`:
  the shadow is **capped at the interface dimension**, no matter how large the true bound.
* **`shadow_undetermines`** — the honest catch: two *different* full bounds cast the **same** shadow
  (`shadow ⟨big₁,d⟩ = shadow ⟨big₂,d⟩`).  A square shadow fits a cube *or* a cylinder — the shadow does
  not determine the object.

## Honest scope — a real partial bound, capped and non-determining

The shadow is genuinely verified, and genuinely proportional to the interface (Flatland is exact: the
observer sees a real projection, not nothing).  But two honest limits stand:

1. **Capped.**  `bounded_shadow_capped`: the verified shadow is at most `interfaceDim`.  A *polynomial*
   interface verifies a *polynomial* shadow — and SAT's full bound is superpolynomial, so the projection
   loses exactly the superpolynomial part.  The lost dimensions are `fullDim − interfaceDim` = the
   superpoly gap = `cost_super`.
2. **Non-determining.**  `shadow_undetermines`: the same shadow is cast by many full bounds.  Verifying the
   poly-shadow is consistent with the God's bound being superpoly (P ≠ NP) *or* only poly (P = NP) — like a
   2D being who cannot tell a cube from a cylinder.  So the shadow does not prove the full bound.

So the bounded observer really does verify the lower-dimensional shadow of the God's proof — a true,
partial, projected bound — but the shadow is capped at its interface and consistent with many higher-
dimensional truths.  Recovering the lost dimensions is `cost_super`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ShadowProjection

/-- A **shadow bound**: the God's full bound has dimension `fullDim`; the observer's interface maintains
`interfaceDim`.  The verified shadow is the projection `min interfaceDim fullDim`. -/
structure ShadowBound where
  /-- the God's full bound dimension (the whole separation) -/
  fullDim : ℕ
  /-- the dimensions the observer's thermodynamic interface maintains -/
  interfaceDim : ℕ

/-- The **shadow**: the projection of the full bound onto the observer's interface. -/
def shadow (S : ShadowBound) : ℕ := min S.interfaceDim S.fullDim

/-- **The teeth bite into a real part of the bound (proved).**  `shadow ≤ fullDim` — the projection is a
genuine portion of the God's full bound. -/
theorem teeth_bite_shadow (S : ShadowBound) : shadow S ≤ S.fullDim := by
  show min S.interfaceDim S.fullDim ≤ S.fullDim
  omega

/-- **The shadow fits the interface (proved).**  `shadow ≤ interfaceDim` — the observer can hold and verify
it. -/
theorem shadow_verifiable (S : ShadowBound) : shadow S ≤ S.interfaceDim := by
  show min S.interfaceDim S.fullDim ≤ S.interfaceDim
  omega

/-- **The God sees the whole proof (proved).**  An infinite interface (`fullDim ≤ interfaceDim`) gives
`shadow = fullDim` — no information lost. -/
theorem god_full_bound (S : ShadowBound) (hgod : S.fullDim ≤ S.interfaceDim) : shadow S = S.fullDim := by
  show min S.interfaceDim S.fullDim = S.fullDim
  omega

/-- **The bounded shadow is capped at the interface (proved).**  A bounded interface
(`interfaceDim ≤ fullDim`) gives `shadow = interfaceDim` — capped at the observer's dimension, no matter how
large the true bound.  The lost dimensions are `fullDim − interfaceDim`. -/
theorem bounded_shadow_capped (S : ShadowBound) (hb : S.interfaceDim ≤ S.fullDim) :
    shadow S = S.interfaceDim := by
  show min S.interfaceDim S.fullDim = S.interfaceDim
  omega

/-- **The shadow does not determine the object (proved).**  Two *different* full bounds `big₁, big₂` (both
above the interface `d`) cast the **same** shadow `d`.  A square shadow fits a cube or a cylinder — the
projection loses which higher-dimensional truth cast it. -/
theorem shadow_undetermines (d big1 big2 : ℕ) (h1 : d ≤ big1) (h2 : d ≤ big2) :
    shadow ⟨big1, d⟩ = shadow ⟨big2, d⟩ := by
  show min d big1 = min d big2
  omega

end PallLean.Paper93.DeepMath.PathB.ShadowProjection

#print axioms PallLean.Paper93.DeepMath.PathB.ShadowProjection.bounded_shadow_capped
#print axioms PallLean.Paper93.DeepMath.PathB.ShadowProjection.shadow_undetermines
