import Mathlib.Data.Nat.Basic

/-!
# Inferring the cube from the square: a heuristic guess, not a proof

Darren: we may see a square but *infer* the cube — we can always infer the full object from the shadow's
dimensionality; that heuristic is the missing piece.  The instinct is real — it is **inductive inference**
(Occam / Solomonoff / compression): guess the simplest full object consistent with the shadow.  But it lands
where the compression thread already did: a heuristic inference is a **guess**, not a **proof**, because the
projection is many-to-one — a square is cast by a cube *and* a cylinder.

## The obstruction

An inference is a function `infer : shadow → fullObject`.  For it to *reliably* recover the object it would
have to *invert* the projection.  But the projection collapses distinct objects to the same shadow
(`shadow_undetermines`: `big₁ ≠ big₂` cast the same shadow), and no function can map one shadow to two
different objects.  So **any** inference errs on some input — it picks one preimage and is wrong wherever the
truth is the other.

## What is proved

* **`projection_not_invertible`** — no inference maps a shadow to *both* objects sharing it: `¬(infer d = big₁
  ∧ infer d = big₂)` for `big₁ ≠ big₂`.
* **`any_inference_errs`** — hence any inference is wrong on at least one of the two: `infer d ≠ big₁ ∨
  infer d ≠ big₂`.  The heuristic is a guess; it cannot be reliable.
* **`inference_errs_concrete`** — concretely, any `infer` has `infer 5 ≠ 10 ∨ infer 5 ≠ 20`.

## Honest scope — the guess is right on structure, wrong on the hard core

The "infer the cube" heuristic is genuinely useful — it is how minds and LMs work: guess the simplest object
consistent with what you see.  On **structured** inputs (the object really is the simple one) the guess is
right.  But it is a *guess*: on **adversarial** inputs (a cylinder casting the same square) it is wrong, and
`any_inference_errs` proves no inference avoids this — because a *reliable* inference would make the shadow
*determine* the object, contradicting `shadow_undetermines`.

This is the compression thread once more: the heuristic works exactly where the instance is compressible
(structured), and the hard core is the incompressible one where the inference is underdetermined.  And for a
*proof*: a heuristic guess of the proof is not a proof — you would still have to *verify* it
(`VerifyFindGap`), and the valid, non-natural, high-effective-dimension object is exactly the one *not*
recoverable from the poly shadow (`FullProjection`).  So the inference is a real inductive tool, not the
missing piece: it guesses, it does not prove, and it guesses wrong precisely on the hard core = `cost_super`.
This file certifies neither `P ≠ NP` nor its unprovability.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.InferenceUnderdetermined

/-- **The projection is not invertible (proved).**  No inference `infer : shadow → object` can map a single
shadow `d` to *both* distinct objects `big₁, big₂` that cast it: `¬(infer d = big₁ ∧ infer d = big₂)`. -/
theorem projection_not_invertible (infer : ℕ → ℕ) (d big1 big2 : ℕ) (hne : big1 ≠ big2) :
    ¬ (infer d = big1 ∧ infer d = big2) := by
  intro h
  exact hne (h.1.symm.trans h.2)

/-- **Any inference errs on some input (proved).**  Since two distinct objects cast the same shadow, an
inference picks at most one: `infer d ≠ big₁ ∨ infer d ≠ big₂`.  The heuristic is a guess, not a reliable
recovery. -/
theorem any_inference_errs (infer : ℕ → ℕ) (d big1 big2 : ℕ) (hne : big1 ≠ big2) :
    infer d ≠ big1 ∨ infer d ≠ big2 := by
  by_cases hb1 : infer d = big1
  · right
    intro hb2
    exact hne (hb1.symm.trans hb2)
  · left
    exact hb1

/-- **Concrete (proved).**  Any inference is wrong on one of two objects sharing a shadow:
`infer 5 ≠ 10 ∨ infer 5 ≠ 20`. -/
theorem inference_errs_concrete (infer : ℕ → ℕ) : infer 5 ≠ 10 ∨ infer 5 ≠ 20 :=
  any_inference_errs infer 5 10 20 (by decide)

end PallLean.Paper93.DeepMath.PathB.InferenceUnderdetermined

#print axioms PallLean.Paper93.DeepMath.PathB.InferenceUnderdetermined.projection_not_invertible
#print axioms PallLean.Paper93.DeepMath.PathB.InferenceUnderdetermined.any_inference_errs
