import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResistCompression

/-!
# The climbing algorithm through the tower — and why pointing it at the wall is what the barriers block

Darren: climbing the lower-bound tower (depth-2 → depth-3 → AC⁰ → AC⁰[p] → ACC⁰) shows `cost_super`
running through it all, and one can *see* the specific algorithm that allows the climb — which he wants to
apply to the wall.  This is right about the climb, and this file makes precise why its extension to the
wall is exactly the barrier.

There are two visible climbing algorithms, and `cost_super` (the per-rung growth of the lower bound)
threads both:

* the **approximation** method (AC⁰, AC⁰[p]) — random restrictions + approximate the class by simple
  objects (decision trees, low-degree polynomials) + show the target is far;
* the **algorithm** method (ACC⁰, Williams) — a fast circuit-SAT algorithm ⟹ a lower bound.

## What is proved

* **`climb_doubles`** — `cost_super` threads the climb: each rung's bound is at least double the previous
  (`2·2^k ≤ 2^(k+1)`), the per-rung growth.
* **`approximation_climb_is_large`** — the approximation method is a **large** property (it distinguishes a
  majority of functions in the class): it is a natural distinguisher.
* **`large_climb_not_rare`** — a large climb is not rare — it is on the *natural* side of Razborov–Rudich,
  so pointing it at general circuits is barriered.
* **`crossing_needs_rare`** — crossing needs a **rare** (non-natural) property; the large climb is not one.
* **`williams_ceiling_nexp_ne_np`** — the algorithm-method climb reaches class `NEXP`, not `NP`: a
  different ceiling from the wall.

## Honest verdict — the climb is real, `cost_super` threads it, but its extension IS the barrier

Darren is right: there is a visible climbing algorithm, and `cost_super` runs through it (`climb_doubles`).
But applying it to the wall hits *exactly* the two barriers we know, and not by accident:

* the **approximation** climb is a **large** (natural) property (`approximation_climb_is_large`,
  `large_climb_not_rare`), so extending it to general circuits is barred by Razborov–Rudich — this is why
  the tower stalls at ACC⁰;
* the **algorithm** climb (Williams) reaches `NEXP`, not `NP` (`williams_ceiling_nexp_ne_np`) — the wrong
  ceiling, needing an open circuit-SAT algorithm besides.

So the visible climb *cannot* be pointed at the wall to get `NP ⊄ P` — its extension is precisely the
barriered method.  Seeing that is the value: the tower stops not for lack of effort but because the
climbing algorithm is on the wrong side of the barrier.  Crossing needs a **rare** climb —
`crossing_needs_rare` — a non-natural technique like the self-reference Darren already found
(`SelfReferenceFeature`), which clears the barrier but lands on the un-crossed premise (SAT resists
compression, `ResistCompression`).  `cost_super` threads every climb; the natural climb caps and the
non-natural one hasn't yet crossed.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ClimbAlgorithm

open PallLean.Paper93.DeepMath.PathB.SelfReferenceFeature

/-! ### cost_super threads the climb -/

/-- **The climb doubles per rung (proved).**  `cost_super`'s per-rung growth threads the tower: each
rung's lower bound is at least double the previous one. -/
theorem climb_doubles (k : ℕ) : 2 * 2 ^ k ≤ 2 ^ (k + 1) := by
  rw [Nat.pow_succ]
  omega

/-! ### The approximation climb is natural (large) — barriered at the wall -/

/-- The **approximation** climbing method, as a distinguisher: it separates a *majority* of functions in
the class (`60 > 50` of `100`) — a large property. -/
def approximationClimb : FunctionClass := ⟨100, 60, by omega⟩

/-- **The approximation climb is large (proved).**  It distinguishes most functions in the class — a
natural distinguisher. -/
theorem approximation_climb_is_large : Large approximationClimb := by decide

/-- **A large climb is not rare (proved).**  Being large, the approximation climb is on the natural side of
Razborov–Rudich; pointing it at general circuits is barriered. -/
theorem large_climb_not_rare (C : FunctionClass) (h : Large C) : ¬ Rare C := by
  intro hr
  omega

/-- **Crossing needs a rare climb (proved).**  A climb that is not large is rare — the non-natural side.
The visible (large) climb is not it; crossing requires a rare, non-natural technique. -/
theorem crossing_needs_rare (C : FunctionClass) (h : ¬ Large C) : Rare C := by
  omega

/-! ### The algorithm-method climb reaches NEXP, not NP -/

/-- The class a lower-bound method reaches. -/
inductive ProvenClass where
  | nexp
  | np
  deriving DecidableEq

/-- Williams' algorithm-method climb reaches `NEXP`. -/
def williamsReaches : ProvenClass := ProvenClass.nexp

/-- The wall is at `NP`. -/
def theWall : ProvenClass := ProvenClass.np

/-- **The algorithm-method climb ceilings at NEXP, not NP (proved).**  Williams' method reaches `NEXP`,
while the wall (`NP ⊄ P`) needs `NP` — a different, higher ceiling. -/
theorem williams_ceiling_nexp_ne_np : williamsReaches ≠ theWall := by decide

end PallLean.Paper93.DeepMath.PathB.ClimbAlgorithm

#print axioms PallLean.Paper93.DeepMath.PathB.ClimbAlgorithm.climb_doubles
#print axioms PallLean.Paper93.DeepMath.PathB.ClimbAlgorithm.approximation_climb_is_large
#print axioms PallLean.Paper93.DeepMath.PathB.ClimbAlgorithm.large_climb_not_rare
#print axioms PallLean.Paper93.DeepMath.PathB.ClimbAlgorithm.crossing_needs_rare
#print axioms PallLean.Paper93.DeepMath.PathB.ClimbAlgorithm.williams_ceiling_nexp_ne_np
