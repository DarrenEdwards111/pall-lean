import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTimeBoundaryPrinciple

/-!
# Decision-holonomy: the precise missing target (named, with the gap to existing debt proved)

The arc has isolated the missing maths to a single shape.  The debt/holonomy invariants we proved measure
**distinguishability** (how many branches differ) — equivalently a lower bound on **action** `∑ 2^{B_τ}`.  But
deciding SAT can sometimes *avoid* resolving those distinctions (Gaussian elimination decides Tseitin without
servicing its proof debt in observer time).  The missing theorem must produce **decision-holonomy**: an
invariant that lower-bounds **decision time**, surviving such shortcuts.

This file makes that precise and proves the two honest facts around it:

* **The reduction (proved).**  A decision-holonomy bound — `decisionTime n ≥ threshold n` with `threshold`
  super-polynomial — implies the family is **not polynomially decidable**.  For an NP-complete family that is
  `P ≠ NP`.
* **The gap (proved).**  The existing debt is an **action** lower bound, and an action lower bound does **not**
  give a decision-time lower bound: a single-step (poly-time) trajectory can carry *arbitrarily large* action.
  So distinguishability/holonomy debt, as currently proved, cannot supply decision-holonomy.

## Proved (clean axioms, no `sorry`)

* `not_polyBounded_of_superPoly_le` — if `g ≤ f` pointwise and `g` is super-polynomial, then `f` is not
  polynomially bounded.
* `decisionHolonomy_implies_not_poly` — **the reduction**: `DecisionHolonomyHyp` (decision time `≥` a
  super-poly threshold) ⇒ decision time is not poly-bounded ⇒ the family `∉ P`.
* `distinguishability_debt_not_time_lower_bound` — **the gap**: for any debt `D`, there is a one-step
  (poly-time, `T = 1`) trajectory with action `≥ D`.  Action `≥ D` is achievable in poly time, so an action
  (distinguishability) lower bound gives **no** decision-time lower bound.

## Honest status — why this is the wall, not a step before it

`DecisionHolonomyHyp` for an NP-complete family is, by `decisionHolonomy_implies_not_poly`, **equivalent in
strength to `P ≠ NP`**: it is a super-poly *time* lower bound for an NP-complete problem.  Defining the
invariant does not prove it; the invariant *is* the separation.  The gap theorem shows precisely why the
machinery built so far is insufficient: it bounds **action** (capacity integrated over time), which a
high-boundary poly-time decider drives up for free — exactly the Tseitin / Gaussian-elimination escape.

So the missing new maths is sharply named: **an invariant `ι` of an NP-complete SAT family with
`decisionTime ≥ ι` and `ι` super-polynomial** — decision-holonomy.  It must use NP-complete structure to rule
out high-boundary shortcuts (option 1, a SAT time–space tradeoff) or be obtained via the algorithmic/Williams
route (option 2, with its named diagonalisation + decision-hardness inputs).  This file proves the reduction
and the gap; it does **not** prove `DecisionHolonomyHyp`, which would be `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DecisionHolonomy

open PallLean.Paper93.DeepMath.PathB.TimeBoundaryPrinciple

/-- A function is **polynomially bounded** if some fixed `n^k + k` dominates it. -/
def PolyBounded (f : ℕ → ℕ) : Prop := ∃ k, ∀ n, f n ≤ n ^ k + k

/-- A function is **super-polynomial** if it eventually exceeds every `n^k + k`. -/
def SuperPoly (g : ℕ → ℕ) : Prop := ∀ k, ∃ n, n ^ k + k < g n

/-- **A super-poly lower bound breaks poly-boundedness (proved).**  If `g ≤ f` pointwise and `g` is
super-polynomial, then `f` is not polynomially bounded. -/
theorem not_polyBounded_of_superPoly_le {f g : ℕ → ℕ} (hle : ∀ n, g n ≤ f n) (hg : SuperPoly g) :
    ¬ PolyBounded f := by
  rintro ⟨k, hk⟩
  obtain ⟨n, hn⟩ := hg k
  have hgf : g n ≤ n ^ k + k := le_trans (hle n) (hk n)
  omega

/-- **Decision-holonomy hypothesis** (the named target).  The decision time of the family is bounded below by
`threshold n` at every `n`.  With a super-polynomial `threshold` and an NP-complete family this is `P ≠ NP`.
*Not proved here.* -/
def DecisionHolonomyHyp (decisionTime threshold : ℕ → ℕ) : Prop := ∀ n, threshold n ≤ decisionTime n

/-- **The reduction (proved).**  A decision-holonomy bound with super-polynomial `threshold` forces the
decision time out of `P`: it is not polynomially bounded.  For an NP-complete family this is `P ≠ NP`. -/
theorem decisionHolonomy_implies_not_poly {decisionTime threshold : ℕ → ℕ}
    (hHol : DecisionHolonomyHyp decisionTime threshold) (hSP : SuperPoly threshold) :
    ¬ PolyBounded decisionTime :=
  not_polyBounded_of_superPoly_le hHol hSP

/-- **The gap (proved): action ⇏ decision time.**  For any debt/distinguishability value `D`, there is a
*single-step* trajectory (`T = 1`, poly time) whose action is at least `D`.  Hence an action (distinguishability,
holonomy-debt) lower bound of `D` does **not** imply a decision-time lower bound — a poly-time high-boundary
decider achieves large action for free.  This is exactly why the existing debt machinery cannot supply
decision-holonomy. -/
theorem distinguishability_debt_not_time_lower_bound (D : ℕ) :
    ∃ B : ℕ → ℕ, D ≤ action B 1 := by
  obtain ⟨B, hB⟩ := action_unbounded_by_time 1 D (le_refl 1)
  exact ⟨B, le_of_lt hB⟩

end PallLean.Paper93.DeepMath.PathB.DecisionHolonomy

#print axioms PallLean.Paper93.DeepMath.PathB.DecisionHolonomy.not_polyBounded_of_superPoly_le
#print axioms PallLean.Paper93.DeepMath.PathB.DecisionHolonomy.decisionHolonomy_implies_not_poly
#print axioms PallLean.Paper93.DeepMath.PathB.DecisionHolonomy.distinguishability_debt_not_time_lower_bound
