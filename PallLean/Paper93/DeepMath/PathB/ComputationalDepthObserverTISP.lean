import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBoundedBoundaryDebt
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderFoolingInstance

/-!
# The TISP framing of the boundary–time law — positioning against the SAT time–space literature

The classical SAT time–space line (Lipton–Viglas → Fortnow–Van Melkebeek → R. Williams) proves, for **general
machines**, `SAT ∉ TISP(n^{2cos(π/7)−ε}, n^{o(1)})` (`≈ n^{1.8019}` time, sub-polynomial space) — via
alternation-trading, a technique Buss–Williams proved **barriered** at that exponent.  This file states our
`bounded_boundary_tradeoff` in the same `TISP` language, so the comparison — and the two gaps — are explicit.

We define the **observer time–space class** `ObserverTISP P F T B`: the fooling-set-`P` instance is decidable
by a bounded-boundary observer using `≤ T` steps and boundary `≤ B` (a correct trajectory at servicing rate
`≤ 2^B`).  The boundary–time law gives a clean exclusion.

## Proved (clean axioms, no `sorry`)

* `not_observerTISP_of_large_fooling` — if `(T+1)·2^B < |P|` then the instance is **not** in
  `ObserverTISP P F T B`: a time–space *exclusion*, the bounded-boundary analogue of `SAT ∉ TISP(…)`.
* `hypercube_not_observerTISP` — concrete: the `2^n` hypercube witness is excluded from `ObserverTISP` whenever
  `(T+1)·2^B < 2^n`.  For `T = poly`, `B = o(n)` this holds, so it is excluded from
  `ObserverTISP(poly, o(n))` — **super-polynomial-time-strong** in this regime (far past the literature's
  `n^{1.8}`).

## Honest positioning — strength vs. the two restrictions

Our exclusion is *stronger in its regime* than the classical bound (it rules out `poly` time at `o(n)` boundary,
not just `n^{1.8}`), but it buys that with two restrictions the general results do not have — the same two gaps
as the rest of the programme:

1. **Observer model, not general machines.**  `ObserverTISP` is the bounded-boundary *observer* abstraction;
   the classical results handle arbitrary `TISP` machines.  Lifting to general machines is the open
   `CookLevinFrontierHyp` direction.
2. **Decision-easy instance.**  The hypercube/expander fooling instance is *proof*-hard but *decision*-easy
   (§ `tseitin_unsat_of_odd_charge`); the classical results are about SAT, which is *decision*-hard.

So the two lines are non-comparable and both far from `P ≠ NP`: ours is super-poly-but-restricted, theirs is
`n^{1.8}`-but-general-and-barriered.  Neither is a route to the separation; this file makes that precise in the
corpus rather than only in prose.  No `P ≠ NP` claim.
-/

namespace PallLean.Paper93.DeepMath.PathB.ObserverTISP

open PallLean.Paper93.DeepMath.PathB.BoundaryDebt
open scoped BigOperators

variable {X : Type*} [DecidableEq X]

/-- **The observer time–space class.**  The fooling-set-`P` instance (must-separate relation `F`) is in
`ObserverTISP P F T B` if some bounded-boundary observer decides it within time `T` and boundary `B`: an
initial view into `Fin (2^B)`, a debt sequence servicing at rate `≤ 2^B`, with all debt cleared by step `T`. -/
def ObserverTISP (P : Finset X) (F : Finset (X × X)) (T B : ℕ) : Prop :=
  ∃ (view0 : X → Fin (2 ^ B)) (debt : ℕ → ℕ),
    debt 0 = debtCount F view0 ∧ (∀ t, debt t ≤ debt (t + 1) + 2 ^ B) ∧ debt T = 0

/-- **Time–space exclusion (proved).**  A fooling-set-`P` instance with `(T+1)·2^B < |P|` is **not** in
`ObserverTISP P F T B` — the bounded-boundary analogue of `SAT ∉ TISP(T, 2^B)`.  Directly from
`bounded_boundary_tradeoff`. -/
theorem not_observerTISP_of_large_fooling (P : Finset X) (F : Finset (X × X))
    (hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ F) {T B : ℕ}
    (hbig : (T + 1) * 2 ^ B < P.card) :
    ¬ ObserverTISP P F T B := by
  rintro ⟨view0, debt, hinit, hservice, hcleared⟩
  have h := bounded_boundary_tradeoff P F hfool view0 debt T hinit hservice hcleared
  omega

/-- **Concrete (proved): the `2^n` witness is excluded from `ObserverTISP` below the budget.**  Whenever
`(T+1)·2^B < 2^n`, the hypercube fooling instance is not in `ObserverTISP T B`.  For `T = poly`, `B = o(n)`
this holds — so the instance is outside `ObserverTISP(poly, o(n))`: super-polynomial-time-strong for
sub-linear boundary, in the bounded-boundary observer model. -/
theorem hypercube_not_observerTISP {n T B : ℕ} (hTB : (T + 1) * 2 ^ B < 2 ^ n) :
    ¬ ObserverTISP (Finset.univ : Finset (Fin n → Bool)) (hypercubeFool n) T B := by
  apply not_observerTISP_of_large_fooling _ _ (hypercube_fool n)
  rw [hypercube_card]
  exact hTB

end PallLean.Paper93.DeepMath.PathB.ObserverTISP

#print axioms PallLean.Paper93.DeepMath.PathB.ObserverTISP.not_observerTISP_of_large_fooling
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverTISP.hypercube_not_observerTISP
