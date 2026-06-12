import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBoundedLocalityNonCollapse

/-!
# Refinement monotonicity — why a debt‑conservation law cannot, by itself, defeat the high‑boundary escape

HAL's tri‑aspect / N‑frame proposal hopes for a **conservation law**: refinement lowers merge‑debt but raises
"raveling/holonomy debt," so total action is bounded below and the high‑boundary escape pays elsewhere.  The
decisive question is the *direction* in which concrete debts move under refinement.  This file proves the merge
(distinguishability) debt is **monotone non‑increasing under refinement** — it goes *down*, never up.

## Proved (clean axioms, no `sorry`)

* `refinement_reduces_debt` — if `refined` is a refinement of `orig` (it separates at least as much: whenever
  `refined` merges a pair, so does `orig`), then `debtCount F refined ≤ debtCount F orig`.  A finer observer
  carries *less* distinguishability debt.  (Immediate from `debtCount_mono`.)

## What this says about the conservation route

Every concrete *distinguishability‑type* debt moves the same way as merge‑debt under refinement — **downward**:

* merge‑debt: ↓ (proved here);
* holonomy/twist debt (`holonomy_forces_debt_card`): pairs twisted *and merged* — a finer view merges fewer, so ↓;
* dimension gap `d_res − d_obs` (`…ObserverDimensionGap`): refinement *raises* `d_obs`, so the gap ↓;
* local→global / marginal‑gluing debt: a larger boundary sees larger marginals, which glue more easily, so ↓.

So for these terms the conservation **sum decreases** under refinement — it is *not* conserved, and the
brute‑force escape (refine to full boundary ⇒ all such debts `→ 0`, `hypercube_brute_force_escape`) goes
through.  A conservation law that defeats refinement therefore **requires a term that strictly *increases* with
boundary.**  The only such quantity is the **cost of computing/maintaining the refined states** — the view's
own computational complexity (which the abstraction omits: views are free functions).  And that term being
super‑polynomial for SAT *is* the separator/decision lower bound `= P ≠ NP`.

## Honest verdict (the answer to "does the conservation idea defeat refinement?")

**Not by itself.**  Made concrete, the conservation law conserves distinguishability‑type debts, all of which
*fall* under refinement, so their total is reducible to zero by buying boundary — exactly the escape.  To
defeat refinement the law must include a **refinement‑increasing computation‑cost term**, and bounding that
term below super‑poly for SAT is the wall (a decision‑hard separator lower bound), not a consequence of the
conservation structure.  So the tri‑aspect/N‑frame conservation gives the *right architecture* — debt as a
gluing defect, action as its cost — but the load‑bearing inequality is the same unproven separator bound.  Not
circular here (the monotonicity is a real theorem); not a proof of the separation.
-/

namespace PallLean.Paper93.DeepMath.PathB.RefinementMonotone

open PallLean.Paper93.DeepMath.PathB.BoundaryDebt

variable {X : Type*}

/-- **Refinement reduces merge‑debt (proved).**  If `refined` is a refinement of `orig` — it separates at least
as much, i.e. whenever `refined` assigns two continuations the same state, so does `orig` (`hrefine`) — then the
refined observer carries no more distinguishability debt: `debtCount F refined ≤ debtCount F orig`.  Buying a
finer boundary can only *lower* this debt. -/
theorem refinement_reduces_debt {S T : Type*} [DecidableEq S] [DecidableEq T]
    (F : Finset (X × X)) (refined : X → S) (orig : X → T)
    (hrefine : ∀ x y, refined x = refined y → orig x = orig y) :
    debtCount F refined ≤ debtCount F orig :=
  debtCount_mono F refined orig hrefine

end PallLean.Paper93.DeepMath.PathB.RefinementMonotone

#print axioms PallLean.Paper93.DeepMath.PathB.RefinementMonotone.refinement_reduces_debt
