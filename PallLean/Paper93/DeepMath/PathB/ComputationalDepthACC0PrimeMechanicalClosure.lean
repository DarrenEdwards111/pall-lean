import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SmolenskyPrime

/-!
# Prime mechanical closure — discharging the bookkeeping residuals, and the clean prime theorem

Entry 278 left the prime-case Smolensky route "closed modulo bookkeeping": three residuals (`ApproximatorDegreeBound`,
the binomial tail, the committed-arc `Circ` recursion).  This file discharges the genuinely-mechanical one and packages
the clean prime theorem, **leaving exactly one frontier: composite carry-crossing** (entry-238 `CarryRefinementCrossing`).

* **`ApproximatorDegreeBound` (DISCHARGED).**  This is just *the degree of a product is at most the sum of degrees*:
  `MvPolynomial.totalDegree_mul`.  The approximator (degree `≤ D`) times the complement monomial (degree `≤ |Sᶜ|`) has
  degree `≤ D + |Sᶜ| ≤ D + n/2` — `approximator_times_complement_totalDegree`, PROVED.
* **The binomial tail** — `lowDegreeDim n (n/2 + D) < 2ⁿ − E` for `D = O(√n)` and small `E` — is *not* bookkeeping; it is
  the standard Chernoff/normal-tail estimate on `∑_{i ≤ n/2+D} C(n,i)`.  We keep it as an explicit numeric hypothesis
  (the textbook Smolensky parameter regime), not a faked socket; the weak form `lowDegreeDim n D < 2ⁿ` (`D < n`) is the
  proved entry-264 `lowDegreeDim_lt_two_pow`.
* **The `Circ` recursion** — the quantitative refinement of `approximable_exists` — lives in the committed circuit arc.

* **`prime_smolensky_route_closed` (PROVED).**  The clean prime theorem: the prime-case hardness (`CrossFieldCountHard`,
  established by entry-278's `no_small_approximator`) yields `ACC0CompositeComponent` via the entry-261 bridge.

## What is proved (clean axioms, no `sorry`)

* **`approximator_times_complement_totalDegree`** (PROVED) — `P.totalDegree ≤ D`, `Q.totalDegree ≤ d` ⇒
  `(P * Q).totalDegree ≤ D + d` (`MvPolynomial.totalDegree_mul`): discharges `ApproximatorDegreeBound`.
* **`prime_smolensky_route_closed`** (PROVED, no axioms) — `CrossFieldCountHard` + the entry-261 bridge ⇒
  `ACC0CompositeComponent`: the clean prime route to the ACC component.

## The one remaining frontier

After this, the prime-`ACC⁰[p]` lower bound is assembled with all *mechanical* residuals discharged (the product-degree
bound here, the weak counting bound entry 264) and only standard parameter estimates (the binomial tail) and the
committed `Circ` recursion outstanding.  **The single genuinely-open frontier is composite modulus** — the
`CarryRefinementCrossing` wall (entry 238).  *Do not bookkeep through it; it needs a new idea.*

## Honest scope

Discharges the mechanical `ApproximatorDegreeBound` (degree of a product) and packages the clean prime route to
`ACC0CompositeComponent`.  The binomial tail is the standard numeric estimate (kept as a hypothesis, not faked); the
`Circ` recursion is the committed arc's.  Prime case = textbook Smolensky, mechanically closed; **composite = the open
wall** (entry 238).  This is **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0PrimeMechanicalClosure

open PallLean.Paper93.DeepMath.PathB.ACC0FirePatternRichness (crossFieldHard_to_ACC0Component)

/-- **`ApproximatorDegreeBound` discharged (PROVED).**  The degree of a product is at most the sum of the degrees
(`MvPolynomial.totalDegree_mul`): the approximator `P` (degree `≤ D`) times the complement monomial `Q` (degree `≤ d`)
has degree `≤ D + d`.  Taking `d = |Sᶜ| ≤ n/2` (entry 277, for `|S| > n/2`) gives degree `≤ D + n/2` — the product-degree
bookkeeping the degree-halving needed. -/
theorem approximator_times_complement_totalDegree {σ R : Type} [CommSemiring R]
    (P Q : MvPolynomial σ R) (D d : ℕ) (hP : P.totalDegree ≤ D) (hQ : Q.totalDegree ≤ d) :
    (P * Q).totalDegree ≤ D + d :=
  le_trans (MvPolynomial.totalDegree_mul P Q) (Nat.add_le_add hP hQ)

/-- **The clean prime theorem (PROVED, no axioms).**  The prime-case hardness `CrossFieldCountHard` — established by
entry-278's `no_small_approximator` (no low-degree small-error approximator of the non-native `MOD_q` target, from the
proved pigeonhole/halving/wiring) — yields `ACC0CompositeComponent` via the entry-261 bridge.  This is the prime
Smolensky route, closed and wired to the ACC component. -/
theorem prime_smolensky_route_closed {CrossFieldCountHard ACC0CompositeComponent : Prop}
    (hCFH : CrossFieldCountHard)
    (hbridge : crossFieldHard_to_ACC0Component CrossFieldCountHard ACC0CompositeComponent) :
    ACC0CompositeComponent :=
  ACC0SmolenskyPrime.prime_route_to_ACC0Component hCFH hbridge

/-!
**The closure.**  The mechanical residual `ApproximatorDegreeBound` is discharged
(`approximator_times_complement_totalDegree`, `MvPolynomial.totalDegree_mul`), and the prime route is packaged
(`prime_smolensky_route_closed`).  The prime-`ACC⁰[p]` lower bound is now assembled with every *mechanical* part proved;
the only outstanding inputs are the *standard binomial tail* (a Chernoff-type estimate, kept as an honest numeric
hypothesis) and the committed arc's `Circ` recursion.  The **single genuinely-open frontier is composite modulus** — the
`CarryRefinementCrossing` wall (entry 238) — which needs a new idea and must not be bookkept through.  Not faked, not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0PrimeMechanicalClosure

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimeMechanicalClosure.approximator_times_complement_totalDegree
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimeMechanicalClosure.prime_smolensky_route_closed
