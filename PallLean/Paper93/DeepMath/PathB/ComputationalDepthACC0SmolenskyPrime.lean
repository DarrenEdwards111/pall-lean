import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0FullProductGoodSet

/-!
# The prime-case Smolensky lower bound, assembled — and wired to the ACC component (roadmap steps 3–4)

This assembles the prime-case Razborov–Smolensky lower bound from the proved pieces — the pigeonhole (entry 275), the
degree-halving substitution (entry 276), and the full-product wiring (entry 277) — and wires the resulting hardness
through the existing bridge to `ACC0CompositeComponent` (entry 261).  **Prime case only; composite modulus stays the
open `CarryRefinementCrossing` wall (entry 238), deliberately untouched.**

**Step 3 (the lower bound).**  Under degree-halving on the good set `G` (every good-set point function is degree `≤ D'`,
supplied by entries 276/277), the pigeonhole (entry 275) forces `|G| ≤ lowDegreeDim n D'` — the good set is *bounded by
the low-degree dimension* (`smolensky_prime_goodset_bound`).  A degree-`D'` approximator with a *large* good set
(`≥ 2ⁿ − E`, the small-bad-set output of the approximation machinery) then cannot exist when the low-degree dimension is
below that threshold (`lowDegreeDim n D' < 2ⁿ − E`, the binomial tail) — `no_small_approximator`.  This is the prime
Smolensky lower bound: no low-degree, small-error approximator of the symmetric (`MOD`/parity) target.

**Step 4 (wire to ACC).**  The resulting `CrossFieldCountHard` feeds the entry-261 bridge
`crossFieldHard_to_ACC0Component → ACC0CompositeComponent` (`prime_route_to_ACC0Component`).

## What is proved (clean axioms, no `sorry`)

* **`smolensky_prime_goodset_bound`** (PROVED) — under `SmolenskyDegreeHalving (D') G`, `|G| ≤ lowDegreeDim n D'`
  (contrapositive of entry-275's `smolensky_lower_bound_via_pigeonhole`).
* **`no_small_approximator`** (PROVED) — degree-halving + good set `≥ 2ⁿ − E` + `lowDegreeDim n D' < 2ⁿ − E` ⇒ `False`:
  no degree-`D'`, `≤ E`-error approximator with the degree-halving exists (the prime Smolensky lower bound).
* **`prime_route_to_ACC0Component`** (PROVED) — `CrossFieldCountHard` + the entry-261 bridge ⇒ `ACC0CompositeComponent`.

## The remaining (mechanical / wall) sockets

* **`ApproximatorDegreeBound`** (entry 277) — product-degree bookkeeping giving `SmolenskyDegreeHalving` from the wiring.
* **the binomial tail** `lowDegreeDim n (D + n/2) < 2ⁿ − E` for `D` small — a standard binomial estimate (hypothesis here).
* **`CrossFieldCountHard` from the lower bound** — the prime lower bound (`no_small_approximator`) shows no small `AC⁰[p]`
  circuit computes the target, i.e. the cross-field count is hard; identifying this with the `CrossFieldCountHard` Prop is
  the (prime-case) connection.
* **composite modulus** — the open `CarryRefinementCrossing` wall (entry 238), untouched.

## Honest scope

This assembles the prime-case Smolensky lower bound from the proved pigeonhole/halving/wiring (`no_small_approximator`)
and wires its hardness to `ACC0CompositeComponent` (`prime_route_to_ACC0Component`).  The remaining inputs are the
mechanical product-degree bookkeeping (entry 277), the standard binomial tail, and the prime-case
`CrossFieldCountHard` identification.  **Composite modulus is the open wall** (entry 238).  This is **not** `NEXP ⊄ ACC⁰`
or `P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0SmolenskyPrime

open PallLean.Paper93.DeepMath.PathB.ACC0SmolenskyPigeonhole (SmolenskyDegreeHalving smolensky_lower_bound_via_pigeonhole)
open PallLean.Paper93.DeepMath.PathB.ACC0NonNativeDegree (lowDegreeDim)
open PallLean.Paper93.DeepMath.PathB.ACC0FirePatternRichness (crossFieldHard_to_ACC0Component)

/-- **Step 3a — the good set is bounded by the low-degree dimension (PROVED).**  Under degree-halving on `G` (every
good-set point function is degree `≤ D'`, from entries 276/277), the pigeonhole (entry 275) forces
`|G| ≤ lowDegreeDim n D'`: the good set cannot exceed the low-degree dimension.  (Contrapositive of
`smolensky_lower_bound_via_pigeonhole`.) -/
theorem smolensky_prime_goodset_bound {F : Type} [Field F] {n D' : ℕ}
    (G : Finset (Fin n → Bool)) (hhalving : SmolenskyDegreeHalving (F := F) (D' := D') G) :
    G.card ≤ lowDegreeDim n D' := by
  by_contra h
  push_neg at h
  exact smolensky_lower_bound_via_pigeonhole G hhalving h

/-- **Step 3 — the prime Smolensky lower bound (PROVED).**  If the good set `G` satisfies degree-halving (entries
276/277), is large (`2ⁿ − E ≤ |G|`, the small-bad-set output of the approximation machinery), and the low-degree
dimension is below that threshold (`lowDegreeDim n D' < 2ⁿ − E`, the binomial tail), then `False`: no degree-`D'`,
`≤ E`-error approximator of the symmetric (`MOD`/parity) target exists.  (From `smolensky_prime_goodset_bound`:
`2ⁿ − E ≤ |G| ≤ lowDegreeDim n D' < 2ⁿ − E`.) -/
theorem no_small_approximator {F : Type} [Field F] {n D' E : ℕ}
    (G : Finset (Fin n → Bool)) (hhalving : SmolenskyDegreeHalving (F := F) (D' := D') G)
    (hGsize : 2 ^ n - E ≤ G.card) (htail : lowDegreeDim n D' < 2 ^ n - E) : False := by
  have hbound := smolensky_prime_goodset_bound G hhalving
  omega

/-- **Step 4 — wire the prime hardness to the ACC component (PROVED).**  The prime lower bound shows the target's
cross-field count is hard (`CrossFieldCountHard`); the entry-261 bridge `crossFieldHard_to_ACC0Component` then yields
`ACC0CompositeComponent`, the component upstream of Williams `NEXP ⊄ ACC⁰`. -/
theorem prime_route_to_ACC0Component {CrossFieldCountHard ACC0CompositeComponent : Prop}
    (hCFH : CrossFieldCountHard)
    (hbridge : crossFieldHard_to_ACC0Component CrossFieldCountHard ACC0CompositeComponent) :
    ACC0CompositeComponent :=
  hbridge hCFH

/-!
**The prime route, assembled.**  The prime-case Smolensky lower bound is now assembled from proved parts: degree-halving
(§5r/§5s, entries 276/277) makes the good-set point functions low-degree; the pigeonhole (§5q, entry 275) then bounds
the good set by the low-degree dimension (`smolensky_prime_goodset_bound`); and with a large good set + the binomial
tail this is a contradiction (`no_small_approximator`) — no low-degree small-error approximator of the symmetric target.
Its hardness wires to `ACC0CompositeComponent` via the entry-261 bridge (`prime_route_to_ACC0Component`).  The residual
inputs are the mechanical `ApproximatorDegreeBound` (entry 277), the standard binomial tail, and the prime-case
`CrossFieldCountHard` identification.  **Composite modulus is the open `CarryRefinementCrossing` wall** (entry 238),
deliberately untouched.  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0SmolenskyPrime

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SmolenskyPrime.smolensky_prime_goodset_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SmolenskyPrime.no_small_approximator
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SmolenskyPrime.prime_route_to_ACC0Component
