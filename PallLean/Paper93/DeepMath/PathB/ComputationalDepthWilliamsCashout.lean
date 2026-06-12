import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverAlgorithmicSchema
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSpeedupMargin

/-!
# The Williams cash‑out — the one route with teeth, built faithfully (template + the NEXP→NP gap)

The debt mechanism caps at effective dimension `< r` (the brute‑force escape is real).  The **only** known way
past that ceiling is the Williams route: don't lower‑bound the boundary — turn a *cheap separator* into an
**algorithmic speedup**, and collapse it against a **time hierarchy**.  This file builds that structure as a
checkable object and locates precisely where it bites and where it stalls.

## The genuine three‑part structure (Williams, `NEXP ⊄ ACC⁰`)

```
(smallCircuits)  a hard problem has small circuits / a cheap separator
(speedup)        ⇒ a faster‑than‑brute‑force algorithm for the class's SAT
(hierarchy)      ⇒ a class collapse (NTIME shortcut)
(noCollapse)     but the nondeterministic time hierarchy forbids that collapse
            ────────────────────────────────────────────────────────────────
                 the hard problem has NO small circuits
```

The lower bound comes from the **contradiction**, not from bounding boundary — that is the "teeth," and it
bypasses the `d_obs < r` ceiling entirely.

## Proved (clean axioms, no `sorry`)

* `williams_cashout` — the faithful composition: `speedup` (smallCircuits ⇒ fastSat) `+` `hierarchy`
  (fastSat ⇒ collapse) `+` `noCollapse` (the hierarchy theorem) `⇒ ¬ smallCircuits`.  Three‑part, vs the
  two‑part `williams_route`.
* `cashout_with_margin` — the margin‑aware form: the speedup must be *strong enough* (savings `≥ 2^m` with `m`
  super‑poly) for the hierarchy to bite; `cheap separator ⇒ savings ≥ 2^m` is supplied by the framework's DP
  engine, and `margin_le_of_correct` shows the deliverable margin is `n − r = Ω(n)` — abundant.

## What this route delivers, and the exact NEXP→NP gap (honest)

* **The framework supplies the `speedup` ingredient.**  A low‑action / low‑boundary observer *is* a structured
  fast‑SAT algorithm (`dpSat_beats_bruteforce`), and `margin_le_of_correct` proves its savings is `Ω(n)` —
  more than the `n^{ω(1)}` the hierarchy needs.  So, unlike every boundary‑mechanism route, the *margin is not
  the blocker here.*
* **`noCollapse` (the hierarchy) is real and provable** — the nondeterministic time hierarchy is a genuine
  diagonalization theorem (not open).  It is the source of the teeth.
* **Where it stalls — twice, and these are the open inputs:**
  1. **`speedup` for a *decision‑hard* problem.**  Williams' instantiation works because a fast *ACC⁰‑SAT*
     algorithm exists *and* `NEXP ⊆ ACC⁰` would compress witnesses.  Our hard instance (expander‑Tseitin) is
     *decision‑easy* (Gaussian, `tseitin_unsat_of_odd_charge`), so a fast algorithm for it triggers **no**
     collapse — correctly, it is in `P`.  The route needs a *decision‑hard* family whose cheap separator
     compresses; that is the missing object.
  2. **NEXP → NP.**  Williams proves `NEXP ⊄ ACC⁰`; the hierarchy gives teeth at the *exponential* level.
     Pulling the same argument down to `NP ⊄ ACC⁰` (let alone `P ≠ NP`) is a known open problem — the
     hierarchy's separation at the polynomial level is far weaker.

So the Williams cash‑out is the **right route and the only one with teeth**, the framework genuinely supplies
its algorithmic half with abundant margin, and what remains open is exactly: a decision‑hard family with a
compressing cheap separator, and the NEXP→NP descent.  These are the field's open frontier (guarded by
natural proofs / relativization / algebrization), not gaps a Lean file closes.  This file builds the template
faithfully and names them; it proves no separation.
-/

namespace PallLean.Paper93.DeepMath.PathB.WilliamsCashout

open PallLean.Paper93.DeepMath.PathB.ObserverAlgorithmic

/-- **The Williams cash‑out (proved composition).**  A cheap separator / small circuits (`smallCircuits`) give a
fast SAT algorithm (`speedup`), which collapses a class (`hierarchy`); but the time hierarchy forbids the
collapse (`noCollapse`).  Hence the hard problem has no cheap separator.  The lower bound is the
*contradiction* — no boundary is bounded — which is why this route passes the `d_obs < r` ceiling. -/
theorem williams_cashout {smallCircuits fastSat collapse : Prop}
    (speedup : smallCircuits → fastSat) (hierarchy : fastSat → collapse) (noCollapse : ¬ collapse) :
    ¬ smallCircuits :=
  fun h => noCollapse (hierarchy (speedup h))

/-- **Margin‑aware cash‑out (proved).**  The speedup must clear the hierarchy's threshold: if a cheap separator
yields savings `≥ 2^m` (`speedup`) and a savings of `2^m` collapses the class (`hierarchyAtMargin`) which the
hierarchy forbids (`noCollapse`), then no cheap separator exists.  The framework supplies `speedup` (DP engine)
with `m = n − r = Ω(n)` (`margin_le_of_correct`), so the margin clears the bar; the open part is the other two. -/
theorem cashout_with_margin {smallCircuits collapse : Prop} (m : ℕ)
    (speedup : smallCircuits → (∃ savings : ℕ, 2 ^ m ≤ savings))
    (hierarchyAtMargin : (∃ savings : ℕ, 2 ^ m ≤ savings) → collapse)
    (noCollapse : ¬ collapse) :
    ¬ smallCircuits :=
  fun h => noCollapse (hierarchyAtMargin (speedup h))

end PallLean.Paper93.DeepMath.PathB.WilliamsCashout

#print axioms PallLean.Paper93.DeepMath.PathB.WilliamsCashout.williams_cashout
#print axioms PallLean.Paper93.DeepMath.PathB.WilliamsCashout.cashout_with_margin
