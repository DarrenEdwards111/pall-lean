import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBoundedLocalityNonCollapse

/-!
# The raveling wedge — the surviving non‑circular program, and exactly where it lands

The blocked Step 5 was the *global* bridge "poly‑time ⇒ low action" (false: `step5_naive_bridge_false`).  The
**raveling wedge** replaces it with two more modest pieces that avoid that nakedly circular claim:

```
(raveling)     low‑action observer  ⇒  factors through a constrained separator class K
(noSeparator)  SAT has no separator in K
            ────────────────────────────────────────────────────────────
               no low‑action observer decides SAT
```

This is **exactly the structure of every known complexity lower bound**: fix a restricted class `K`, prove the
hard function is not in `K`.  The calibrations and the residual‑non‑collapse ladder in this corpus are *already*
instances of `noSeparator` for concrete `K`.

## Proved (clean axioms, no `sorry`)

* `ravel_wedge` — the composition: `raveling` (low‑action ⇒ in `K`) and `noSeparator` (`K` cannot decide SAT)
  give "no observer is both low‑action and SAT‑correct."  A one‑line, fully general reduction.

## Where it lands — the good news and the catch

* **Good news (non‑circular, and realized for restricted `K`).**  The wedge never asserts "poly‑time ⇒ low
  action."  Its two premises are *separately* provable for restricted `K`, and this corpus proves instances:
  - `noSeparator` for `K = F₂‑linear / read‑set / bounded‑locality observers` is exactly
    `expander_linear_decomposition_noncollapse`, `expander_residual_forces_debt`,
    `expander_bounded_locality_noncollapse` (the expander residual has no separator in those `K`);
  - `noSeparator` for `K = AC⁰[p] / Nečiporuk / communication` is the three calibrations
    (`mod_q_indicators_false` etc.).
  So the wedge is *not* speculative: it is the engine the whole programme already runs.

* **The catch (where `P ≠ NP` hides).**  To conclude `SAT ∉ P`, `K` must be large enough that `raveling`
  captures *every* low‑resource (ideally every `P`) observer.  Then `noSeparator` — "SAT has no separator in
  `K`" for that large `K` — **is** the decision lower bound `= P ≠ NP`.  So the wedge relocates the difficulty
  from the false global Step 5 into the size of `K`: it is **provable for every `K` we can currently beat, and
  exactly `P ≠ NP` for any `K` big enough to matter.**

HAL's refinement of the route is therefore correct and valuable: classify high‑boundary refinement into
*ravelable* (smooth, low‑holonomy — refinement helps) vs *non‑ravelable* (curved, high‑holonomy — refinement
cannot smooth), and prove SAT needs the second.  Expansion is precisely the source of non‑ravelable curvature
(`expander_manyloop_holonomy`), which is why the restricted instances work.  The open content is a *single*
inequality — `noSeparator` for a `K` that captures all of `P` — and that inequality is the separation.  The
wedge gives the cleanest non‑circular *architecture*; it does not, and this file does not, supply that
inequality.
-/

namespace PallLean.Paper93.DeepMath.PathB.RavelWedge

variable {Obs : Type*}

/-- **The raveling wedge (proved).**  If every low‑action observer factors through a constrained separator
class `K` (`raveling`), and no member of `K` is a correct SAT decider (`noSeparator`), then no observer is both
low‑action and SAT‑correct.  Both premises are explicit; neither is the blocked global bridge "poly‑time ⇒ low
action."  For restricted `K` both are theorems of this corpus; for `K` capturing all of `P`, `noSeparator` is
`P ≠ NP`. -/
theorem ravel_wedge (lowAction correctSAT inK : Obs → Prop)
    (raveling : ∀ o, lowAction o → inK o)
    (noSeparator : ∀ o, inK o → ¬ correctSAT o) :
    ∀ o, ¬ (lowAction o ∧ correctSAT o) :=
  fun o h => noSeparator o (raveling o h.1) h.2

/-- **Contrapositive form (proved).**  A correct SAT decider that lies in the ravelable class `K` cannot be
low‑action: if `K` has no SAT separator, then `inK` + `correctSAT` forces `¬ lowAction`.  This is the "SAT
requires the non‑ravelable (curved/high‑action) kind" statement, conditional on `noSeparator`. -/
theorem ravel_forces_high_action (lowAction correctSAT inK : Obs → Prop)
    (noSeparator : ∀ o, inK o → ¬ correctSAT o)
    (o : Obs) (hK : inK o) (hc : correctSAT o) :
    ¬ lowAction o :=
  fun _ => noSeparator o hK hc

end PallLean.Paper93.DeepMath.PathB.RavelWedge

#print axioms PallLean.Paper93.DeepMath.PathB.RavelWedge.ravel_wedge
#print axioms PallLean.Paper93.DeepMath.PathB.RavelWedge.ravel_forces_high_action
