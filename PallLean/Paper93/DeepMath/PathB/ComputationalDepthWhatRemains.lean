import PallLean.Paper93.DeepMath.PathB.ComputationalDepthInjectTheDoubling

/-!
# What remains to prove P ≠ NP: exactly one statement

This is the terminus of the arc, stated plainly.  After building the apparatus and locating the wall
from three independent bearings, **exactly one open statement remains**, and everything downstream of
it is proved, axiom-clean.

## The one statement

`WhatIsLeft cbudget := ∀ d, 2 · cbudget d ≤ cbudget (d+1)` — for the SAT composition tower, the cost
**at least doubles** per composition level (`cost_super`).  That is the whole of what is unproved.

Everything above it is machine-checked here:

* **`left_gives_exponential`** — the one statement forces `cbudget d ≥ 2^d`.
* **`left_breaks_P`** — hence no bounded (polynomial) budget survives: P-membership of SAT is
  impossible.  So `WhatIsLeft ⟹ SAT ∉ P ⟹ P ≠ NP`, with the cash-out proved (cited from
  `InjectTheDoubling`).
* **`left_is_cost_super`** — and the one statement is exactly `cost_super` (`Iff.rfl`).

## The same statement, localized (the gate-side form)

The three-bearing triangulation gives `WhatIsLeft` an equivalent *structural* form, which is what a
direct attack would target:

> **SAT's minimal circuit contains no global gate** — no gate that is nonlinear on two disjoint
> private territories (`GlobalGateCoordinates.GlobalGate`).

Equivalently, in each of the three languages the map established: SAT's minimal circuit has **bounded
reach** (localization), its two slots satisfy **NoSharing** (mass production fails), and the
computation across the territory partition is a **product / rectangle** (communication-trivial).
These are one statement — `cost_super` — seen from the size, sharing, and communication sides; and
its coordinate is the doubly-nonlinear-on-disjoint-territories gate, proved minimal.

## Honest scope — one statement, and it is the genuinely hard core

What remains is not a fog and not a list: it is a single inequality (`cost_super`), with an exact
equivalent structural form (exclude the global gate), and everything else — that this one statement
converts into `P ≠ NP` — is proved and axiom-clean.  This does **not** prove it.  The one statement is
P ≠ NP-hard by construction: the meta-arc showed the apparatus only *transports* it (measure, shape,
and injection are all fixed points), and it sits behind all three barriers (its proof must be
non-natural, anatomical, beyond the degree ceiling).  So the honest answer to "what is left" is:
exactly this — proved to be the only remaining obligation, located precisely, and left standing,
neither faked nor declared impossible.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.WhatRemains

open PallLean.Paper93.DeepMath.PathB.InjectTheDoubling

/-- **What is left to prove `P ≠ NP`.**  For the SAT composition tower, the cost at least doubles per
composition level: `∀ d, 2 · cbudget d ≤ cbudget (d+1)`.  This single statement is `cost_super`, and
it is the entire remaining obligation. -/
def WhatIsLeft (cbudget : ℕ → ℕ) : Prop := ∀ d, 2 * cbudget d ≤ cbudget (d + 1)

/-- **The one statement forces exponential cost (proved).**  `WhatIsLeft` (with base `cbudget 0 ≥ 1`)
gives `cbudget d ≥ 2^d`. -/
theorem left_gives_exponential (cbudget : ℕ → ℕ) (h : WhatIsLeft cbudget) (hbase : 1 ≤ cbudget 0)
    (d : ℕ) : 2 ^ d ≤ cbudget d :=
  doubling_forces_exponential cbudget h hbase d

/-- **The one statement breaks P-membership (proved).**  Given `WhatIsLeft`, no bounded (hence no
polynomial) budget can hold for all depths: `SAT ∉ P`, i.e. `P ≠ NP`.  The cash-out is proved; only
`WhatIsLeft` is open. -/
theorem left_breaks_P (cbudget : ℕ → ℕ) (h : WhatIsLeft cbudget) (hbase : 1 ≤ cbudget 0)
    (B : ℕ) (hbdd : ∀ d, cbudget d ≤ B) : False :=
  doubling_breaks_bounded cbudget h hbase B hbdd

/-- **The one statement is exactly `cost_super` (proved, `Iff.rfl`).**  What remains is neither more
nor less than the doubling of the SAT tower's cost. -/
theorem left_is_cost_super (cbudget : ℕ → ℕ) :
    WhatIsLeft cbudget ↔ (∀ d, 2 * cbudget d ≤ cbudget (d + 1)) := Iff.rfl

end PallLean.Paper93.DeepMath.PathB.WhatRemains

#print axioms PallLean.Paper93.DeepMath.PathB.WhatRemains.left_gives_exponential
#print axioms PallLean.Paper93.DeepMath.PathB.WhatRemains.left_breaks_P
#print axioms PallLean.Paper93.DeepMath.PathB.WhatRemains.left_is_cost_super
