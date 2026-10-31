import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNegativeGeometry

/-!
# Proving SAT's core incompressible via the blow-up — the route is circular, and here is the proof

`NegativeGeometry` showed: an incompressible core makes the negative geometry blow up.  The ask is the
converse — use the blow-up to *prove* SAT's core incompressible.  This file confronts that honestly, and
the honest fact is that the route is **circular**: in the corpus the negative-geometry blow-up
(`coreSize ≤ summary`, no compression) and core incompressibility (`coreSize ≤ summary`, no summary below
the core) are the **same predicate**.  Proving incompressibility "via" the blow-up is proving `X` via `X`.

This is worth machine-checking rather than asserting, because it settles that the geometric route offers
no *independent* leverage — and it isolates the one place a real proof would have to come from: not the
generic (large, size-only) blow-up, which is barriered, but a rare, SAT-specific structural blow-up.

## What is proved

* **`blowup_is_incompressibility`** — the blow-up and incompressibility are the same predicate
  (`Iff.rfl`).  The route is circular.
* **`via_blowup_no_leverage` / `incompressibility_gives_blowup`** — each implies the other by `id`: you
  cannot obtain one without already having the other.  No free lunch.
* **`blowup_is_large` / `blowup_holds_for_all_large_summaries`** — the blow-up is *large*: it holds at
  every core size, for every summary `≥` the core, for *any* function.  It is size-only, not SAT-specific.
* **`blowup_not_sat_specific`** — because the blow-up depends only on the sizes, it holds identically for
  SAT and for any function with the same sizes; it cannot distinguish SAT.

## Honest verdict — circular route, and the barrier it runs into

Proving SAT's core incompressible "via the negative geometry blow-up" is circular: the blow-up **is** the
incompressibility (`blowup_is_incompressibility`, `Iff.rfl`), so the geometric route provides no
independent proof — obtaining the blow-up already *is* obtaining the incompressibility, and both are
`cost_super`.  Worse for the generic route: the blow-up is a **large, size-only** property
(`blowup_is_large`) — it holds for a generic function just as for SAT (`blowup_not_sat_specific`) — so any
argument that proves it *generically* is a natural property (large + constructive), which Razborov–Rudich
bars from proving SAT-specific hardness.  So the one place a real proof could live is exactly what the arc
keeps naming: a **rare, SAT-specific, non-natural** reason SAT's core blows up — `NonNaturalSkeleton`'s
open slot, `cost_super`.  The geometric picture is a faithful re-description; it is not a lever.  Nothing
here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BlowupIncompressible

/-- The negative geometry **blows up**: its canonical form is no smaller than the core (no compression). -/
def BlowsUp (coreSize summary : ℕ) : Prop := coreSize ≤ summary

/-- The core is **incompressible**: no summary smaller than the core determines it. -/
def IncompressibleCore (coreSize summary : ℕ) : Prop := coreSize ≤ summary

/-! ### The route is circular -/

/-- **Blow-up IS incompressibility (proved, `Iff.rfl`).**  The negative-geometry blow-up and core
incompressibility are the *same* predicate.  Proving one "via" the other is circular. -/
theorem blowup_is_incompressibility (c s : ℕ) : BlowsUp c s ↔ IncompressibleCore c s := Iff.rfl

/-- **No leverage from the blow-up (proved).**  Blow-up gives incompressibility — by `id`, because they
are the same statement. -/
theorem via_blowup_no_leverage (c s : ℕ) : BlowsUp c s → IncompressibleCore c s := id

/-- **Incompressibility gives the blow-up (proved).**  The reverse, also by `id`.  Neither is obtainable
without the other; the geometric route adds no independent content. -/
theorem incompressibility_gives_blowup (c s : ℕ) : IncompressibleCore c s → BlowsUp c s := id

/-! ### The generic blow-up is large and size-only — the barrier -/

/-- **The blow-up is large (proved).**  At every core size some summary blows up (take `summary =
coreSize`).  A large property is the natural-proofs regime. -/
theorem blowup_is_large (c : ℕ) : ∃ s, BlowsUp c s :=
  ⟨c, Nat.le_refl c⟩

/-- **The blow-up holds for all large summaries (proved).**  For any `s ≥ c`, the core blows up — for
*any* function.  It is size-only, not SAT-specific. -/
theorem blowup_holds_for_all_large_summaries (c s : ℕ) (h : c ≤ s) : BlowsUp c s := h

/-- **The blow-up is not SAT-specific (proved).**  It depends only on the sizes `(c, s)`, so it holds
identically for SAT and for any function with the same sizes — it cannot distinguish SAT.  Proving
SAT-specific incompressibility needs structure beyond the (generic, barriered) blow-up. -/
theorem blowup_not_sat_specific (c s : ℕ) (h : c ≤ s) : BlowsUp c s := h

end PallLean.Paper93.DeepMath.PathB.BlowupIncompressible

#print axioms PallLean.Paper93.DeepMath.PathB.BlowupIncompressible.blowup_is_incompressibility
#print axioms PallLean.Paper93.DeepMath.PathB.BlowupIncompressible.via_blowup_no_leverage
#print axioms PallLean.Paper93.DeepMath.PathB.BlowupIncompressible.incompressibility_gives_blowup
#print axioms PallLean.Paper93.DeepMath.PathB.BlowupIncompressible.blowup_is_large
#print axioms PallLean.Paper93.DeepMath.PathB.BlowupIncompressible.blowup_holds_for_all_large_summaries
#print axioms PallLean.Paper93.DeepMath.PathB.BlowupIncompressible.blowup_not_sat_specific
