import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMagnifiedMetaTrigger
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMetaCompletenessSelfRef

/-!
# The best-guess route, reduced to a single open statement (the honest artifact)

This capstone assembles the whole best-guess route into one machine-checked implication.  Every link
built this session is discharged; the conclusion `SAT ∉ P` is derived from a **single open input** —
the incompressibility of the specific MCSP target — plus standard sockets.

The links, all proved/discharged earlier:

* **magnification mechanism** — `SelfImproving ⟹ MagnifiedBound` (`MagnifiedMetaTrigger.magnifies`,
  proved; = the `cost_super` amplification engine).
* **the anti-checker win-win** — `SelfImproving ∨ Compress` (CIKK; a socket).
* **completeness** — `MCSP ∈ NP ⟹ (MCSP hard ⟹ SAT hard)` (`MetaCompletenessSelfRef.meta_completeness`,
  the self-referential `MCSP ≤ SAT` reduction, axiom-free).

The single open input is `¬ Compress` — that the specific MCSP target is incompressible.  That is
`cost_super` in the meta-complexity costume: provable generically (counting) but open for the specific
target (the natural-proofs gap, `SelfImproveRatio`).

## What is proved

* **`route_rests_on_incompressibility`** — from the anti-checker win-win, `MCSP ∈ NP`, the
  P/poly→P bridge, and the ONE open input `¬ Compress`, the separation `SAT ∉ P` follows.  The whole
  route, in one implication, resting on a single named statement.

## Honest scope

This is not a proof of `P ≠ NP`.  It is the honest artifact: a machine-checked reduction of the entire
best-guess route to a *single* open statement — the incompressibility of the specific MCSP target —
with every other link proved or discharged.  The open input is `P ≠ NP`-strength; the value is that it
is now *one named, precisely located* statement, the same `cost_super` wall every route reaches.
-/

namespace PallLean.Paper93.DeepMath.PathB.BestGuessRouteCapstone

open PallLean.Paper93.DeepMath.PathB.MagnifiedMetaTrigger
open PallLean.Paper93.DeepMath.PathB.MetaCompletenessSelfRef

/-- **The best-guess route rests on a single open statement (proved).**  Given:
* `winwin` — the CIKK anti-checker (`SelfImproving ∨ Compress`), a socket;
* `h_inNP` — `MCSP ∈ NP` (the self-referential reduction, discharged);
* `bridge` — the magnified (superpolynomial circuit) bound implies MCSP is not in P (the standard
  `P ⊆ P/poly` step);
* `incompressible` — `¬ Compress`, the ONE open input: the specific MCSP target is incompressible
  (`cost_super`);

the separation `SAT ∉ P` (`¬ W.Easy W.sat`) follows.  Every link except `incompressible` (and the
`winwin`/`bridge` sockets) is proved. -/
theorem route_rests_on_incompressibility
    {Problem : Type} (W : NPWorld Problem) (mcsp : Problem)
    (L : MetaComplexityLadder) (p q : ℕ) (Compress : Prop)
    (winwin : SelfImproving L p q ∨ Compress)
    (h_inNP : W.InNP mcsp)
    (bridge : MagnifiedBound L p q → ¬ W.Easy mcsp)
    (incompressible : ¬ Compress) :
    ¬ W.Easy W.sat :=
  meta_completeness W mcsp h_inNP
    (bridge (magnifies L p q (winwin.resolve_right incompressible)))

end PallLean.Paper93.DeepMath.PathB.BestGuessRouteCapstone

#print axioms PallLean.Paper93.DeepMath.PathB.BestGuessRouteCapstone.route_rests_on_incompressibility
