import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NFrameWilliamsRoute

/-!
# Bridge (Williams via N-Frame, honest anatomy) — the algorithmic-method socket is separation-strength (proved)

The honest conditional anatomy of the Williams route to `NEXP ⊄ ACC⁰`, through the N-Frame algorithmic-counting branch.  The
N-Frame counting route (integer-count observer, count-cell boundary, `< 2^n` compression) *is* the fast-SAT route
(`nframe_williams_route_equiv`, proved), and the char-0 escape (`nframe_observer_characteristic_free`, proved) handles the
composite-modulus barrier that blocks the single-field polynomial method.  What remains is the **algorithmic-method bridge**:
a fast-SAT speedup, combined with `NEXP ⊆ ACC⁰`, collapsing the nondeterministic time hierarchy.

This brick makes the honesty explicit, in the self-audit style: **that collapse socket is exactly the separation**.  Given the
(proved-structure) counting route, the uniform-realization socket, and the time hierarchy, the collapse socket holds *iff*
`NEXP ⊄ ACC⁰` (`nframe_collapse_socket_iff_separation`).  So the Williams/N-Frame route does **not** reduce `NEXP ⊄ ACC⁰` to
something weaker — the load-bearing socket is the separation itself (P≠NP-adjacent strength), not progress hidden in
infrastructure.

## What is proved (clean axioms, no `sorry`)

* **`nframe_collapse_socket_iff_separation`** (PROVED) — given the counting route + realization socket + time hierarchy, the
  algorithmic-method collapse socket `↔ ¬(NEXP ⊆ ACC⁰)`.
* **`nexp_not_acc0_via_nframe`** (PROVED, conditional) — `¬(NEXP ⊆ ACC⁰)` from the YBT/`SYM∘AND` socket
  (`WilliamsFastSatRoute`, the classical Beigel–Tarui form) + the named algorithmic-method sockets.

## Honest scope

This is the **conditional anatomy**, not an unconditional `NEXP ⊄ ACC⁰`.  Two kinds of remaining content are named and
distinguished:
* `WilliamsFastSatRoute` (= `∀ C, HasExactSymAndForm C`) — the general YBT/`SYM∘AND` form (classical Beigel–Tarui);
  proved in the corpus only under structural restrictions, a *formalization* gap, **not** P≠NP-strength.
* the **collapse socket** — proved here to be *equivalent to the separation*, hence the genuinely deep, separation-strength
  step (easy-witness / NW + nondeterministic time hierarchy).

Nothing here is an unconditional `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0NFrameWilliamsAnatomy

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (CClass)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (NEXP NTIME)
open PallLean.Paper93.DeepMath.PathB.ACC0NFrameWilliamsRoute
  (NFrameWilliamsRoute WilliamsFastSatRoute nframe_williams_route_equiv nframe_fastSat_to_timeHierarchy)

/-- **Self-audit: the algorithmic-method collapse socket is separation-strength (PROVED).**  Given the (proved-structure)
N-Frame counting route, the uniform-realization socket, and the nondeterministic time hierarchy, the collapse socket holds
*iff* `NEXP ⊄ ACC⁰`.  Forward: the full Williams composition.  Backward: if `NEXP ⊄ ACC⁰` then `NEXP ⊆ ACC⁰` is false, so the
collapse implication is vacuous.  Hence the route does not reduce the separation to anything weaker. -/
theorem nframe_collapse_socket_iff_separation (ACC0 : CClass) (f g : ℕ → ℕ) (speedup : Prop)
    (routeGivesSpeedup : NFrameWilliamsRoute → speedup)
    (hierarchy : ¬ (NTIME f ⊆ NTIME g))
    (route : NFrameWilliamsRoute) :
    (speedup → NEXP ⊆ ACC0 → NTIME f ⊆ NTIME g) ↔ ¬ (NEXP ⊆ ACC0) := by
  constructor
  · intro collapse
    exact nframe_fastSat_to_timeHierarchy ACC0 f g speedup routeGivesSpeedup collapse hierarchy route
  · intro hsep _ hNEXP
    exact absurd hNEXP hsep

/-- **`NEXP ⊄ ACC⁰` from the YBT socket + algorithmic-method sockets (PROVED, conditional).**  The full Williams/N-Frame
route as one visible conditional: the YBT/`SYM∘AND` form (`hYBT`), the uniform realization (`routeGivesSpeedup`), the
easy-witness/NW collapse (`collapse`), and the time hierarchy (`hierarchy`) compose to `¬(NEXP ⊆ ACC⁰)`. -/
theorem nexp_not_acc0_via_nframe (ACC0 : CClass) (f g : ℕ → ℕ) (speedup : Prop)
    (hYBT : WilliamsFastSatRoute)
    (routeGivesSpeedup : NFrameWilliamsRoute → speedup)
    (collapse : speedup → NEXP ⊆ ACC0 → NTIME f ⊆ NTIME g)
    (hierarchy : ¬ (NTIME f ⊆ NTIME g)) :
    ¬ (NEXP ⊆ ACC0) :=
  nframe_fastSat_to_timeHierarchy ACC0 f g speedup routeGivesSpeedup collapse hierarchy
    (nframe_williams_route_equiv.mpr hYBT)

/-!
**Williams via N-Frame, honest anatomy, proved.**  The route is a genuine conditional with its open content named and
classified: the YBT/`SYM∘AND` form (classical, formalization-gap) and the collapse socket (proved separation-strength).  No
fake unconditional closure.  Remaining (open, not faked): the actual `NEXP ⊄ ACC⁰` (the collapse socket = the separation).
Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0NFrameWilliamsAnatomy

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NFrameWilliamsAnatomy.nframe_collapse_socket_iff_separation
