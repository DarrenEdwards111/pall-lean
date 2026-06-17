import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DynamicObserverSelection
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RouteBComplete

/-!
# The BT-closure frontier — the final conditional chain `dynamic closure ⇒ NEXP ⊄ ACC⁰`

The dynamic-observer programme (`…ACC0DynamicObserverSelection`, the capstone) is **frozen**: it proved that the
boundary is forced to refine the observer up the ladder `residue → p-adic carry → threshold`, and it isolated the one
remaining wall — that refinement *closes* at a quasipolynomial-size Beigel–Tarui `SYM∘AND` observer.  This file states
the **whole reduction as a single conditional theorem**, ending not at an abstract `Speedup` but at the codebase's actual
separation statement `¬ NEXPHasACC0Circuits` (via the proved Route-B / Williams glue of `…ACC0RouteBComplete`).

The chain is:
```
  DynamicClosesAtBT          -- SOCKET: dynamic refinement stabilises at a BT/SYM∘AND observer (the ACC⁰[composite] wall)
    → BTHasQuasipolySparse   -- SOCKET: that observer has a quasipoly-size sparse representation
    → ACC0SatSpeedup         -- the sparse read-off gives a sub-2ⁿ ACC⁰-SAT algorithm
    → ¬ NEXPHasACC0Circuits  -- Williams cash-out + nondeterministic time hierarchy
```

## What is proved (clean axioms, no `sorry`)

* **`dynamicClosure_to_NEXP_not_ACC0`** — the end-to-end conditional: the dynamic-closure socket, plus the
  closure→quasipoly and quasipoly→speedup implications, plus the Williams glue (`williams`) and the hierarchy
  (`hierarchy`, `¬ Collapse`), yield `¬ NEXPHasACC0Circuits`.  Pure composition (modus ponens through the proved
  Route-B reduction); it depends on **no axioms**.
* **`observer_ladder_proved`** (re-export) — the proved foundation the chain rests on: the boundary refines the `MOD_p`
  observer to the sufficient `p`-adic observer for `MOD_{p^e}` (`…ACC0DynamicObserverSelection`).

## Honest scope

This is the **final scaffolding**, not a proof of `NEXP ⊄ ACC⁰`.  The chain is valid and machine-checked, but its two
load-bearing premises — `DynamicClosesAtBT` (refinement closes at a BT observer) and `BTHasQuasipolySparse` (that
observer is quasipoly-size) — are **unproved sockets**, and together they *are* the open `ACC⁰[composite]` lower bound
(equivalently, the Beigel–Tarui/Yao quasipolynomial `SYM∘AND` representation for arbitrary `ACC⁰`).  The proved part is
everything *around* the wall: the observer-refinement ladder up to thresholds (`…DynamicObserverSelection`,
`…CountCarrySymmetric`, `…CarrySparseTheory`, `…ValuationSparseTheory`) and the Route-B/Williams reduction
(`…ACC0RouteBComplete`).  Discharging `DynamicClosesAtBT` is the hard wall; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BTClosureFrontier

open PallLean.Paper93.DeepMath.PathB

/-- **The final conditional chain (proved as glue; every premise is a socket): dynamic BT-closure ⇒ `NEXP ⊄ ACC⁰`.**
If dynamic refinement closes at a BT/`SYM∘AND` observer (`hClosure : DynamicClosesAtBT`), and that yields a
quasipolynomial sparse representation (`closure_to_quasipoly`), which yields the `ACC⁰`-SAT speedup
(`quasipoly_to_speedup`), then — with the Williams meta-glue (`williams`) and the nondeterministic time hierarchy
(`hierarchy : ¬ Collapse`) — we get `¬ NEXPHasACC0Circuits`.  Pure composition through the proved Route-B reduction
(`…ACC0RouteBComplete.routeB_to_NEXP_not_ACC0`); depends on **no axioms**.  The open content is entirely in the two
socket premises `DynamicClosesAtBT` and `closure_to_quasipoly`, which together are the `ACC⁰[composite]` lower bound. -/
theorem dynamicClosure_to_NEXP_not_ACC0
    (DynamicClosesAtBT BTHasQuasipolySparse ACC0SatSpeedup NEXPHasACC0Circuits Collapse : Prop)
    (hClosure : DynamicClosesAtBT)
    (closure_to_quasipoly : DynamicClosesAtBT → BTHasQuasipolySparse)
    (quasipoly_to_speedup : BTHasQuasipolySparse → ACC0SatSpeedup)
    (williams : ACC0SatSpeedup → NEXPHasACC0Circuits → Collapse)
    (hierarchy : ¬ Collapse) :
    ¬ NEXPHasACC0Circuits :=
  ACC0RouteBComplete.routeB_to_NEXP_not_ACC0
    BTHasQuasipolySparse ACC0SatSpeedup NEXPHasACC0Circuits Collapse
    (closure_to_quasipoly hClosure) quasipoly_to_speedup williams hierarchy

/-- **The proved foundation the chain rests on (re-export).**  The dynamic boundary provably refines the residue
(`MOD_p`) observer to the sufficient `p`-adic carry observer for `MOD_{p^e}`: the residue observer is insufficient, the
`p`-adic observer is sufficient, and it refines the residue observer.  This is the bottom of the ladder that the
`DynamicClosesAtBT` socket continues to the BT observer. -/
theorem observer_ladder_proved (p e : ℕ) (hp : p.Prime) (he : 2 ≤ e) :
    ¬ ACC0DynamicObserverSelection.Sufficient (ACC0DynamicObserverSelection.resObs p)
        (ACC0DynamicObserverSelection.modPow p e)
      ∧ ACC0DynamicObserverSelection.Sufficient (ACC0DynamicObserverSelection.padicObs p e)
        (ACC0DynamicObserverSelection.modPow p e)
      ∧ ACC0DynamicObserverSelection.Finer (ACC0DynamicObserverSelection.padicObs p e)
        (ACC0DynamicObserverSelection.resObs p) :=
  ACC0DynamicObserverSelection.observer_refines_modp_to_padic p e hp he

end PallLean.Paper93.DeepMath.PathB.ACC0BTClosureFrontier

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BTClosureFrontier.dynamicClosure_to_NEXP_not_ACC0
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BTClosureFrontier.observer_ladder_proved
