# Tseitin Proof-Space Observer Capstone & Scope

*One-page ledger for the positive Tseitin **proof-space** lower bound (resolution model) — a genuine but
**restricted** result. Capstone:
`PallLean/Paper93/DeepMath/PathB/ComputationalDepthTseitinSpaceCapstone.lean`. Nothing here is `NEXP ⊄ ACC⁰`
or `P ≠ NP`.*

---

## What is PROVED (clean-axiom, no `sorry`)

Each name verified by `#print axioms` to depend on only `propext, Classical.choice, Quot.sound` (**verified
by build** — despite the import surface reaching `GlobalGodMoveGauge`, no custom axiom enters any proof term).

| Capstone name | Statement | Backed by |
|---|---|---|
| `tseitin_proofspace` | engine: expander-Tseitin (`HasExpansion c`, unsat, standard encoding, `1<t`, `4t≤\|V\|`) forces `c·t ≤ totalSpace` for **every** blackboard resolution refutation | `TseitinSpace.tseitin_totalSpace_lower_bound` |
| `tseitin_proofspace_observer` | observer restatement (`observerBoundary := Blackboard.totalSpace`): `c·t ≤ observerBoundary Ref` | `TseitinSpaceObserver.tseitin_proofSpace_observer_lower_bound` |
| `completeGraph_tseitin_proofspace` | **expansion discharged**: `Kₙ` odd charge forces total space `≥ ⌊n/4⌋ = Ω(\|V\|)`, unconditional | `TseitinSpaceObserver.completeGraph_tseitin_space_lower_bound` |
| `tseitin_proofspace_unbounded` | the boundary is not `O(1)`: every bound `K` is forced by `K_{4K}` | `TseitinSpaceObserver.tseitin_proofSpace_observer_unbounded` |
| `tseitin_min_proofspace` | proof-system-level: `Kₙ` needs `Ω(\|V\|)` space over **all** refutations (`sInf`) | `TseitinCompleteForcing.tseitin_complete_min_space` |

**Status:** a genuine positive proof-space lower bound (`Ω(|V|)` total space), proved with **no**
Atserias–Dalmau space–width inequality and **no** locking lemma. For `Kₙ` the expansion constant is
discharged, so the bound is unconditional (only odd charge + standard axiom encoding + a refutation exists).

---

## The restriction (three explicit fences — why this is not more)

1. **Model = resolution, not the general observer.** It bounds the blackboard/configuration **resolution**
   proof-space (the memory of a resolution refutation), *not* the general machine-decomposition observer of an
   arbitrary SAT-decider. That general observer (`min` over all decompositions `≥ ω(log n)`) is
   `P`-vs-`NP`-strength and **open**, untouched here.
2. **Space, not spacetime.** This is an `Ω(|V|)` *total-space* bound, not a space×time tradeoff. The sibling
   "spacetime/lightcone" files are a **socket harness**: `requiredSpacetimeVolume` is hard-coded to `0`, the
   asymptotic signed-Tseitin expander family is **never constructed**, and the locality/communication
   principle is an assumed hypothesis. There is **no** unconditional spacetime bound; those files are **not**
   in this capstone.
3. **PHP sibling is partial.** The generic forcing engine (`PHPProofSpace.*`) is proved, but the classic PHP
   bipartite-expansion input (`phpWidthLink`/`phpRoot`) remains a named hypothesis, not proved here.

---

## Honest scope

- **Proved:** a positive `Ω(|V|)` Tseitin proof-space lower bound in the resolution model, incl. the
  proof-system-level `min`-over-refutations form — machine-checked, custom-axiom-free.
- **Open:** the general (non-resolution) machine-decomposition observer (`P`-vs-`NP`-strength); any spacetime
  tradeoff (Arc-2 socket harness); the PHP expansion input.

A real result at the **resolution proof-space** tier — honestly **not** the general observer, **not** a
spacetime bound, **not** `NEXP ⊄ ACC⁰`, **not** `P ≠ NP`.

*Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`. Companions: `PRIME_ACC0_CAPSTONE.md`,
`SCOPE_OBSERVER_PROGRAMME_CAPSTONE.md`, `SCOPE_OBSERVER_BOUNDARY_ENTROPY.md`.*
