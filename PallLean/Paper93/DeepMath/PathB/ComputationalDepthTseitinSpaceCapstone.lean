import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinSpace
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTseitinSpaceObserver
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTseitinCompleteForcing

/-!
# Tseitin proof-space observer capstone — the positive `Ω(|V|)` space lower bound

This file collects, under clean citable names, the genuinely-proved Tseitin **proof-space** lower bound in
the blackboard/configuration resolution model — the "first positive observer bound." Each name is verified
by `#print axioms` to depend on **only** `propext, Classical.choice, Quot.sound`.

The "observer boundary" is *defined* to be the resolution refutation's total space
(`observerBoundary := Blackboard.totalSpace`). The bound is a pure **space** bound (`Ω(|V|)` total space),
proved with no Atserias–Dalmau space–width inequality and no locking lemma.

## The capstone theorems (all PROVED, clean-axiom, no `sorry`)

* **`tseitin_proofspace`** (`= TseitinSpace.tseitin_totalSpace_lower_bound`) — the engine: for a Tseitin
  graph with `HasExpansion c` (`c ≥ 1`), globally-unsatisfiable charge, the standard axiom encoding, and
  `1 < t`, `4t ≤ |V|`, **every** blackboard resolution refutation reaching `∅` has `c·t ≤ totalSpace`.
* **`tseitin_proofspace_observer`** (`= TseitinSpaceObserver.tseitin_proofSpace_observer_lower_bound`) — the
  observer restatement: `c·t ≤ observerBoundary Ref` for a general expander.
* **`completeGraph_tseitin_proofspace`** (`= TseitinSpaceObserver.completeGraph_tseitin_space_lower_bound`) —
  **expansion discharged**: for `Kₙ` with odd charge and the standard axiom set, every refutation has
  `t ≤ observerBoundary Ref` for `1 < t`, `4t ≤ n` — i.e. total space `≥ ⌊n/4⌋ = Ω(|V|)`, unconditional
  (only odd charge + standard encoding + a refutation exists).
* **`tseitin_proofspace_unbounded`** (`= TseitinSpaceObserver.tseitin_proofSpace_observer_unbounded`) — for
  every `K ≥ 2`, the `K_{4K}` instance forces boundary `≥ K`; the boundary is provably not `O(1)`.
* **`tseitin_min_proofspace`** (`= TseitinCompleteForcing.tseitin_complete_min_space`) — the
  proof-system-level bound: for odd-charge `Kₙ`, `t ≤ minProofSpaceBoundary` (sInf over **all** refutations)
  for `1 < t`, `4t ≤ n`. The whole resolution proof system needs `Ω(|V|)` space.

## Honest scope

This is a genuine positive proof-space lower bound, but it is **restricted**, in three explicit ways:

1. **Model.** It bounds the **resolution** blackboard/configuration proof-space observer (the memory of a
   resolution refutation), *not* the general machine-decomposition observer of an arbitrary SAT-decider.
   That general observer (`min` over all admissible decompositions ≥ `ω(log n)`) is `CookLevinFrontierHyp`,
   `P`-vs-`NP`-strength, and **open** (untouched here).
2. **Space, not spacetime.** It is an `Ω(|V|)` *total-space* bound, not a spacetime (space×time) tradeoff.
   The sibling "spacetime/lightcone" files are a **socket harness** — `requiredSpacetimeVolume` is hard-coded
   to `0`, the asymptotic signed-Tseitin expander family is never constructed, and the locality/communication
   principle is an assumed hypothesis — so there is **no** unconditional spacetime bound and those are **not**
   part of this capstone.
3. **PHP sibling is partial.** The generic forcing engine is proved, but the classic PHP bipartite-expansion
   input remains a named hypothesis (not proved here).

Real machine-checked mathematics at the **resolution proof-space** tier — and honestly **not** `NEXP ⊄ ACC⁰`
or `P ≠ NP`. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`. See `TSEITIN_SPACE_CAPSTONE.md`, the master ledger
`PRIME_ACC0_CAPSTONE.md`, and `SCOPE_OBSERVER_PROGRAMME_CAPSTONE.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TseitinSpaceCapstone

/-- The engine: expander-Tseitin forces `c·t ≤ totalSpace` for every blackboard resolution refutation. -/
alias tseitin_proofspace := PallLean.Paper93.DeepMath.PathB.TseitinSpace.tseitin_totalSpace_lower_bound

/-- Observer restatement: `c·t ≤ observerBoundary Ref` (general expander). -/
alias tseitin_proofspace_observer :=
  PallLean.Paper93.DeepMath.PathB.TseitinSpaceObserver.tseitin_proofSpace_observer_lower_bound

/-- Expansion discharged: `Kₙ`-Tseitin forces total space `≥ ⌊n/4⌋ = Ω(|V|)`, unconditional. -/
alias completeGraph_tseitin_proofspace :=
  PallLean.Paper93.DeepMath.PathB.TseitinSpaceObserver.completeGraph_tseitin_space_lower_bound

/-- The proof-space observer boundary is provably not `O(1)`: every bound `K` is forced by some instance. -/
alias tseitin_proofspace_unbounded :=
  PallLean.Paper93.DeepMath.PathB.TseitinSpaceObserver.tseitin_proofSpace_observer_unbounded

/-- Proof-system-level: `Kₙ`-Tseitin needs `Ω(|V|)` space over **all** resolution refutations (`sInf`). -/
alias tseitin_min_proofspace :=
  PallLean.Paper93.DeepMath.PathB.TseitinCompleteForcing.tseitin_complete_min_space

end PallLean.Paper93.DeepMath.PathB.TseitinSpaceCapstone

#print axioms PallLean.Paper93.DeepMath.PathB.TseitinSpaceCapstone.tseitin_proofspace
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinSpaceCapstone.tseitin_proofspace_observer
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinSpaceCapstone.completeGraph_tseitin_proofspace
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinSpaceCapstone.tseitin_proofspace_unbounded
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinSpaceCapstone.tseitin_min_proofspace
