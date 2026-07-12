# SCOPE: The charged dynamic-SPDP arc — a reduction to the P-vs-NP socket

This document records, honestly and in full, the charged holographic dynamic-SPDP investigation on branch
`razborov-recoverRho-wip`. It is a **capstone / scope note**, not a claim of a separation. Nothing in this arc is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.

All files below build with `#print axioms ⊆ {propext, Classical.choice, Quot.sound}` and no `sorry`.

## 1. What the arc set out to do

Formalize a "dynamic SPDP" candidate: project a machine's *actual computation trace* to a finite observer and
charge cumulative boundary innovation there, hoping for a resource `R` that is polynomial on every `P` machine
(`PUpper`) but super-polynomial on every SAT decider (`SATLower`). Per the separating-invariant interface
(`ComputationalDepthPvsNPSeparatingInvariant`), `PUpper R ∧ SATLower R L ∧ L ∈ NP ⇒ P ≠ NP`.

## 2. The arc, file by file (each machine-checked)

1. **`HolographicDynamicSPDP`** — first fixed-observer construction over the abstract `ClockedMachine`. Causal,
   decision-sufficient, `projectedInnovation ≤ runtime`, `PUpper` proved; `SATLower` left explicit.
2. **`HolographicDynamicSPDPInitNoGo`** — *fatal flaw exposed.* `ClockedMachine.init : List Bool → Config` is an
   uncharged arbitrary function, so `oracleInitMachine L` decides any `L` in zero charged steps ⇒
   `every_language_InP` ⇒ `PeqNP_in_model` ⇒ `SATLower` impossible for every `L`. The whole interface is vacuous
   until `init` is charged.
3. **`ChargedHolographicMachine`** — the repair. A genuine single-tape TM: finite states `Fin Q`, finite table
   `δ`, `init = (start, head 0, tape = input)` forced, one local transition per charged step, poly clock. `InP`
   redefined here is sound and complete for real `P`; the oracle-init cheat is blocked. Holographic layer rebuilt;
   `projectedInnovation ≤ clock`. Coverage flagged: an infinite-tape machine need not have a single finite global
   observer, so the cash-out targets `ObserverEquippedInP`.
4. **`ChargedLengthObserver`** — closes coverage *per input length*. `ReachablePoint M n = input × time`,
   `exists_lengthObserver` gives every charged machine a finite length-indexed observer. Carrier size
   `2^n·(clock n + 1)`.
5. **`ChargedLengthObserverCollapse`** — *first minimization no-go.* Under a terminal-decision-only contract the
   two-state observer "eventual answer" has zero innovation, so `universal_observer_lower_impossible`. Fix: require
   continuation/query sufficiency, not just the final bit.
6. **`ChargedContinuationQuotient`** — continuation/query sufficiency: `profile p : Query → Bool`, observational
   equivalence, intrinsic quotient `queryRank`. Blocks the final-bit collapse. But the **equality stress test**
   `eqProfile_rank = 2^n`, `eqProfile_not_polyBounded`: raw quotient cardinality fails `PUpper` on EQUALITY (a `P`
   language). So the candidate cannot be static quotient cardinality.
7. **`ChargedDynamicQueryInnovation`** — the dynamic repair: count profile *changes along the trace*
   (`profileInnovation ≤ clock` ⇒ `dynamicQueryResource_polyBounded`, `PUpper` for every scheme). Equality's
   time-invariant profile has `2^n` static profiles but dynamic innovation `0`.
8. **`ChargedDynamicQueryCollapse`** (audit) — *the dynamic measure also collapses.* A time-invariant scheme
   (`answerSemantics`, `Query = Unit`) has innovation `0`, so `universal_dynamic_lower_impossible`. Sharper:
   `richSemantics` is rich (2^n input-separating profiles, `richScheme_distinguishes`, not the final-bit collapse)
   yet still dynamic-`0` (`richScheme_dynamic_zero`). So **richness ≠ nonzero innovation**; the missing ingredient
   is time-variation.
9. **`ChargedCanonicalQueryAudit`** — the other horn. The maximally-rich canonical scheme (every predicate on the
   carrier) has innovation `= clock` *exactly* (`canonical_profileInnovation_eq_clock`,
   `canonical_schemeResource_eq_clock`), because the carrier includes charged time. Not a new mechanism: its
   `SATLower` is precisely a charged-time lower bound; padding-sensitive.
10. **`ChargedDynamicSPDPCapstone`** (this arc's close) — `charged_dynamic_notInP`: for any scheme assignment,
    `SATLower ⇒ L ∉ charged-P`, `PUpper` discharged. `charged_dynamic_padding_sensitive`: two machines decide the
    same language with different canonical resource — the clock-horn measure is not a language invariant.

## 3. The two-horn boundary (the load-bearing conclusion)

For the charged dynamic query-profile measure, over the space of admissible query schemes:

* **Collapse horn** — a *time-invariant* scheme (even a rich, input-separating one) has innovation `0`. Quantified
  over all schemes, `SATLower` is impossible (`universal_dynamic_lower_impossible`).
* **Clock horn** — the *maximally time-sensitive* canonical scheme has innovation `= clock` exactly
  (`canonical_schemeResource_eq_clock`), so its `SATLower` is `SAT ∉ P` verbatim, and it is padding-sensitive
  (`charged_dynamic_padding_sensitive`).

Query richness is orthogonal to time-variation, so no intermediate invariant is forced by richness. A surviving
separating measure would have to be simultaneously time-varying (to avoid collapse), simulation-invariant (to
quotient harmless padding), and `≤ runtime` (for `PUpper`) yet super-polynomial on SAT. A simulation-invariant,
`≤ runtime`, super-poly-on-SAT measure *is* `SAT ∉ P`; and "quotient harmless padding" = minimum over
padding-equivalent machines = the min-over-machines/decompositions quantifier.

## 4. Where this connects (and where the real traction is)

This is the same socket the earlier **observer-boundary programme** maps (`CookLevinFrontierHyp`): high boundary
under *every* decomposition for SAT. See `SCOPE_OBSERVER_PROGRAMME_CAPSTONE.md`. The dynamic-SPDP arc is a
distinct, fully-charged road to that identical wall.

The only components with *proven* content are the restricted min-realized rungs of the observer-boundary
programme, where the min-over-decompositions quantifier is discharged in a structured class:
`ComputationalDepthMinBoundaryRealized` (`minProofSpaceBoundary ≥ c·t` for expander-Tseitin) and
`ComputationalDepthObserverBlockDecompositionMin` (`minBlockBoundary ≥ 2^b − 1` for address-block families), plus
the three calibrations rederiving AC⁰[p] / Nečiporuk / communication bounds through the boundary invariant.

## 5. Honest status

The charged dynamic-SPDP framework is a **correct, fully-charged, machine-checked reduction** of "SAT ∉ P" to a
`SATLower` obligation, with `PUpper` discharged and both trivial extremes proven to fail. It is the honest version
of what the collapsed `ClockedMachine` model only pretended to be. It does **not** prove `SATLower`, and by the
`≤ runtime` ceiling plus padding-sensitivity it cannot yield leverage beyond an unrestricted charged-time lower
bound for SAT. The productive continuation is not another query scheme (the pincer kills any general one) but the
restricted min-realized rungs above. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
