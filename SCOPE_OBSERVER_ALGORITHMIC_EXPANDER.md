# Observer + algorithm + expander + Williams — the combined conditional schema

This note describes the **second engine** added to the observer/God-Move programme: the *algorithmic* route
(Williams' direction), amplified by expander geometry.  It is **conditional and modular** — Ramanujan
expansion and Williams diagonalization are explicit hypotheses, never reproved here.  The value is wiring the
engines cleanly: **God-Move boundary → expander amplification → faster SAT → Williams lower bound.**

Files: `ComputationalDepthObserverAlgorithmicSchema.lean`, `ComputationalDepthObserverAlgorithmicExpanderSchema.lean`.

---

## The two complementary engines

The original observer programme proves lower bounds by forcing *high* boundary (God-Move: a hard instance
forces every faithful observer to large boundary; proved for expander-Tseitin proof-space and the
address-block forcing families).  Williams' route uses the *opposite*: a class with *low* boundary is
**algorithmically exploitable**, and a nontrivial algorithm yields a lower bound.  Combining them is HAL's
"second engine".

## The three pieces (modular, each isolated)

### 1. Observer → algorithm (PROVED core)

A low-boundary decomposition admits **dynamic programming over its `2^B` boundary states**: `stages` stages,
each costing `2^B` (one per boundary state), total `≤ stages · 2^B`.  This beats brute-force `2^n` whenever
`stages · 2^B ≤ 2^{n−1}` (i.e. `B + log₂ stages ≤ n − 1`).

* `ObserverAlgorithmic.dpSat_beats_bruteforce` — **proved**.  Same DP that solves bounded-pathwidth /
  bounded-width-branching-program SAT.
* `ObserverAlgorithmic.LowBoundaryInstance` / `.fast` — packages an instance and its proved sub-brute-force
  bound.

### 2. Expander amplification (EXPLICIT hypothesis)

The Ramanujan/expander geometry spreads local constraints globally, so a cheap decomposition cannot isolate
the hard part: a low-boundary observer either collapses distinguishable continuations or pays boundary
proportional to the expansion frontier.  Modelled as `ExpanderAmplifies → LowBoundaryDecomp` (the geometry
yields a *faithful* low-boundary decomposition rather than a local cheat).  **Not reproved**; the proved
instances of "pay the frontier" are the `ForcingFamily` results (§12) and expander-Tseitin (§8).

### 3. Williams (EXPLICIT hypothesis)

`FastSAT → (NEXP ⊄ C)`: a nontrivial SAT algorithm for a circuit class yields a lower bound (Williams
diagonalization, the `#SAT`-algorithm-to-lower-bound theorem).  **Not reproved.**

## The wiring (proved glue)

`expander_observer_williams_schema` : `amplify` (2) → `algorithm` (1) → `williams` (3) ⊢ `LowerBound`.

`expander_williams_with_proved_algorithm` : engine 1 **discharged** by the proved `LowBoundaryInstance.fast`,
so only engine 2 (expander) and engine 3 (Williams) remain as explicit hypotheses:

```
(amplify  : ExpanderAmplifies → LowBoundaryInstance) →
(williams : ∀ I, (dpSatTime I.stages I.boundary < bruteForceTime I.n) → LowerBound) →
 ExpanderAmplifies → LowerBound
```

## Honest status

* Engine 1 (DP / low boundary ⇒ sub-brute-force SAT): **proved**.
* Engine 2 (expander amplification): **explicit hypothesis** (`p vs np1` geometry; the forcing-family /
  expander-Tseitin results are its proved "pay-the-frontier" instances, but the full amplification for an
  arbitrary class is not reproved).
* Engine 3 (Williams): **explicit hypothesis** (deep theorem, not reproved).
* `NEXP ⊄ ACC⁰`, `NP ⊄ ACC⁰`, `P ≠ NP`: **open**.  This schema closes none of them.

**What this achieves.**  A clean, modular conditional that integrates the algorithmic (Williams) engine with
the God-Move boundary invariant and the expander amplifier — the `p vs np1` intuition, formalized as a wiring
with the algorithmic glue *proved* and the two deep inputs *named and isolated*.  It says precisely what each
engine must supply, without pretending any of the deep inputs is in hand.
