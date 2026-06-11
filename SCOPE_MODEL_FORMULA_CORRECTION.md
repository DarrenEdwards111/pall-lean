# Honest correction — the `Circuit` model is a FORMULA model (no gate sharing)

**Surfaced while probing the Khrapchenko measure (Layer 10D).  This affects how Layers 8–10 must be read.
The theorems are all true; several *labels* overclaim and are corrected here.**

> **RESOLVED (option 2): `ComputationalDepthLayer11DagCircuit.lean`** builds the genuine **DAG / straight-
> line circuit model** with gate sharing (`DagCircuit`, `eval`, `size` = #gates, fan-out free).  Over it,
> `Ppoly_dag` is the *real* `P/poly`, and the bridges `np_not_subset_ppoly_dag` / `p_ne_np_of_np_hard_dag`
> have `hPsub : P ⊆ PpolyClass_dag` = the **true** standard `P ⊆ P/poly` (not `P ⊆ NC¹`).  Sharing is shown
> real: `parity3Dag` computes `parityFn 3` with **8 gates**, below its `n²=9` formula bound.  Layers 8–10
> remain valid **as formula / `NC¹` results** (read per the table below); Layer 11 is the circuit-model
> version for the `P/poly` framing.

---

## The fact

`Layer8.Circuit` is an inductive tree, and its size double-counts shared subterms:

```
size (and c d) = c.size + d.size + 1
```

Writing `and c c` costs `2·size c + 1`, not `size c + 1`.  There is **no gate sharing / fan-out > 1**.
Therefore `size` measures **formula leaf/gate size**, not DAG/circuit size.  A genuine general circuit
(`P/poly`) is a *DAG* (straight-line program) where a gate's output feeds many gates at unit extra cost —
the model here cannot express that.

## What this means, layer by layer (theorems stay true; reading changes)

| As labelled | Should be read as |
|---|---|
| Layer 8 "general circuit lower bounds" | **formula** lower bounds |
| `SIZE n s` ("size-`≤s` circuits") | size-`≤s` **formulas** |
| Layer 8 Shannon (`exists_function_needing_exp_size`) | most functions need **formula** size `≈ 2ⁿ/n` |
| Layer 8 linear bound (`andAll_needs_linear_size`) | a **formula** for AND needs `≥ n` leaves |
| Layer 9 `Ppoly` ("`P/poly`") | **poly-size formulas** = nonuniform **`NC¹`** (Spira) |
| Layer 10C monotone circuits | monotone **formulas** |
| Layer 10D Khrapchenko `n²` | a real **formula** lower bound for PARITY (correct in this model) |

The mathematics is unaffected — every theorem is a true statement *about this (formula) model*.  Formula
size `≥` circuit size, so these are genuine but **weaker** bounds than the corresponding circuit bounds.

## The one place the framing was materially wrong: Layer 10B

`Layer10.p_ne_np_of_np_hard` takes `hPsub : P ⊆ PpolyClass` and calls it "the standard inclusion
`P ⊆ P/poly`".  But `PpolyClass` here is **poly-size formulas ≈ `NC¹`/poly**, so `hPsub` is really
**`P ⊆ NC¹`** — which is *open and widely believed false* (e.g. `P`-complete problems are believed not in
`NC`).  So:

* The bridge theorem is still **logically valid** (it is an implication).
* But its hypothesis is **not** the harmless true fact it was described as — it is likely *false*, which
  makes that particular bridge much weaker than advertised (a false premise implies anything).
* The genuinely useful half — `not_ppoly_of_observerHyp` / Bridge 1 (`an explicit hard language ⇒
  NPpoly ⊄ NC¹`) — remains meaningful as a *formula/`NC¹`* statement, just not a `P/poly` one.

## Recommended fix (honest options)

1. **Relabel** (cheap, honest): rename `Circuit → Formula`, `SIZE → formulaSIZE`, `Ppoly → NC1poly`
   throughout Layers 8–10, and restate the bridges as connecting *formula/`NC¹`* lower bounds.  The
   `P ≠ NP` bridge then correctly requires the **circuit** model, which this code does not have.
2. **Build the real circuit model** (substantial): a DAG / straight-line-program `Circuit` with shared
   gates and DAG-size, redo `SIZE`/`Ppoly` over it.  Only then is `P ⊆ Ppoly` the true standard inclusion
   and the route to `P ≠ NP` correctly modelled.  Shannon counting then needs the straight-line count
   (already used in `…ShannonCount` R1b for the *bound*, but the *model* there is still the tree).

Until one of these is done, **read Layers 8–10 as formula / `NC¹` results**, and treat the Layer 10B
`P ⊆ P/poly` hypothesis as the (open, dubious) `P ⊆ NC¹` rather than a standard fact.

## Why this is in the record, not quietly patched

Per project discipline (never certify a false framing): the overclaim — formula presented as general
circuit, `NC¹` presented as `P/poly` — is surfaced explicitly rather than silently relabelled, so the
prior commit messages and docstrings are corrected by this note on the record.
