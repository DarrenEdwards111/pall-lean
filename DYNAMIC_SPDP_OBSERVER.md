# Dynamic SPDP Observer

## Purpose

This note records a future P vs NP direction for the N-frame observer programme. It is **not** a current proof target and it is **not** a proof of `P ≠ NP`.

The current ACC⁰ work is building fixed and composable observer modules: support, switching, polynomial, residue, decision-tree, and oracle-control observers. A P vs NP-strength observer likely has to be stronger: adaptive over time.

## Core Idea

A polynomial-time algorithm can be viewed as an observer that evolves a bounded boundary state while interacting with a large witness/search bulk.

Static observer:

```text
x ↦ stat(x)
```

Dynamic observer:

```text
B_0 → B_1 → ... → B_T
```

where each update can reveal/query/add new directions or relations, and `T = poly(n)`.

In SPDP language:

```text
observer starts with a low-dimensional SPDP boundary
→ computation reveals or queries new directions
→ the SPDP basis/admissible span adapts over time
→ after T polynomial updates, decoder D reads B_T
```

The P vs NP-shaped obstruction would be:

```text
SAT_n ≠ D ∘ B_T
```

for every polynomial-length dynamic SPDP observer on some NP-complete family.

## Holographic Reading

This fits the observer-boundary principle:

- **static observer** = fixed low-dimensional projection;
- **dynamic observer** = adaptive sequence of projections/boundaries;
- **NP witness bulk** = high-dimensional search hypercube;
- **P vs NP obstruction** = even polynomially many adaptive boundary updates cannot recover the global SAT holonomy.

So the slogan is:

> NP-complete search may require witness-bulk holonomy that cannot be compressed by any polynomial-length dynamic SPDP boundary.

## Needed Formal Ingredient

This only becomes proof-relevant if it yields a monotone invariant:

```text
dynamic_SPDP_capacity(poly steps) < NP_holonomy_requirement
```

Without such an invariant, higher-dimensional / infinite-dimensional language is only metaphor.

A theorem-shaped future target:

```text
No polynomial-length dynamic SPDP observer factors SAT for an NP-complete family.
```

or:

```text
∀ dynamic observers B_T with T ≤ poly(n),
∀ poly-time decoders D,
SAT_n ≠ D ∘ B_T.
```

## Current Status

This is a north-star note, not today’s build target.

Immediate work remains the ACC⁰ observer calculus:

```text
observer algebra
→ ACC fragments
→ oracle-control / switching+MOD composition
→ shrinkage and speedup theorems
```

Dynamic SPDP should be revisited after the ACC observer machinery is mature enough to support adaptive boundary updates, state-count monotonicity, and lower-bound invariants.
