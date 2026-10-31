# Observer-Boundary Principle

## Purpose

This note records the P vs NP north-star for the N-frame observer programme. It is **not** a proof of `P ≠ NP`. It is the conceptual/formal target that the current ACC⁰ observer calculus is building toward.

The guiding idea is a computational version of holography:

> A hard search bulk is tractable for an observer exactly when the relevant satisfiability information factors through a small, efficiently accessible boundary state.

In this language:

- **Bulk** = the full witness/search space of an instance.
- **Boundary** = an observer-accessible compressed statistic.
- **Observer** = a constrained computational lens: support, switching, polynomial, residue, or ultimately polynomial-time.
- **Holography condition** = the decision predicate factors through the boundary.
- **Obstruction** = global witness holonomy that no allowed boundary captures.

## Polynomial Holography for NP Search

For a family of instances `φ ∈ I_n`, a polynomial observer-boundary consists of:

```text
B_n : I_n → Boundary_n
D_n : Boundary_n → Bool
```

with:

```text
SAT(φ) = D_n(B_n(φ))
```

where `B_n` is polynomial-time computable, `D_n` is polynomial-time computable, and the boundary has polynomially bounded representation size.

Equivalently, `SAT_n` factors through the observer boundary:

```text
SAT_n = D_n ∘ B_n
```

This is the observer-boundary / holographic form of efficient decision.

## P vs NP Translation

In this language:

```text
P = NP
```

would imply universal polynomial holography for NP search:

> every NP-complete witness bulk admits a polynomial-time observer-boundary from which satisfiability is recoverable.

Conversely:

```text
P ≠ NP
```

would follow from exhibiting an NP-complete family whose satisfiability predicate does **not** factor through any polynomial observer-boundary.

A theorem-shaped version:

```text
Observer-Boundary Separation Principle.
Let B_poly be the class of polynomial-time computable boundary maps
with polynomially bounded descriptions, and let D_poly be polynomial-time decoders.
If there exists an NP-complete language L such that for every B ∈ B_poly
and every D ∈ D_poly,

    L_n ≠ D_n ∘ B_n

for infinitely many n / all sufficiently large n,
then P ≠ NP.
```

N-frame phrasing:

> No polynomial observer-boundary fully captures NP witness holonomy.

Or:

> NP contains non-polynomially-holographic witness bulks.

## Relation to Current ACC⁰ Observer Work

The current ACC⁰ programme is building concrete observer modules below the full polynomial-time observer class.

### Support observer

Boundary:

```text
x ↦ x|_S
```

Captures functions depending only on a small support `S`.

Proved use:

- support normal form;
- junta / bounded-union-support SAT search.

### Switching observer

Boundary:

```text
restriction / subcube / decision-tree state
```

Captures AC⁰ collapse under random restrictions.

Proved use:

- switching probability tail;
- high-probability depth collapse;
- formal MOD no-go: switching does not force MOD gates unless their whole support is fixed.

### Polynomial observer

Boundary:

```text
low-degree span over F_p
```

Captures Razborov–Smolensky style AC⁰[p] approximants.

Proved use:

- N-frame holonomy parity equals ordinary parity;
- low-degree span obstruction;
- AC⁰[p] approximates into low-rank predictors;
- method capped at same-prime MOD_p via Fermat.

### Residue observer

Boundary:

```text
x ↦ (count_{S_j}(x) mod q_j)_j
```

Captures MOD and mixed-modulus residue compression.

Proved use:

- depth-2 MOD residue compression;
- operational residue machine;
- branched residue cost;
- restriction ⇒ surviving residue gates;
- AC⁰-over-MOD normalization;
- extraction of mixed observers from raw `ACC0Circuit` syntax;
- deduplicated state bound `modOcc C · 2^|varSupp C|` (vars counted once across leaves, `MOD`-internal vars absorbed into the residue) — `acc0_dedupObserved` / `acc0_dedup_searchable`.

## Why This Matters

The ACC⁰ work is not separate from the P vs NP programme. It is the training ground for the observer calculus.

Each proved observer module has the same shape:

```text
ObservedBy f stat
state bound on image(stat)
SAT reduces to searching observer states
obstruction or speedup follows from boundary size
```

The P vs NP target is the same pattern at maximum strength:

```text
ObservedBy SAT_n B_n
B_n polynomial-time computable
B_n polynomial-size / polynomial-boundary
```

and the desired obstruction is:

```text
no polynomial observer-boundary preserves NP-complete satisfiability.
```

## North Star

The N-frame claim, in its strongest P vs NP form:

> NP-complete search spaces contain global holonomy / consistency structure that cannot be compressed into any polynomial-time observer-boundary without reconstructing the witness bulk.

Equivalently:

> P = NP would mean universal computational holography for NP search. P ≠ NP says some NP witness bulks are non-holographic for polynomial observers.

This file is a roadmap principle, not a completed theorem. The immediate proof work remains incremental: continue strengthening the ACC⁰ observer calculus, especially normal-form/shrinkage results, before attempting the full polynomial observer-boundary class.
