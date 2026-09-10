# pall-lean

Lean 4 formalization of OBDD width lower bounds for Tseitin formulas on expander graphs.

## Revision audit: the selector-to-SAT objection (2026-09-10)

The [revision audit](research-audits/nframe-fixed-invariant/GodMoveDiscoveryRevisionAudit.md)
confirms that the new discovery uses a supplied correct SAT machine. This is
valid under a hypothetical polynomial-time SAT decider in a contradiction
argument, and the original selector-to-SAT implication still holds. Lean
checks the semantic round trip and proves that the revision's derived
guarantees do not restrict that hypothetical decider further.

A concrete rejecting machine satisfies the numerical bounds but fails sample
correctness, showing why the SAT-correctness premise cannot be dropped. The
independent superpolynomial wire-rank lower bound remains unproved; discovery
does not amplify rank or establish separation.

## Discovery through a supplied SAT machine (2026-09-10)

The [machine discovery continuation](research-audits/nframe-fixed-invariant/GodMoveMachineDiscovery.md)
replaces the abstract discovery oracle with exact arithmetic circuits, actual
CNF encodings, and clocked calls to a supplied correct SAT machine. It returns
separating samples and exact basis wires without an assignment scan. Lean
derives polynomial request counts, coefficient bit bounds throughout discovery,
and query sizes; a supplied polynomial SAT clock also bounds each query's
machine steps. The same machine can discover a basis for its own unrolled
computation, capturing the SAT decision polynomial.

Correctness still assumes the supplied machine decides SAT. Full construction
runtime, complete gauge certificate construction, and the requested
superpolynomial SAT lower bound remain unproved. This does not establish
`P ≠ NP`. Earlier continuation reports below record their respective stages.

## Adaptive discovery with an explicit oracle (2026-09-10)

The [adaptive continuation](research-audits/nframe-fixed-invariant/GodMoveAdaptiveDiscovery.md)
constructs separating samples and exact basis wires using at most
`(s+1)*(n+1)` predicate-existence oracle calls for an `s`-gate circuit on `n`
inputs. Exact rational residuals supply the semantic counterexample witnesses.
The oracle's implementation and cost remain external; this is not a
polynomial-time discovery theorem.

A separate theorem proves a `2^n` lower bound for exact adaptive testing using
only scalar output queries, with circuit descriptions and internal wires
unavailable. That restricted query bound is not a SAT runtime lower bound.
Efficient unrestricted discovery and the requested superpolynomial SAT lower
bound remain unproved.

## Executable sample and basis discovery (2026-09-10)

The [discovery continuation](research-audits/nframe-fixed-invariant/GodMoveExecutableDiscovery.md)
implements exact rational selection from actual Boolean circuit-wire values.
It constructs separating assignments and selects independent wire columns that
span the entire computed-wire polynomial space. Their number equals the exact
wire rank. The resulting SAT program has verified language-level correctness
without a supplied sample selector.

Discovery still scans all `2^n` Boolean assignments. The small returned lists
do not establish polynomial runtime. A separate refinement theorem bounds
successful counterexample steps by the gate count, while leaving the search
for each counterexample unbounded. Efficient general discovery, complete gauge
certificate construction, and a superpolynomial SAT lower bound remain unproved.

## Explicit sampled gauge construction (2026-09-10)

The [sampled gauge continuation](research-audits/nframe-fixed-invariant/GodMoveGaugeConstruction.md)
defines a production projection directly from supplied basis wires, Boolean
samples, and a finite inverse matrix. Its executable evaluator reads actual
circuit wires, and Lean proves that separating sample lists exist with at
most one sample per gate.

Efficient discovery remains unresolved: the verified sample-selector reduction
already supplies a SAT solver. A separate four-gate construction proves that
one exact wire-rank increment detects satisfiability. Small sample lists and finite matrix arithmetic
do not establish an efficient way to find the required samples and spanning
basis. The production minimizer obstruction remains, and no superpolynomial
SAT lower bound or `P ≠ NP` result is claimed.

## Production gauge and SAT lower-bound continuation (2026-09-10)

The [production connection](research-audits/nframe-fixed-invariant/GodMoveProductionConnection.md)
realizes computed-wire rank exactly in the existing production gauge type and
derives a genuine `N-22` lower bound for every circuit deciding the encoded SAT
input slice. The gauge minimizes the existing action among candidates explicitly
required to preserve all computed wires; efficient projection construction and
a superpolynomial SAT lower bound remain unproved.

The unrestricted minimizer requirement has a stronger obstruction: for
nonnegative weights and a positive rank weight, every global minimizer of
`FullLagrangianFixed` has rank bounded by the ratio of its barrier and rank
weights. With both weights one, every minimizer is the zero
projection. Even the existing unit-preserving refinement permits a rank-at-most-two
gauge fixing any chosen output. These results do not establish `P ≠ NP`.

## Rank-connection continuation (2026-09-10)

The [rank continuation](research-audits/nframe-fixed-invariant/GodMoveRankConnection.md)
proves that the span of actual circuit wires gains at most one dimension per
gate, that normalization cannot increase this span's rank, and that the
machine clock supplies a polynomial upper bound. Under SAT correctness, the
same construction captures the SAT decision polynomial over encoded inputs.
Boolean finite differences also recover the normalized target's derivative
rows exactly.

The missing lower-bound transport remains unresolved: Lean proves that those
derivative rows cannot always fit inside the bounded wire span. It also proves
that every fixed CNF verifier target has a small circuit and that the easy
product already maximizes the strict zero-shift rank. These results constrain
the proposed connection; they do not establish a SAT lower bound or `P ≠ NP`.

## Compact machine-circuit connection (2026-09-10)

The [new circuit connection](research-audits/nframe-fixed-invariant/GodMoveCircuitConnection.md)
constructs one shared machine circuit over a symbolic pinned-SAT input, without
enumerating assignments in the source representation. Lean proves its actual
clocked-run semantics, polynomial gate/DAG/storage bounds, verified bit-codec
roundtrip, and exact equality of its Boolean-normalized polynomial with the
verifier characteristic under SAT correctness.

The rank-bounded extraction remains unproved. Actual linear-size Boolean
circuits already disprove a generic polynomial characteristic-rank bound, and
a three-gate circuit shows Boolean normalization can increase the existing
projected derivative rank. The new work does not establish `P ≠ NP`.

## God-Move gap-repair update (2026-09-09)

The desktop paper's product-encoding and common-span steps are being checked
without changing the production invariant. See
[GodMoveGapRepairs.md](research-audits/nframe-fixed-invariant/GodMoveGapRepairs.md)
for the checked constructions, their exact scope, and reproduction commands.
The original common-span premise is false for the current raw product compiler;
the corrected placement-sensitive bound does not complete its P-side budget.
**The P versus NP separation remains unproved.**

A subsequent [semantic handshake](research-audits/nframe-fixed-invariant/GodMoveHandshake.md)
connects actual faithfully encoded SAT-query outputs to a Boolean verifier
polynomial with equal SPDP rows and ranks, assuming faithful SAT correctness.
Its explicit common-span bound is
exponential, not the polynomial bound required for separation.
A [matched calibration](research-audits/nframe-fixed-invariant/GodMoveCharacteristicCalibration.md)
constructs a compact product and binomial identity minor for the easy unit-CNF
target, and proves unsatisfiable characteristic targets have zero rank.
Neither establishes the missing general-SAT separation construction.
Further [characteristic-target checks](research-audits/nframe-fixed-invariant/GodMoveCharacteristicNextStep.md)
prove that ignored witness padding cancels exactly and that exact midpoint
evaluation recovers the number of satisfying assignments.

## Proved lower bounds — capstone ledger

For a machine-checked, honestly-scoped inventory of the restricted-class circuit / formula / proof-space
lower bounds proved in this repo — separating what is **proved unconditionally** from what is
**conditional, open, or equivalent to `P ≠ NP`** — see the master ledger:

- **[PRIME_ACC0_CAPSTONE.md](PRIME_ACC0_CAPSTONE.md)** — the index (proved-vs-conditional tables).

Each capstone re-exports its arc's results under citable names, every one `#print axioms`-verified to depend
on only `[propext, Classical.choice, Quot.sound]` (no custom axioms, no `sorry`):

| Capstone | Result | Status |
|---|---|---|
| [Prime `AC⁰[p]`](PRIME_ACC0_CAPSTONE.md) — `…ACC0PrimeCapstone` | `PARITY / MOD_q ∉ AC⁰[p]` (Razborov–Smolensky) | complete |
| [Nečiporuk](NECIPORUK_CAPSTONE.md) — `…NeciporukCapstone` | `Ω(N²/log N)` De Morgan formula size | complete + ceiling |
| [Switching-lemma](SWITCHING_CAPSTONE.md) — `…SwitchingCapstone` | Håstad switching bound (`hnf` regime) | partial (tight-general open) |
| [Forster](FORSTER_CAPSTONE.md) — `…ForsterCapstone` | sign-rank `≥ n/‖·‖`, Walsh UPP `≥ k/2` | complete (circuit-app fenced) |
| [Tseitin proof-space](TSEITIN_SPACE_CAPSTONE.md) — `…TseitinSpaceCapstone` | resolution proof-space `Ω(\|V\|)` | restricted |

These are genuine restricted-class results. **None is `NEXP ⊄ ACC⁰` or `P ≠ NP`**; the ledger states
precisely why each stops where it does.

## Active Proof Chain (Route 2: Tseitin/OBDD)

The main result: **no polynomial-width OBDD computes the Tseitin clause-subset
satisfiability function on expander graphs** (`tseitin_not_poly_obdd`).

All theorems fully proved — 0 sorry, 0 axioms. Two standard graph-theoretic
conditions (`HasGoodCut`, `HasSatisfiablePrefixes`) are provided as hypotheses,
satisfied by known expander families.

### Core files (all clean ✅)

| File | What | Lines |
|------|------|-------|
| `MUSWidthLowerBound.lean` | OBDD width from distinct residuals | ✅ |
| `SearchToOBDDBridge.lean` | Bridge: search complexity → OBDD width | ✅ |
| `TseitinOBDD.lean` | Main theorem: Tseitin exponential OBDD width | ✅ |
| `TseitinDefs.lean` | Regular graph definitions, Tseitin encoding | ✅ |

### Proof architecture

```
HasGoodCut (hypothesis)          HasSatisfiablePrefixes (hypothesis)
         │                                │
         ▼                                ▼
greedy_independent_split ──► tseitin_parity_residuals
         │                        │
         ▼                        ▼
private_edges_from_independent   width_from_many_residuals
                    │                    │
                    ▼                    ▼
              tseitin_obdd_width ◄───────┘
                    │
                    ▼
            exp_exceeds_poly
                    │
                    ▼
           tseitin_not_poly_obdd
```

### Hypotheses (conditions on the graph)

1. **`HasGoodCut G c`** — The graph has a cut with ≥(d+1)·c split vertices
   and every vertex has a right-side edge. Follows from edge expansion
   (Jukna, *Boolean Function Complexity*, Ch. 8).

2. **`HasSatisfiablePrefixes G labels k hk`** — For even-parity labels,
   every prefix assignment extends to a satisfying completion. Follows from
   GF(2) linear algebra and spanning tree elimination.

### Open frontier

The real proof value now lives in:
- **Proving the expander support package** (HasGoodCut from edge expansion)
- **Proving GF(2) satisfiability** (HasSatisfiablePrefixes from linear algebra)
- **Lifting from OBDD to general poly-time** (the L vs P question)

## Paper-faithful God-Move branch note

On branch `godmove-paper-faithful`, there are multiple paper-facing routes and
historical shells in the tree.

The important paper-faithfulness correction is:

- the desktop paper `p-vs-np1.pdf` presents two genuine routes
- Route A: direct separation on an explicit NP witness family
- Route B: the Global God-Move route
- the paper treats **Route B / God-Move as primary**

The **active imported Lean route today is not that primary Route B shell**.
The active imported route is the latent compiler route:

- `PallLean/LatentCompiler.lean`
- `PallLean/LatentWidthRankDecomp.lean`
- `PallLean/LatentWitnessMinorDecomp.lean`
- `PallLean/LatentCompilerFinalRoute.lean`

The active entrypoint is [PallLean.lean](/tmp/pall-lean/PallLean.lean), and the
active final contradiction theorem is:

- `LatentCompilerFinalRoute.P_neq_NP_latent_decomp`

So the honest route classification on this branch is:

- faithful to a real paper route: yes
- specifically closest to the paper's direct-separation shell / Route A: yes
- fully faithful to the paper's overall emphasis, where Route B is primary: no, not yet

This route is axiom-free in Lean syntax but still conditional on an explicit
paper-facing assumptions bundle:

- NP-side data: now built canonically inside the active route
- P-side obligation: `latent_profile_assembly_logscale` (profile-assembly Width⇒Rank bound)

For the current honest status summary, see:

- [PROOF-OBLIGATIONS.md](/tmp/pall-lean/PROOF-OBLIGATIONS.md)
- [SORRY-INVENTORY.md](/tmp/pall-lean/SORRY-INVENTORY.md)

Older paper-numbered files such as `Separation29.lean`,
`SeparationAssembly.lean`, and the God-Move wrappers remain useful for
orientation, but they are not the current imported route.

Files carrying the paper's primary Route B / God-Move intent are still in the
tree:

- `PallLean/PaperFaithfulSeparation.lean`
- `PallLean/GodMoveCore.lean`
- `PallLean/GodMoveReal.lean`

Those should be read as the paper-faithful Route B frontier, not as the branch's
current active final shell.

## Route 1 files (archived/exploratory)

The `MobiusBridge`, `TracedMobiusBridge`, `CoupledCompiler`, `ProfileDecomp`,
`NPViolationLowerBound`, `ExtractionWiring`, and `SearchPSide` files are from
an earlier approach via Möbius coefficients and SPDP rank. That route identified
a fundamental gap: Möbius mass alone does not separate P from NP (unit clause
SAT is in P but has superpolynomial Möbius mass). These files are retained as
historical branches but are not on the active proof path.

## Building

```bash
lake update
lake build
```

Requires Lean 4.28.0 and Mathlib.
