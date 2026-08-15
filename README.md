# pall-lean

Lean 4 formalization of OBDD width lower bounds for Tseitin formulas on expander graphs.

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

## Exact three-bit majority circuit budget

The repository also contains a fully kernel-checked exact result for the
three-input majority function in the unrestricted binary-gate `CGate` model:

- **[MAJORITY_CIRCUIT_CAPSTONE.md](MAJORITY_CIRCUIT_CAPSTONE.md)** —
  `majorityThreeFloor_cbudget_eq_seven` proves that the minimum wire count is
  exactly `7`.

The binary gates may compute arbitrary Boolean functions.  The proof gives a
seven-wire construction and excludes every six-wire circuit by compressing its
three genuine binary transitions into a finite semantic observer schedule.

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
