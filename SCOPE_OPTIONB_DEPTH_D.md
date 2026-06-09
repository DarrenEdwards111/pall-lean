# Scope: Route-2 Option (b) — m-free depth-`d` AC⁰ parity lower bound

**Goal of (b):** lift the m-free single-gate refutation ([158]/[161]) to a depth-`d` statement:
parity ∉ depth-`(d+2)` AC⁰, with all constants m-free and the parameter regime non-vacuous for
`d ≥ 1` (the regime where the existing m-ful tower, brick 140 `parity_not_altO_geomREL2`, collapses
to a vacuous bound).

**Honest ceiling (unchanged):** completing (b) closes Layer 2 (General AC⁰). The achievable depth in
the standard Håstad regime is `d = O(log n / log log n)`. Still AC⁰; not P vs NP.

---

## Key finding from scoping: (b) is a RETROFIT, not a greenfield build

The original framing ("need a `canonicalDTree`-compatible collapse layer; the existing machinery is
bit-level `canonicalDT`") is **outdated**. The block-level collapse glue already exists and is wired
to `canonicalDTree`. The seam is narrow and vertical.

### What already exists and is REUSABLE (parameter-agnostic, block-level)

These consume `(canonicalDTree g w F ρ).depth < s` and don't care where the budget came from — so
the m-free survivor [157] drops straight in:

| Lemma | File | Role |
|---|---|---|
| `collapse_or_layer_at` / `collapse_and_layer_at` | `LayerCollapseAt` | layer collapse, ρ given |
| `collapse_gAnd_dnf_at` / `collapse_gOr_cnf_at` | `GateCollapse` | whole-gate collapse, ρ given |
| `collapse_core` / `collapse_core_or` | `LayerCollapse` | semantic core |
| `Reduces.round` | `ReduceChain` | one-stage glue (via `EquivOn`) |
| `reduces_iterate` / `iterated_not_parity` | `IteratedReduction` | the `d`-fold chain |
| `tower_not_parity` | `TowerParity` | parity capstone |
| `canonicalDTree_depth_ge_of_parity` / `shallow_canonical_not_parity` | `CanonicalParity` | block-level parity lower bound |

### What is m-ful and must be re-derived m-free (the actual work)

Only the **budget-carrying producers** pay the `m`/`F`-dependent factor (via `exists_shallow_all`,
whose budget has the `card (Fin F → Option (Fin w → Option (Option Bool)))` factor). The whole
existing depth-`d` apparatus — `RecursiveTower*`, `ParityGeneralD`, `ParityWCSeq3`, brick 140,
`ParityDepth4Uncond` — is built on this m-ful budget, which is **exactly why it is vacuous for
`d ≥ 1`**.

| m-ful producer | m-free analog to build |
|---|---|
| `collapse_or_layer` (`exists_shallow_all`) | **[162] `collapse_or_layer_findep` ✓ DONE** |
| `collapse_and_layer` | [163] `collapse_and_layer_findep` |
| `one_round_or` | [164] `one_round_or_findep` |
| iterated assembly (m-ful schedule) | [165] m-free ρ-sequence → `iterated_not_parity` |
| `geomSchedB` schedule + per-round tails (brick 140) | [166] m-free geometric schedule |
| `parity_not_altO_geomREL2` (vacuous d≥1) | [167] concrete m-free depth-`d` instance |

### Why the BridgeNoGo does NOT block this

`blockStream_length_le_canonicalDTree_depth` (`BridgeNoGo`) proves `blockStream.length ≤
canonicalDTree.depth` — a *lower* bound, so the `blockStream` count cannot prove the tree shallow.
This is **sidestepped**: the m-free survivor [157] bounds `canonicalDTree.depth` **directly** via the
value-augmented descent count (`descent_switching_findep_le`), never through `blockStream`. The no-go
only kills the `blockStream` shortcut; the `canonicalDTree`-direct route (route 2) is unaffected.

---

## Brick ladder for (b)

- **[162] `collapse_or_layer_findep`** — m-free producing OR-layer collapse. ✓ **DONE** (commit
  d86e6353), clean axioms. Thin adapter: [157] → `collapse_or_layer_at`.
- **[163] `collapse_and_layer_findep`** — dual AND-layer (via `collapse_and_layer_at` + `negDNF`).
  *Risk: LOW* (mirror of [162]).
- **[164] `one_round_or_findep`** — the full round (`EquivOn` + width `< s` + freshness) used by
  `Reduces.round`. *Risk: LOW–MED* (mirror `one_round_or`, swap survivor + budget).
- **[165] m-free iterated assembly** — construct the per-round survivor sequence `ρ : ℕ → …` and the
  `EquivOn` chain, feed `reduces_iterate` / `iterated_not_parity`. `reduces_iterate` is
  parameter-agnostic, so this is sequence construction, not new structure. *Risk: MED*.
- **[166] m-free geometric schedule** — the real remaining analytic content: a star/width/depth
  schedule `(s_i, F_i, w_i)` with `w_{i+1} = s_i`, keeping `r'_i = (2p/(1-p))(4w_i+1) < 1` and the
  per-round star-tails small across all `d` rounds simultaneously. This re-derives brick 140's
  `geomSchedB` **without** the clause-count invariant `m` — one fewer invariant to track (alternation,
  width, gate-count remain), but the schedule feasibility must be re-proven m-free. *Risk: HIGH* —
  this is where the genuine multi-round work lives.
- **[167] concrete unconditional depth-`d` instance** — the analog of [161] for `d ≥ 2`: pick
  concrete `(p, n, d, schedule)` and discharge the per-round gap by `norm_num`. *Risk: MED* (norm_num
  over a `d`-fold product; heavier than [161] but same technique).

## Recommended order

[163] → [164] (finish the thin adapters, low risk, immediate progress) → [165] (assembly) → [166]
(the hard schedule rung — the true gate) → [167] (concrete finish). The first three rungs are
de-riskable now; [166] is the one that decides whether m-free depth-`d` actually closes.

*AC⁰ ceiling throughout; not P≠NP-strength.*

---

## UPDATE (after building [162]–[164]): the engine is budget-agnostic — only the terminal is the seam

Reading the existing general-`d` apparatus changed the picture again, in our favour:

- **`parity_not_altO` (ParityGeneralD) is already budget-agnostic.** It takes the per-round survivor
  `hround` and the terminal switching `hterm` as *abstract hypotheses*. `hround` is discharged
  **trivially** (`survivor_round_trivial`, needs only `n ≤ F`) — the per-round collapse `collapseRound`
  is `EquivOn` *unconditionally* (`canonicalDTree`/`canonicalDT` compute the layer exactly on the
  subcube; shallowness is NOT needed per round). `parity_not_altO_hround_discharged` already leaves
  **only `hterm`**.
- **So the m-ful-ness of the whole depth-`d` bound lives in exactly ONE hypothesis: `hterm`.**
  The m-free retrofit = discharge `hterm` m-free. This is far smaller than re-deriving the tower.

### The one real seam: `hterm` is BIT-LEVEL (`canonicalDT`); route 2 is BLOCK-LEVEL (`canonicalDTree`)

`hterm` (as `parity_not_altO` states it) asks for `(canonicalDT cs F σ').depth < stars σ'`. Route 2's
m-free count bounds `canonicalDTree`. **No depth bridge is needed** (`TightParity`: the relativized
parity bound is generic over `DTree n`, so the contradiction holds for either tree on its own). The
clean move is therefore to keep the terminal on **`canonicalDTree`** and use the block-level capstone
`iterated_not_parity` / `tower_not_parity` (which already terminate on `canonicalDTree`), rather than
`parity_not_altO`'s `canonicalDT` `hterm`.

### Revised remaining work (replaces [165]/[166] framing)

Two viable finishes, pick one:

- **B1 (recommended): m-free `hterm` on the block tree + block engine.** Discharge an
  m-free terminal `terminal_shallow_of_survivor_findep` producing `(canonicalDTree cs w F σ').depth <
  stars σ'` from the m-free conditional budget [164] (we already have `exists_shallow_survivor_extends_
  findep`). Then drive `iterated_not_parity` with the m-free rounds [162]/[164]. The schedule is the
  remaining analytic content (per-round `(s_i,F_i,w_i)`, `w_{i+1}=s_i`, all star-tails small at once),
  but with the `m` invariant already gone. *Risk: MED–HIGH (schedule feasibility).*
- **B2 (smaller, bit-level): port route 2's value-augmented count to `canonicalDT`.** Re-prove the
  [155b] injectivity for the single-literal tree, giving an m-free `canonicalDT` terminal that
  discharges `parity_not_altO`'s `hterm` directly and reuses the whole engine. *Risk: MED (re-derive
  one injectivity lemma) but bit-level, against the route-2 grain.*

**The honest gate is the same in both: an m-free survivor whose deep-cap stays `<1` across `d` rounds
simultaneously (the schedule). That is the genuine remaining mathematics; everything above it is now
either built or budget-agnostic.**

---

## UPDATE 2 — B1 structural core BUILT ([165]–[168])

The block-level path B1 is now built down to a single remaining input:

| brick | what | status |
|---|---|---|
| [165] `terminal_shallow_of_survivor_findep` | m-free block terminal on `canonicalDTree` (from [164] at `{cs}`) | ✓ clean |
| [166] `recursive_tower_not_parity_surv_seq_block` | block recursive-tower engine (reuses tree-agnostic chain) | ✓ clean |
| [167] `parity_not_altO_block` | general-`d` parity bound, block terminal | ✓ clean |
| [168] `parity_not_altO_block_hround_discharged` | `hround` discharged; **only the block terminal `hterm` remains** | ✓ clean |

So the depth-`d` block bound now follows from **one** input: a block terminal
`hterm : ∀ cs σ, s ≤ stars σ → ∃ σ', Extends σ σ' ∧ stars σ' < F ∧ (canonicalDTree cs w F σ').depth < stars σ'`.

### Remaining ladder to a concrete unconditional m-free depth-`d` bound

- **[169] width-aware block tower** — [168]'s `hterm` is quantified over *all* `cs`, but [165]
  discharges it only for `cs` of width `≤ w` (consistent, nodup). Need a width-tracking `Valid`
  invariant (mirror `ParityWidthAware` block-level) so the bottom `DNF` has width `≤ w`. *Risk: MED.*
- **[170] discharge `hterm` via [165] + uniform conditional budget** — for every base `σ` with
  `s ≤ stars σ`, the per-base budget `P[stars ≤ s-1 | extBox σ] + geom < 1` must hold (the conditional
  Chernoff, via `stars_tail_le_extends`). This is the **schedule feasibility** — the true analytic
  gate. *Risk: HIGH.*
- **[171] concrete unconditional depth-`d` instance** — pick `(p,n,d,s,F,w)` and discharge by
  `norm_num`, the depth-`d` analog of [161]. *Risk: MED.*

Everything from `hterm` upward (the entire tower, engine, oracle, collapse, parity capstone) is now
built and verified m-free. The remaining work is width-tracking + the schedule + a concrete instance.
