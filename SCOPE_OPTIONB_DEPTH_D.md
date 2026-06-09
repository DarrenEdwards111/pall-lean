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

---

## UPDATE 3 — [169] width-tracking: the architectural fork, scoped precisely

[169] needs the bottom `DNF` to have width `≤ w` (so the terminal [165] applies). The existing width
invariant is threaded by `collapseRound_BottomWidth`, but **`collapseRound`/`leafCollapse` are
bit-level**: `leafCollapse (dnf cs) = cnf (dtreeToCNF (toDTree (canonicalDT cs F ρ)))`. So collapsed
width is governed by `canonicalDT` depth, while route 2 produces `canonicalDTree` depth. Two paths:

### Path (i) — the depth bridge `canonicalDT.depth ≤ canonicalDTree.depth`  [PROBED — HARD]

The project's own comments assert this is **true** (manifest:1391 *"depth_canonicalDTree ≥
depth_canonicalDT; equality is FALSE in general"*) but it is **not formalized**, and manifest:1536
calls it *"the remaining substantial"* piece they routed around (via the generic parity bound in
`TightParity`). Probing it: the recursions are structurally mismatched —
- `canonicalDT` reads **one free literal per fuel unit** (same term stays active, recurse at `fuel-1`);
- `canonicalDTree` reads **the whole term's free vars per fuel unit** (`queryAll`, recurse at `F-1`).

So the proof needs an auxiliary induction matching `canonicalDT`'s per-literal descent across a full
term to `canonicalDTree`'s per-block step, with fuel accounting (`canonicalDT` needs `~|T|` fuel where
`canonicalDTree` needs 1). This is a genuine multi-lemma induction, not a bounded probe. **Deferred.**

### Path (ii) — block `collapseRoundBlock` [RECOMMENDED, mechanical, multi-file]

Build a block collapse operator from the already-built per-gate block collapses
(`collapse_or_layer_at` / `collapse_and_layer_at`, used in [162]/[163]): every clause it emits has
width `< s` directly from `canonicalDTree`-shallowness — no bridge. Mirror, block-level:
1. `leafCollapseBlock` (the 4 `Layered` cases via `canonicalDTree`/`dtreeToCNF`) — mirror `LeafCollapse`.
2. `collapseRoundBlock := mergePass ∘ leafCollapseBlock` (`mergePass` is tree-agnostic, reused).
3. `collapseRoundBlock_EquivOn` / `_AltO` (mirror; structure identical) / `_BottomWidth` (width `< s`
   from block shallowness — the per-gate fact is in [162]/[163]).
4. Then `parity_not_altO_block_width_aware` (mirror `parity_not_altO_width_aware`) drives the block
   engine [166] with a block `ShallowsBlock` predicate, discharging `hterm` for free at the bottom DNF.

This reuses [162]–[168] and avoids the bridge; the cost is ~3–4 new mirror files. **This is the
realistic completion of [169].**

### State at this checkpoint
Structural core [165]–[168] built + pushed. [169] scoped to path (ii) (mechanical, multi-file) or
path (i) (one hard induction). [170] schedule + [171] concrete instance follow. AC⁰ ceiling throughout.

---

## UPDATE 4 — [169] COMPLETE via path (ii), no bridge

Path (ii) (block `collapseRoundBlock`) is fully built — the depth bridge (i) was **not** needed:

| brick | what | status |
|---|---|---|
| [169a] `leafCollapseBlock` + `_EquivOn` | block leaf collapse (`canonicalDTree`, no `toDTree`) | ✓ clean |
| [169b] `collapseRoundBlock` + `_EquivOn` | `mergePass ∘ leafCollapseBlock` | ✓ clean |
| [169c] `ShallowsBlock`, `_BottomWidth` | block round preserves bottom width (via generic `dtreeToCNF_width`/`dtreeToDNF_width`) | ✓ clean |
| [169d] `collapseRoundBlock_AltO`/`_AltA` | drops one alternation level (verbatim structural mirror) | ✓ clean |
| [169e] `parity_not_altO_block_width_aware` | **width-aware general-`d` block bound — [169] capstone** | ✓ clean |

The whole depth-`d` block lower bound now reduces to a **single per-round block survivor**:
`hsurv : ∀ C τ, BottomWidth w C → s ≤ stars τ → ∃ ρ, Extends τ ρ ∧ s ≤ stars ρ ∧ stars ρ < F ∧
ShallowsBlock w F ρ s C`. No `canonicalDT ↔ canonicalDTree` bridge appears anywhere.

### Remaining ladder
- **[170] discharge `hsurv` + schedule** — apply the m-free conditional survivor [164] to
  `bottomGates C ∪ map negDNF (bottomGates C)` (both polarities of `ShallowsBlock`), leaving the
  **uniform per-base budget** (the schedule: deep-cap `<1` for every reachable `(C, τ)` at once). This
  is the genuine remaining analytic gate. *Risk: HIGH.*
- **[171] concrete unconditional depth-`d` instance** — the depth-`d` analog of [161], `norm_num`.
  *Risk: MED.*

The entire *structure* of the m-free depth-`d` AC⁰ bound is now built and verified (no bridge, no
`m`). What remains is purely the survivor discharge + schedule feasibility + a concrete instance.

---

## UPDATE 5 — [170] structure COMPLETE; reduces to ONE schedule hypothesis

| brick | what | status |
|---|---|---|
| [170a] `collapseRoundBlock_BottomClean` | well-formedness (`BottomClean`) threads the tower | ✓ clean |
| [170b] `parity_not_altO_block_width_aware_clean` | width-aware block tower carrying `BottomClean` | ✓ clean |
| [170c] `hsurv_block_round` | m-free per-round survivor on `bottomGatesG C` (both polarities) | ✓ clean |
| [170d] `parity_not_altO_block_findep` | **`hsurv` discharged — reduces to one schedule hypothesis** | ✓ clean |

The complete m-free depth-`d` block lower bound `parity_not_altO_block_findep` now follows from a
**single uniform schedule hypothesis** `hsched`: for every reachable `BottomClean`, width-`≤ w` tower
`C` and base `τ` with `s ≤ stars τ`,
`P[stars ≤ s-1 | extBox τ] + (bottomGatesG C).card · (r')^s/(1-r') < 1` (in unnormalised form).

### Remaining ladder
- **[171] discharge `hsched`** — the schedule feasibility, the genuine analytic gate: the conditional
  low-star tail via `stars_tail_le_extends`/`hsmall_of_chernoff` (Chernoff at threshold `s`), plus a
  gate-count bound `bottomGatesG_card_le` for the `card` factor. Then a concrete `(p,n,d,s,F,w)` and
  `norm_num`, the depth-`d` analog of [161]. *Risk: HIGH (the schedule), then MED (instance).*

Everything else — the entire m-free depth-`d` AC⁰ machinery — is now built and verified: no clause
count `m`, no `canonicalDT ↔ canonicalDTree` bridge. `hsched` is the last mathematical input.

---

## UPDATE 6 — [171] finding: `hsched` needs the VARYING geometric schedule (constant `s` can't close)

Probing the discharge of `hsched` against the bit schedule machinery (`h1_of_gap`,
`hsmall_of_chernoff`, `recursive_tower_not_parity_surv_seq`):

- The Chernoff gap that closes the low-star tail is **`7·sOut < stars τ · p`** (`h1_of_gap`): the
  *output* star threshold `sOut` must be comfortably below the *input* `stars τ`.
- **[170b–d] instantiated the block engine [166] at a CONSTANT `s`** (`fun _ => s`). With constant
  `s`, the recursion only guarantees `stars ≥ s`, so at the last round `stars τ` can equal `s`, making
  `P[stars ≤ s-1 | extBox τ]` large — the gap fails. This is the depth/star conflation.
- The bit version closes it with the **varying** engine `recursive_tower_not_parity_surv_seq` and a
  **geometric** schedule `s_i` (`ParityWidthAwareSeq` / `ParityWCSeq` / `geomSchedB`), keeping
  `stars τ_i` comfortably above `s_{i+1}` every round.

So the honest remaining work for [171] is the **m-free varying-schedule rework** — the core analytic
content brick 140 spent the most effort on, now m-free:

1. **[171a]** restate the block width-aware clean tower [170b] with a *per-round* threshold schedule
   `s : ℕ → ℕ` (the block engine [166] is already the seq version — I just passed it a constant). The
   m-free survivor [164] already takes separate depth/star thresholds, so this is a parameterization +
   the per-round `EquivOn`/width/clean threading at `s_i`.
2. **[171b]** the geometric schedule (`geomSchedB` analog) + per-round gap (`h1_of_gap` analog, base
   `4w+1`) + union bound, discharging the per-round `hsched_i`.
3. **[171c]** concrete `(p, n, d, schedule)` and `norm_num` — the depth-`d` analog of [161].

This is genuine multi-brick analytic work (HIGH risk), not a mirror: it is the m-free heart of the
Håstad schedule. Everything structural beneath it ([162]–[170d]) is built and verified. AC⁰ ceiling.

---

## UPDATE 7 — [171a–c] BUILT: schedule reduced to (pure gap) + (gate-count union)

The varying-schedule rework is built; the m-free depth-`d` block bound now reduces to two clean
conditions:

| brick | what | status |
|---|---|---|
| [171a] `parity_not_altO_block_width_aware_clean_seq` | the block tower on a *per-round* threshold `s i` | ✓ clean |
| [171b] `hsurv_block_REL2_round` | two-threshold survivor from the Chernoff gap + union bound | ✓ clean |
| [171c] `parity_not_altO_block_seq_findep` | **assembly: `hsurv` discharged, reduces to gap + union** | ✓ clean |

`parity_not_altO_block_seq_findep` now needs only:
- **`hgap`** — the *pure* schedule gap `7·s(i+1) < s i · p` (a condition on the sequence only; with
  `s i ≤ stars τ` it gives the Chernoff gap). Dischargeable by a **geometric** schedule
  `s(i+1) ≈ ⌊s i · p / 7⌋`, needing `s 0 ≈ (7/p)^d` (the standard Håstad regime).
- **`hunion`** — `card(bottomGatesG C) · (r')^{s(i+1)}/(1-r') < 1/2`. By `bottomGatesG_card_le`,
  `card ≤ 2·(bottomGates C).length`, so this needs the **number of bottom gates bounded** — i.e. a
  gate-count invariant threaded through the tower (brick 140's 4th invariant, `BottomCount`), not yet
  built block-side.

### Remaining ladder
- **[171d] gate-count invariant** — thread `(bottomGates C).length ≤ M` through `collapseRoundBlock`
  (mirror brick 140's gate-count thread), discharging `hunion` for `M·(r')^{s(i+1)} < 1`. *Risk: MED.*
- **[171e] concrete instance** — pick `p, n, d`, the geometric `s i`, and `M`; discharge `hgap`/`hunion`
  by `norm_num`; supply a width-`≤ w`, `BottomClean`, gate-count-`≤ M` depth-`(d+2)` tower. The
  depth-`d` analog of [161]. *Risk: MED.*

The Håstad schedule itself (the HIGH-risk gate) is now **built**: [171a–c] reduced it to a pure
schedule inequality plus a gate-count union. What remains is the gate-count thread + a numeric instance.

---

## UPDATE 8 — [171d–e] BUILT; conflation found: [171a–e] use ONE threshold for depth + star

| brick | what | status |
|---|---|---|
| [171d] `collapseRoundBlock_count_le` | block round doesn't increase the bottom-gate count | ✓ clean |
| [171e] `parity_not_altO_block_seq_count_findep` | all four invariants threaded; reduces to two pure schedule inequalities `hgap`/`huni` | ✓ clean |

[171e] is a clean, verified theorem reducing the whole m-free depth-`d` block bound to `hgap`
(`7·s(i+1) < s i·p`) and `huni` (`2M·(r')^{s(i+1)}/(1-r') < 1/2`), `i ≤ d`. **But it conflates the depth
and star thresholds into one sequence `s i`.** That single `s(i+1)` is simultaneously:
- the depth/shallowness threshold — capped `≤ w` by `hsw` (the bottom-width budget);
- the star-survival threshold — must be *large* for the gap `7·s(i+1) < stars τ·p`;
- the union exponent `(r')^{s(i+1)}` — must be *large* for `huni` to close.

Verified arithmetic (`p` minimal for `r'<1`, `M=1`, `w=2`): `huni` needs the threshold `≳ 3.2`, but
`hsw` caps it at `w=2` — **contradiction**. So [171e] is instantiable only in a weak regime (width
`w ≈ 128^d·log M`, exponential in `d`), not the genuine Håstad regime (small `w`).

### The fix: two-parameter decoupling (the genuine final piece)

Håstad keeps a **small depth threshold `t ≈ w`** (for the union and the bottom width) separate from a
**large star schedule `s_i`** (for the gap). The m-free survivor [164]
(`exists_shallow_survivor_extends_findep (F s k)`) *already takes separate depth `s` and star `k`
thresholds* — but [170c]/[171b]/[171a]/[171e] collapsed them (`k = s-1`, depth `= star`). The remaining
work decouples them:
- **[170c′]/[171b′]** — survivor with depth threshold `t` (`≤ w`, for `ShallowsBlock`/`huni`) and a
  *separate* star threshold `sOut` (large, for the gap). The bit `hsurv_REL2_round` is exactly this
  two-parameter form.
- **[171a′]/[171e′]** — the tower with a *constant* depth threshold `t ≈ w` and a *geometric* star
  schedule `s_i`. `ShallowsBlock` at `t`; `BottomWidth ≤ t ≤ w`; the gap on `s_i`.
- **[171f]** — concrete instance (now feasible: small `w`, `t = w`, geometric `s_i`, `n ≈ s_0`).

This is the genuine final structure. Everything beneath it ([162]–[171e]) is built and verified; the
decoupling is the m-free analog of brick 140's two-parameter (depth/star) form. AC⁰ ceiling.

---

## UPDATE 9 — DECOUPLING DONE + CONCRETE INSTANCE: option (b) closed at depth 3

| brick | what | status |
|---|---|---|
| [171b′] `hsurv_block_REL2_round_dt` | two-parameter survivor: depth `t` ⟂ star `sOut` | ✓ clean |
| [171e′] `parity_not_altO_block_seq_dt` | decoupled capstone: constant depth `t≤w`, geometric stars `s_i` | ✓ clean |
| [171f] `parity_not_depth3_block` | **CONCRETE unconditional m-free depth-3 bound, constant width 10** | ✓ clean |

`parity_not_depth3_block` is **fully unconditional** — no probabilistic/budget hypothesis:

> Every `AltO 3`, `BottomWidth 10`, `BottomClean`, `≤ 10^6`-bottom-gate tower over `n ≥ 490007001`
> variables, on a base `τ₀` with `≥ 490007001` stars, disagrees with parity somewhere.

Parameters `p=1/1000`, `w=t=10`, `M=10^6`, schedule `490007001, 70001, 10, …`; the gap closes strictly
(`490007 < 490007.001`, `70 < 70.001`) and the union `2·10^6·(82/999)^10/(1-82/999) < 1/2` by `norm_num`.
**Constant width (10), m-free, no `canonicalDT↔canonicalDTree` bridge** — the entire route-2 program
realised as a concrete depth-3 AC⁰ lower bound.

### What remains (optional polish)
- General-`d` instance: replace the explicit 3-value schedule with a closed-form geometric `s_i` (a
  `norm_num`-friendly recurrence) to get `parity ∉ depth-(d+2) AC⁰` for all `d` up to `~log n/log(7/p)`.
  The capstone [171e′] already supports it; only the schedule arithmetic is left. *Risk: MED.*

The m-free depth-`d` AC⁰ program is structurally complete and demonstrated unconditionally at depth 3.
Ceiling unchanged: AC⁰, not P vs NP.
