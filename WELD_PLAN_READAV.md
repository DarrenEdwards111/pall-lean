# Weld plan — the halting separate-region `read a_v` machine

Actionable spec for the multi-turn build that welds the proven components into **one halting
`ComposableMachine`** computing `a_v`.  All components below are already machine-checked (branch
`razborov-recoverRho-wip`); this document fixes the marker scheme, the master-machine phase structure, the loop,
and the correctness chain so the remaining build is deterministic, not exploratory.

## 0. Target

```lean
def readAvMachine : ComposableMachine.Machine := …          -- the welded machine
theorem readAv_inP : ComposableMachine.InP readAv           -- readAv x = the a_v of a well-formed x
```
where `readAv` extracts `a_v` from a well-formed doubled encoding of `(v, assignment)`, and correctness bottoms out
on `CookLevinReadAv.readAv_spec` (already proved: `v` rounds of the delete/delete round land `a_v` at position 1).

## 1. The doubled encoding and the marker scheme (DECIDED)

Data bit `b ↦ b b` (pairs `00`/`11`, cells **equal**).  Markers are **differing** pairs (`01`/`10`), which can
never occur in doubled data (`CookLevinDoubled` proves data pairs read equal).  Three roles are needed; only two
single-pair markers exist, so exactly one role is a **composite** (two pairs):

**REFINED (see `CookLevinScanLeftSep`):** the loop is **anchored at `SEP`**, not at a left sentinel.  Each round
checks the pair *left of `SEP`* (`11` ⇒ counter, `10` ⇒ done) and deletes the pairs flanking `SEP`; deleting the
*rightmost* counter cell decrements the unary counter identically to the leading one (`readAv_spec` net transform
unchanged).  So `LSENT` is a **single** `10` checked locally at the loop control — **no composite marker, no
2-pair-lookahead walk-left**.  S6 is just a scan-left to the single `SEP = 01`.

| role | pattern | moves under shifts? | detection |
|---|---|---|---|
| `LSENT` left end (counter-empty test) | `10` (single) | no | pair left of `SEP` differs (`10`) vs `11` |
| `SEP` separator (counter ‖ assignment) | `01` (single) | yes | pair differs, `c₀=0,c₁=1` |
| `REND` right end (shift stop) | `10` (single) | yes | pair differs, `c₀=1,c₁=0` |

Encoding of `(v, assignment)`:
```
LSENT · (11)^v · SEP · (a₀a₀)(a₁a₁)…(a_m a_m) · REND
= (1 0 1 0) · (1 1)^v · (0 1) · encodeD(assignment-bits, doubled, cell-per-cell) · (1 0)
```
Key facts (all provable from `CookLevinDoubled` style lemmas):
- Only `LSENT` and `REND` contain `10`; `LSENT` is the unique **double** `10`.  `SEP` is the unique `01`.
- Counter pairs are `11` (equal); assignment pairs `a_i a_i` are `00`/`11` (equal).  **No marker appears inside
  data**, so every detection below is unambiguous.

## 2. Why each detection is unambiguous (the load-bearing check)

- **Loop control** (read the pair right after `LSENT`): `11` ⇒ counter present ⇒ do a round; `01` ⇒ `SEP` ⇒ counter
  empty ⇒ read result.  `11` is data-equal, `01` differs — distinct.
- **Shift termination** (a rightward shift stops at `REND`): the shift starts at a position `≥` the deleted pair
  (never left of it), so it never meets `LSENT`; it passes `11`/data (equal) and `SEP=01` (`c₀=0`), and stops only
  at `10` (`c₀=1,c₁=0`) `= REND`.  Distinct.
- **Walk-left to `LSENT`**: walking left it passes data (equal), `SEP=01`, and single `REND=10`; it stops only at
  a `10` **whose left neighbour pair is also `10`** — the `LSENT` double.  A single `10` (`REND`) has a data pair
  to its left, so it is skipped.  Needs 2-pair lookahead in the walk.
- Shifts move whole pairs by whole pairs (`PairShift.run_shift2`: `new[p]=old[p+2]`), so `SEP`/`REND` stay intact
  as `01`/`10` pairs; `LSENT` never moves.

## 3. Loop structure

```
loop:  head at LSENT
       read the pair right after LSENT
       | 11 (counter)  → ROUND ; goto loop
       | 01 (SEP)      → READ_RESULT
ROUND: (a) delete the leading counter pair  = pair-shift-left-by-2 from (LSENT+1) to REND
       (b) scan right to SEP
           delete a₀                        = pair-shift-left-by-2 from (SEP+1) to REND
       (c) walk left to LSENT
READ_RESULT: read the pair right after SEP → a_v ; HALT
```
This is exactly `CookLevinReadAv.roundStep` in doubled form: (a) deletes the leading `1`, (b) deletes `a₀`; after
`v` iterations the pair after `SEP` is `a_v` (`readAv_spec`).

## 4. Sub-machine inventory

Built ✓ (reuse directly), remaining ☐:

| # | sub-machine | status | phases | spec |
|---|---|---|---|---|
| S1 | doubled encoding + `data_eq`/`marker`/`firstMarkerD` | ✓ `CookLevinDoubled` | — | detection lemmas |
| S2 | scan to first marker, self-halt | ✓ `CookLevinScanMarker` | 3 | `scan_halt` (→ finds `SEP`) |
| S3 | self-halting write pass | ✓ `CookLevinClearMarker` | 5 | (not on critical path; technique donor) |
| S4 | pair-shift by 2 (run-lemma) | ✓ `CookLevinPairShift` | 5 | `run_shift2`, `lsTape2_shifted` |
| S5 | **REND-terminating** pair-shift | ☐ | 5 + halt | shift-by-2, halt when source pair `= 10`; upgrade S4 with a `10`-check in `GRAB` (compare the two source cells) |
| S6 | **walk-left to LSENT** | ☐ | ~4 | move left; halt at a `10` whose left pair is `10` (carry the last pair, 2-lookahead) |
| S7 | loop-control read + dispatch | ☐ | ~2 | read pair after LSENT; branch on equal/`01` |
| S8 | read-result | ☐ | ~2 | read pair after SEP into accept, halt |

Remaining low-level machines: **S5, S6, S7, S8** — all bounded, ≤ ~5 phases each, ≈ 150–250 lines with proof
(each mirrors an existing one: S5 = S4 + S2's compare; S6 = S2 reversed with 2-lookahead; S7/S8 = ScanMarker-style
reads).

## 5. The master machine

One `Machine` with `State = (tag : Fin 8) × PhaseState`, where `tag` selects the current phase-group
(`LOOPCTRL, SHIFT1, SCANSEP, SHIFT2, WALKLEFT, READRES, HALT`) and `PhaseState` carries the active sub-machine's
local state (its own small `Fin` × carry/stored bits).  `δ` is the disjoint union of the sub-machines' `δ`s, with
**seams**: when a sub-machine reaches its halt/boundary state, `δ` rewrites the state to the next group's start
(tape untouched at the seam — the switch is a control-only step, exactly like `comp`'s `(inr start, none, reset)`).
The head is *not* reset at seams (each group is written to start from where the previous left off — `WALKLEFT`
ends at `LSENT`, `LOOPCTRL` reads there, etc.).

Non-vacuity is preserved: finite `State` (product of finite parts), forced init, local `δ`.

## 6. Correctness chain

Three layers, each a separate lemma:

1. **Per-sub-machine** (S5–S8): run-lemmas on well-formed sub-configs (as S2/S4 already are).  E.g.
   `shift1_correct : run … = ⟨REND-halt, …, tape after deleting leading pair⟩`, proved by `run_shift2` +
   `lsTape2_shifted` up to the REND index (which `= 2·(current counter+assignment length)`, computed from the
   encoding).
2. **Per-round** (the seam-composition): one full `ROUND` transforms the doubled tape as `encodeD∘roundStep` does
   the raw tape — i.e. deletes the leading counter pair and the `a₀` pair.  Proved by `run_add`-chaining the
   sub-machine run-lemmas across the seams, then a `getD`-level lemma "doubled-shift = `roundStep` on the decoded
   list".
3. **Whole run** (the loop): by induction on `v`, `v` rounds bring the pair after `SEP` to `a_v`, invoking
   `readAv_spec` for the arithmetic (`a_v = assignment.getD v`).  Then `READRES` reads it; `run_stable` lifts to
   the poly clock.

Clock: each round is `O(current length)` steps (a scan + two shifts + a walk, each linear); `v` rounds ⇒
`O(v · |x|) = poly(|x|)`.  `PolyBounded` via the `polyBounded_time_comp`-style closure already proved.

## 7. Totality / `Decides` — the honest open point

`Decides` needs halting on **all** inputs.  On a **well-formed** encoding every phase self-terminates at its
marker, so the machine halts.  On a **malformed** input (missing markers) a scan/shift runs into the `00` padding
forever ⇒ not total.  Options, to decide when welding:
- (a) **Promise/precheck**: a first pass validates the encoding (itself terminating only if a final marker exists —
  same problem, unless a length-marker bounds it).
- (b) **Encode the length**: prefix a unary length block delimited by `LSENT`, and bound every phase by walking a
  copy of it — makes totality provable but adds a counter sub-machine.
- (c) **Scope as a promise-machine**: prove `HaltsBy`/correctness only for `x ∈ range encode`, and fence totality
  as the interface to M2 (which produces only well-formed inputs).  This is the honest minimum and matches how the
  components are already stated (run-lemmas on `encodeD bs`).

Recommendation: build under (c) first (correctness on well-formed inputs), then revisit (b) if a total `InP`
membership is required downstream.

## 8. Build order (each a turn)

1. **S5** REND-terminating pair-shift + `shift1_correct`/`shift2_correct` (delete-a-pair, halting).
2. **S6** walk-left-to-LSENT + its halt lemma.
3. **S7 + S8** loop-control read and read-result (small).
4. **Master machine** state/δ + the seam lemmas (control-only steps).
5. **Per-round** lemma (seam-composition = `roundStep` on the decoded list).
6. **Whole-run** induction + `readAv_spec` + clock + `Decides`/`InP` (under promise (c)).

Estimated ~6 turns, ~800–1200 lines.  No hardness content anywhere — this is TM engineering with every termination
obstacle already solved by the marker scheme (§2).  Nothing in this plan or its build is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
