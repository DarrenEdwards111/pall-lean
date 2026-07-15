# Scope — the tableau **emitter transducer** (`EmitsTableau`) as a multi-turn sub-project

Target (stated in `ComputationalDepthCookLevinEmit.lean`):

```
EmitsTableau M clock :=
  PolyComputable (fun x => encodeFormula (tableauReduction M x (clock x.length)))
```

i.e. an actual `ComposableMachine` transducer that, on input `x`, writes the bit-encoding of the tableau
`tableauReduction M x (clock|x|)` onto its tape and halts in polynomial time, with a correctness proof.

This is the **only** remaining gap in Cook–Levin M2.  Everything the emitter's output must satisfy is already proved
(both directions of correctness, unconditional; poly output size; a faithful poly-length codec).  What is missing is
the **machine that computes the output from the input** — a second M1-scale construction.  This memo pressure-tests
its architecture, identifies a decision that removes the largest arithmetic mountain, inventories the bricks (and
which existing M1 bricks are reusable), states the correctness obligations, and gives an honest turn-by-turn plan.

Per standing rules: this is a **plan**, not a claim of completion; the emitter is genuine constructive content with
no hardness/circularity, and it will be built brick-by-brick with `#print axioms ⊆ {propext, Classical.choice,
Quot.sound}` and no `sorry` — or not at all. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

## 0. What must be emitted

`tableauReduction M x clock = fullTableau M x (|x|+clock) clock`, and
`fullTableau = initFormula ++ headFamily ++ stateFamily ++ tapeFamily ++ dynamicsFamily ++ acceptFormula ++
writeFamily` (associativity aside).  Each family is a `bigAnd` (flatten) of clauses indexed by ranges:

| family      | index tuple                    | per-tuple clause(s)                              |
|-------------|--------------------------------|--------------------------------------------------|
| init        | `p ∈ [0,P]` (+ 2 fixed)        | unit clause `cell[0][p] = x[p]` / state / head    |
| headOneHot  | `t ∈ [0,B]`                    | 1 at-least-one (`P+1` lits) + `O(P²)` at-most-one |
| stateOneHot | `t ∈ [0,B]`                    | 1 at-least-one (`card` lits) + `O(card²)` pairs    |
| tape        | `t < B`, `p ∈ [0,P]`           | `cellCopyClause` = 2 clauses (3 lits each)         |
| dynamics    | `t<B`, `q<card`, `p≤P`, `b∈{0,1}` | 2 clauses (4 lits each)                        |
| write       | same as dynamics               | 1 clause (4 lits)                                  |
| accept      | —                              | 1 at-least-one over accepting-halting states       |

So the output is a **nested counter loop**: for each family, for each index tuple, emit a small **fixed-shape
template** with the current counter values spliced in.  With `B = clock|x|`, `P = |x|+clock`, `card` a machine
constant, the number of tuples — hence output length — is polynomial (already proved: `tableauReduction_length_le`).

**Input-dependence.**  Only `initFormula`'s cell fixes carry actual bits of `x` (`cell[0][p] = x.getD p false`).
Everything else depends on `x` **only through `|x|`** (via `B`, `P`).  So the emitter is: a mostly `|x|`-driven
fixed-structure generator, plus an `x`-bit splicer for the init cells.

---

## 1. The decisive architectural choice — an emitter-friendly codec (kills per-variable arithmetic)

The published codec `encodeFormula` serialises a literal's variable as the **unary integer** `3·Nat.pair(t,p)+tag`.
A machine emitting that must compute `Nat.pair` (a squaring/branch) and `×3` **for every variable** — poly-many
on-tape multiplications.  On a Boolean tape with no end marker this is the single largest mountain.

**Decision (brick E0).**  Use a *coordinate* codec `encodeFormula'` that serialises each variable by its triple
`(t, p, tag)` (three unary blocks) instead of the packed integer, with a **pure** decoder
`decodeFormula'` that reconstructs the ℕ-variable `3·Nat.pair(t,p)+tag`.  Then:

* `encodeFormula'` is well-defined on any `Formula` (recover `(t,p,tag)` from a variable `v` via
  `Nat.unpair (v/3)`, `v%3` — pure); `decodeFormula'` inverts it (`Nat.pair`, `×3`, `+tag` — pure).
* `decodeFormula' (encodeFormula' φ) = φ` (faithfulness — same style as the proven
  `decodeFormula_encodeFormula`).
* **The emitter never computes `Nat.pair`.**  When its loop emits `headVar t p`, it *already holds* `t`, `p`, and
  `tag = 1`; it writes those unary counters.  The pair-arithmetic lives only in the pure decoder.
* Correctness still composes: `Satisfiable` is a property of the abstract `Formula`, and
  `decodeFormula' (emitter output) = tableauReduction …`, so
  `Satisfiable (decode' output) ⟺ M halts-and-accepts` via the existing `tableauReduction_correct`.  (The M1 SAT
  verifier consuming this output tests variable identity by coordinate-tuple equality — also no `pair`.)

**Residual arithmetic after E0.**  Only the *loop bounds*: `B = clock|x|` and `P = |x|+clock` require evaluating the
**one fixed polynomial** `clock` on `|x|` — a single bounded arithmetic subroutine (brick E2), not per-variable work.
This is the whole difference between infeasible and a genuine project.

> This choice must be made **before** the machine, because it determines whether E2 is "evaluate one polynomial"
> or "multiply poly-many times."  It is faithful, non-circular, and provable now as the first brick.

---

## 2. Tape discipline and the input-delimitation obstacle

* **Two regions.**  Keep a *work region* (the nested counters `t, p, q, b` and the bounds `B, P`) and grow an
  *output region* by appending.  Because the tape is a single `List Bool` with no separator symbol, the boundary
  needs the **doubled/marker discipline already built for M1** (`...CookLevinDoubled`, `...ScanMarker`,
  `...ClearMarker`): a composite marker distinguishes work-cells, output-cells, and counter boundaries.
* **Input delimitation (same M1 wall).**  Reads past `|x|` return `false`, so the emitter cannot detect where `x`
  ends by scanning alone — exactly the obstacle the `read a_v` machine faced.  Reuse the M1 resolution: assume the
  faithful **doubled input encoding** with an end sentinel (promise-form, as in `readAv_encoded`), or first run the
  M1 self-delimiter.  The emitter is therefore built **under the same promise** as M1 (well-formed doubled input);
  totality is fenced identically.

---

## 3. Brick inventory

Legend: ✅ reusable from M1 as-is · ♻ M1 technique, re-instantiated · ★ new.

**Arithmetic / counters**
* ✅ `writeAt_getD_self` / `_ne`, `getD_append_repl`, evolving-tape invariant (`zeroPrefix`, `run_clear`).
* ♻ **E1 unary counter ops** — increment (append `1`), copy-with-preservation, compare (`≤`) two unary counters.
  Copy/compare are scan+write passes; the shift/scan machinery is M1's (`DeleteShift`, `ScanMarker`).
* ★ **E2 poly-clock evaluator** — a machine computing `clock|x|` and `P = |x|+clock` on the tape.  `clock` is one
  fixed `PolyBounded` function; evaluating it is add + a bounded number of unary multiplications
  (`mul a b` = `a` repeated additions, an evolving-tape nested loop).  The **only** genuine arithmetic mountain, and
  it is bounded (one polynomial, poly-time).  *Fallback:* parameterise the emitter by a supplied clock bound to defer
  E2 and isolate the loop machinery first.

**Codec (pure — buildable now)**
* ★ **E0 coordinate codec** `encodeFormula'` / `decodeFormula'` + `decodeFormula'_encodeFormula'` faithfulness +
  poly length bound.  Mirrors the proven `...CookLevinEmit` codec; ~1 turn, no machine.

**Loop / emission**
* ★ **E3 template emitter** — for each clause shape (unit / at-least-one / at-most-one pair / guardedIff / implClause)
  a routine that appends its fixed skeleton with the current counters spliced as coordinate blocks.  Fixed finite
  control per template; the work is the counter-copy (E1) and the append discipline (§2).
* ★ **E4 nested-loop harness** — compose the counters into the 7 family loops with correct bounds and termination
  (`t≤B`, `p≤P`, `q<card`, `b∈{0,1}`), sequencing the families.  This is the emitter's "master machine," analogous
  to the M1 master (`...CookLevinMaster` + group-sim lifts + round invariants).
* ★ **E5 x-splicer** — for the init cell fixes, read `x.getD p` (M1's addressed read, `readAtUnary`) and emit the
  matching unit clause value.

**Packaging**
* ✅ `run_bounds`, `run_stable`, `Nat.find` first-halt, `PolyBounded` closure (`polyBounded_comp_clock`).
* ★ **E6 correctness + clock** — `transOut M_emit x = encodeFormula' (tableauReduction …)` (a per-family emission
  spec glued to E0 faithfulness) and a `PolyBounded` clock (output poly-size — proved — × per-cell bounded work).

---

## 4. Correctness obligations (what each brick must prove)

1. **E0**: `decodeFormula' (encodeFormula' φ) = φ`; `(encodeFormula' φ).length ≤ poly` (coordinate blocks are
   `≤ B`/`≤ P` long — still poly; re-do `encodeFormula_length_le` for the coordinate form).
2. **E3/E4/E5 emission spec**: the run's output tape, after the loops, **equals** `encodeFormula' (fullTableau …)` —
   proved family-by-family (each loop emits exactly that family's clause-encodings, by a run-invariant induction over
   the counters, the M1 `run_two_j`/round-invariant pattern) then concatenated.
3. **E6 top**: `Transduces M_emit (fun x => encodeFormula' (tableauReduction M x (clock|x|))) T_emit` with
   `PolyBounded T_emit`; hence `PolyComputable`, hence `EmitsTableau'` (the coordinate-codec form of the target).
4. **Bridge to `EmitsTableau`**: either restate the target with `encodeFormula'` (cleanest — the codec is a free
   design choice), or prove the two codecs inter-convertible by a poly transducer (extra work; avoid).

---

## 5. Honest turn-by-turn plan and effort

| turn(s) | brick | risk |
|---------|-------|------|
| 1       | E0 coordinate codec + faithfulness + length (pure) | low |
| 2–3     | E1 unary counter ops (incr/copy/compare) on doubled tape | med (M1 machinery) |
| 4–6     | E3 template emitters for the 5 clause shapes + emission specs | med |
| 7–10    | E4 nested-loop harness (7 families) + per-family run-invariants | **high** (master-machine scale) |
| 11      | E5 x-splicer for init cells (reuse `readAtUnary`) | med |
| 12–14   | E2 poly-clock evaluator (or defer via supplied-bound fallback) | **high** (only real arithmetic) |
| 15–16   | E6 glue: emission spec + `PolyBounded` clock + `Transduces` | med |

**Estimate:** ~15 turns / ~2000–3000 lines — comparable to, and somewhat larger than, the M1 `read a_v` arc
(`WELD_PLAN_READAV.md`), because the emitter's master loop nests 7 families and grows an output region.  E2 is the
one irreducible arithmetic component; E4 is the one irreducible master-machine component.  Neither has a faithful
shortcut, but both are ordinary constructive TM programming — no hardness content.

**Sequencing rule:** build E0 first (locks the codec decision, all pure, de-risks everything downstream); then E1/E3
(local, testable); then E4 (the hard integration); E2 last or via the supplied-bound fallback so the loop machinery
is validated before the arithmetic.

---

## 6. Circularity / faithfulness check

* The emitter is a pure **construction**; `Transduces M_emit f T` is a true theorem provable by building `M_emit`.
  It quantifies over all `x`; it neither assumes nor implies `SAT ∉ P`, `P ≠ NP`, or any lower bound.
* The coordinate-codec (E0) is faithful (`decode' ∘ encode' = id`) and is a serialisation choice only — it does not
  change which formula is emitted, only its bit-layout.  No "universal simulator" shortcut is used (that is the
  vacuity trap `SCOPE_COOKLEVIN.md §2` flags); the emitted object is the concrete tableau CNF.
* Everything the emitter's **output** must satisfy is already proved: `tableauReduction_correct` (unconditional
  `Satisfiable ⟺ accept`), `tableauReduction_length_le` (poly size), `decodeFormula_encodeFormula` (faithful codec).
  The emitter adds only the input→output **computation**.

---

## 7. Feasibility verdict

The emitter is a **genuine research-formalization sub-project**, not session-scale — the same verdict
`SCOPE_COOKLEVIN.md §3` gives for full Cook–Levin, now localised to its single remaining component.  It has **no
faithful shortcut**, but it is decomposed above into ordinary constructive bricks, most of whose *techniques* (and
several of whose *lemmas*) already exist from the M1 arc.  The decisive de-risking is **E0**: the coordinate codec
removes per-variable `Nat.pair` arithmetic and reduces the machine's arithmetic to one poly-clock evaluation.

**Buildable now (next turn), pure and complete:** E0.  **The rest** is the M1-scale machine work, to be built
brick-by-brick under the same well-formed-input promise as M1, each sorry-free and axiom-clean, or reported as an
honest wall if a brick resists.  The observer-class `CookLevin` fence stays undischarged until E6 lands.
