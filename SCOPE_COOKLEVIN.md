# Scope — formalizing `CookLevin` over `ComposableMachine.InP` (paper first)

Target: `CookLevin (SATV : NPObs) := ∀ L, NPLang L → PolyReduces L (acceptBool SATV)` — every NP language
many-one reduces to the boundary of a **concrete SAT verifier**.  This is the genuine NP-hardness half of
Cook–Levin.  This memo lays out the construction over the faithful `ComposableMachine` model, maps the bricks,
checks circularity (against the refuted `CookLevinFrontierHyp`), and gives an honest feasibility verdict **before**
any Lean is attempted.

## 0. What the statement unfolds to

`NPLang L` gives an `ob : NPObs` with `L x = true ↔ AcceptNP ob x`, where
`AcceptNP ob x := ∃ w, |w| ≤ ob.wb |x| ∧ ob.verify (x ++ w) = true`, and `ob.verify` is in P
(`ptime : ComposableMachine.InP ob.verify`), so it is decided by some `Mᵥ` with poly clock `Tᵥ`.

`acceptBool SATV x := decide (AcceptNP SATV x)` for the concrete SAT verifier.  So `CookLevin SATV` demands a
**poly-computable** `f` (a `ComposableMachine` transducer) with, for every `ob`,

```
(∃ w, |w| ≤ ob.wb |x| ∧ ob.verify (x ++ w) = true)  ↔  AcceptNP SATV (f x).
```

## 1. The two genuine sub-mountains

**(M1) A concrete SAT verifier in P.**  `SATV.verify` must be a real `List Bool → Bool` decided by a
`ComposableMachine` in poly time — i.e. a CNF-evaluator TM: decode `(formula ‖ assignment)` off the tape, iterate
clauses/literals, output the conjunction.  In the faithful low-level model this is a genuine ~hundreds-of-lines TM
program **with a correctness proof** (the model is non-vacuous precisely because you cannot cheat a language into P;
you must build the machine).  No hardness content — purely constructive.

**(M2) The tableau reduction.**  Given `ob` (hence `Mᵥ, Tᵥ, wb`), build `f x` = a CNF `φ_{x}` whose satisfiability
is equivalent to `∃ w (|w| ≤ wb|x|)`, `Mᵥ` accepts `x ‖ w` within `Tᵥ(|x|+wb|x|)` steps.  Then compose with an
encoder so `AcceptNP SATV (f x) ↔ Satisfiable φ_x`.  This is the classic tableau:

* **Space/time bounds.**  `B := Tᵥ(|x| + wb|x|)` steps; by `run_bounds`, head `≤ |x|+wb|x|+B` and tape length
  `≤ |x|+wb|x|+B+1 =: P`.  Both poly in `|x|`.
* **Variables.**  For `t ∈ [0,B]`: cell bits `c[t][p]` (`p ∈ [0,P]`); head one-hot `h[t][p]`; state one-hot
  `s[t][q]` (`q ∈ Mᵥ.State`, finite).  Plus the witness bits `w[j]` (`j < wb|x|`) as the free inputs at `t=0`,
  positions `|x|..|x|+wb|x|`.
* **Clauses.**  (init) `t=0` matches `init Mᵥ (x ‖ w)` with `x` hard-wired and `w[j]` free; (transition) for each
  `t`, the triple `(s[t],h[t],c[t]) → (s[t+1],h[t+1],c[t+1])` is consistent with `Mᵥ.δ` and `moveHead`/`writeAt`
  (a **local** window constraint — the crux); (accept) `⋁_q (s[B][q] ∧ Mᵥ.accept q ∧ Mᵥ.halt q)`.
* **Correctness (both directions).**
  * `(⇐)` an accepting run on `x ‖ w` gives a satisfying assignment (read off the trace; local checks hold by
    `run_succ`).  The backbone is `run_eq_of_localCheck` (built below): the run is the *unique* locally-valid trace.
  * `(⇒)` a satisfying assignment reconstructs, by induction on `t` using the transition clauses, a valid run that
    halts-accepting on `x ‖ w` for `w` read off the free bits — so `Mᵥ` accepts, i.e. `verify (x‖w)=true`.
* **Poly transducer.**  `f` must *emit* `φ_x` on a tape as a `ComposableMachine`, and this emission must be poly
  time with a proof.  The formula has `O(B·P·|State|)` clauses — poly — but writing it as a genuine TM transducer
  with a length/΄time bound proof is itself substantial.

## 2. Circularity check (vs. the refuted `CookLevinFrontierHyp`)

The memory/audits found `CookLevinFrontierHyp` **circular / P-vs-NP-strength** (it effectively assumed the
separation).  The tableau content here is **not**:

* (M1) and (M2) are **explicit constructions**; their correctness statements are **true theorems provable by
  construction**, quantifying over *all* machines/assignments.  Neither implies nor assumes `SAT ∉ P`, `P ≠ NP`, or
  any lower bound.  Cook–Levin is a theorem of ZFC, machine-checkable in principle (done in Coq's Undecidability
  Library for the call-by-value λ-calculus model).
* The one honest "socket" temptation to **avoid**: defining `SATV.verify` as a *universal simulator* so the
  reduction is trivial.  That would be defining an NP-complete problem by fiat — **not** SAT, and the exact
  vacuity the user's memory flags (`package ⟺ ¬SAT-in-P`).  Faithful Cook–Levin **requires** `SATV.verify` to be
  the concrete, non-universal CNF-satisfaction check.  So M1 is mandatory and cannot be shortcut.

Conclusion: this is genuine constructive content, not a hardness restatement.  But it is **large**, and there is no
shortcut that stays faithful.

## 3. Feasibility verdict (honest)

* Mathlib has **no** Cook–Levin and **no** generic TM→SAT tableau.
* Comparable faithful formalizations (Coq Library of Undecidability, Gäher–Kunze) are multi-person, multi-month
  efforts, and they fix a *convenient* machine model.  Our `ComposableMachine` has an **arbitrary `Type` `State`**
  (only `Fintype`), which makes the one-hot state encoding and the transition-window clauses genuinely fiddly, and
  the **poly-transducer-output** obligation (M2's emitter) is a second correctness mountain the abstract audits
  usually wave away.
* Verdict: **full sorry-free `CookLevin` is not a session-scale task** (it is a genuine research-formalization
  project, both M1 and M2).  Per standing rules, I will **not** fake it with a `sorry`, an axiom, or a circular
  socket.

## 4. What gets built now (genuine, sorry-free, non-circular)

Not the mountain — the honest first bricks that any tableau rests on, with no hardness content:

1. **CNF/SAT semantics** — `Lit`, `Clause`, `Formula`, `evalFormula`, `Satisfiable`.  The object M2 must emit and
   M1 must evaluate; standalone and reusable.
2. **Local-checkability backbone** — `run_eq_of_localCheck`: any config sequence starting at `init` with each
   successor `= step` **is** the run.  This is the precise fact that makes "`Mᵥ` accepts" a *local* (per-step)
   constraint — the mathematical reason a computation compiles to a CNF.  Plus `run_isLocalCheck` (the run itself
   satisfies the local constraints).  Both genuinely provable.

These do not by themselves prove `CookLevin`; they are its honest foundation, and they make the remaining
mountains (M1 emitter/evaluator, M2 tableau correctness) precise.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

## 5. The full `read a_v` two-pointer shift loop (paper algorithm + brick status)

Directed: build the full variable→value lookup.  Pressure-tested; it is a nested-loop `O(v·n)` **shift**
construction, because the tape is Boolean (§1, M1): a mark cannot be a fresh third symbol.

**Layout.** `1ᵛ 0 a₀ a₁ … aₘ` (unary index `v`, separator `0`, assignment).  Goal: output `a_v`.

**Algorithm (delete/shift).** Repeat `v` times: delete the leading `1` (shift the whole suffix left one), then
delete the assignment cell just right of the separator (shift its suffix left one).  After `i` rounds the tape is
`1^{v−i} 0 a_i a_{i+1} …`; after `v` rounds it is `0 a_v a_{v+1} …`, so `a_v` sits one right of the separator —
read it.  Each delete is an inner left-shift pass (`O(n)`); `v` rounds ⇒ `O(v·n)`.

**Boundary subtlety (the hard part).** Consuming counter cells to `0` makes the "first `0`" ambiguous with the
separator; the delete-and-shift avoids a third symbol but forces the inner copy-left pass and careful re-location
of the (moved) separator each round.

**Brick status.**
* ✔ **Evolving-tape invariant technique** — `run_clear`/`clear_correct` (this file): a run-invariant over a tape
  rewritten every step (`zeroPrefix`), with reusable `writeAt_getD_ne`/`_self`, `getD_append_repl`.  This is the
  proof method every shift pass needs.
* ✔ **Atomic write / addressing** — `markMachine.mark_correct`, `readAtUnary.readOut_encode`.
* ☐ **Inner left-shift pass** — a machine that deletes cell `q` (copy `q+1→q`, `q+2→q+1`, …); needs the
  evolving-tape invariant above plus a two-cell "carry" state.  Not built.
* ☐ **Outer `v`-round loop** + separator re-location + `O(v·n)` clock.  Not built.

The technique (evolving-tape invariant) and the two atomic operations (read-at-address, write/mark) are in place;
the remaining work is the inner shift pass and the outer loop that composes them — a genuine construction, no
hardness content.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
