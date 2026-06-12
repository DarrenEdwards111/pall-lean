# Observer boundary entropy — a mathematical note

A reframing of the Route-F obstruction as **observer interface complexity** ("thermodynamic boundary of an
observer"), per the meta-complexity / branching-holography idea.  The aim: turn the metaphor into a concrete
complexity invariant, state the central conjecture precisely, and position it against known theory.

**Status.** The *invariant* and its basic laws are formalized and proved
(`ComputationalDepthObserverBoundary.lean`).  The *thermodynamic / spacetime-hypercube* language is
intuition, flagged as such.  The *central conjecture* is open and equal in strength to `P ≠ NP`; nothing
here proves it.

---

## 1. The invariant (rigorous)

For a deterministic machine and a cut, define the **observer boundary entropy**

  `B(M, cut) = log₂ |crossing sequences at the cut| ≤ C · log₂ A`

(`A` = size of the head/state alphabet, `C` = number of crossings).  An "observer" reading the computation
across the cut can retain only this much interface information.

**Proved (from the Route-F crossing-sequence bound `rank ≤ A^C`):**
* `log₂ rank ≤ B` (`rank_le_two_pow_boundaryEntropy`): boundary entropy upper-bounds the log of the SPDP /
  communication rank an observer can resolve.
* `B = O(log n) ⇒ rank = poly(n)` (`lowBoundary_poly_rank`): a low-boundary observer sees polynomial rank.

So this is a real quantity with real laws, **not** metaphor.

## 2. The P-observer / NP-observer picture

* **P-observer** — bounded boundary entropy `B = O(log n)`.  Sees the computation through low-rank,
  few-lane, few-crossing summaries (Route F: polynomial profiles).  By §1, resolves only `poly(n)` profiles.
* **NP-observer** — a *branching* boundary: it may expose all witness branches of the Boolean hypercube
  `{0,1}^n` at once.  Its witness boundary is `Ω(n)` (exponentially many faces/sectors).
* **Separation question** — can a P-boundary observer *compress* the NP branching boundary without losing
  decisive witness information?

This is exactly the Route-F question in new clothes: the P-side must force every SAT-decider into
low-boundary geometry.

## 3. Boundary *reuse* is the crux (this is what Route F exposed)

The decisive lesson from the formalized arc: the obstruction is **boundary reuse, not boundary size**.
`SpreadObstruction` proved that a small-space ("small-boundary") observer can *recycle* a tiny interface
`Θ(T)` times — generating large *temporal* crossing entropy from a small *spatial* boundary (the shuttle).
So the right invariant is **crossing entropy** (boundary × reuse), and "P-observer" must mean *low total
crossing entropy*, which a small-space machine can violate.

  P-style observer  :=  total crossing entropy `B = O(log n)`  (boundary size × reuse both controlled).

## 4. The central conjecture (open, `P ≠ NP`-strength)

> **Observer-boundary conjecture.**  For NP-complete families (e.g. SAT), *every* faithful deterministic
> observer has super-logarithmic total crossing entropy: `B = ω(log n)`.

By §1–§3 this is **equivalent** to the Route-F open lemma — the `T/log n` space (= spread) lower bound for
SAT — hence to an explicit super-polynomial circuit lower bound, hence `P`-vs-`NP`-strength.  Renaming does
not prove it; the value is a possibly-more-tractable *language* for the same obstruction.

## 5. Positioning against known theory (what tools might transfer)

| Framework | Relation to observer boundary entropy |
|---|---|
| **Communication complexity** | `B` at a cut *is* a (one-way, deterministic) communication measure; `log rank ≤ B` is the rank↔communication link.  Lower bounds on `B` = communication lower bounds — but here the *partition is chosen by the machine*, the hard part. |
| **Branching programs** | A width-`w` BP has boundary `log w` per layer; `B` is the layered interface entropy.  Known BP lower bounds (`Nečiporuk`, time–space for BPs) are the closest existing tools — and cap at `n²/log n`, below what is needed. |
| **Time–space tradeoffs** | `B = ω(log n)` for all poly time ⟺ SAT needs space `≥ T/log n`.  Known SAT tradeoffs (FLVV / Williams: time `≥ n^{1.8}` for sub-poly space) are far weaker — they bound time given space, not space given time. |
| **Proof complexity** | Crossing sequences ≈ the "memory" of a refutation across a cut; boundary entropy ≈ space measures in proof systems, where strong lower bounds *are* known — a candidate source of technique. |
| **Holographic algorithms / matchgates** | "Branch boundary as a sector/face" is the holographic intuition; matchgate tensor contractions are low-boundary computations.  Suggests the P-observer = bounded-treewidth / low-rank tensor contraction. |
| **Meta-complexity / MCSP** | `B` is a description-length-flavored measure of *the observer's view*.  "P = phenomena admitting low-boundary observers; NP = locally-checkable branching geometry" frames P-vs-NP as: does every locally-checkable branching geometry admit a low-boundary observer? — a clean meta-complexity statement, but still open. |

## 6. Honest assessment

* **Useful**: yes, as *language*.  It unifies Route F's crossing bound, the small-space obstruction,
  communication/BP/proof-space lower bounds, and the holographic "boundary/sector" picture under one
  invariant — and that invariant has proved laws (§1).
* **Not a shortcut**: the central conjecture (§4) is the same open problem.  The thermodynamic/spacetime
  dressing is intuition; the content is crossing/communication/space lower bounds for SAT, all open at the
  required strength.
* **Most promising transfer**: §5's *proof-complexity space* and *branching-program* rows — those are the
  regimes where super-logarithmic boundary/space lower bounds are actually proved (for restricted models).
  The honest research question is whether any of those techniques can be made to apply to a *machine-chosen*
  partition / a faithful observer of an arbitrary SAT-decider, which is exactly where all of them currently
  stop.

**Bottom line.** The observer-boundary-entropy framing is a legitimate, formally-anchored reframing of the
exact obstruction Route F exposed.  It may suggest importing proof-complexity-space or branching-program
techniques.  It does not, by itself, prove anything new — the central conjecture is `P ≠ NP` in a new
language — and this note says so plainly.
