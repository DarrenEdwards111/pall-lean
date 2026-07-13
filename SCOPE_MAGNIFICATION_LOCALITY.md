# Scope — can the corpus feed hardness magnification? The locality barrier, pinned (paper-only)

Directed: scope whether the corpus's proved lower bounds can be pushed onto a sparse magnification-trigger
problem, and pin which constraint the locality barrier costs.  **Finding: the four-constraint tension is *not* the
residual obstruction — magnification with an MCSP/MKtP target dissolves it.  The residual obstruction relocates
one level down, to the *proof method*: every corpus lower bound is LOCAL, the locality barrier provably blocks
local methods from the near-linear MCSP trigger, and the one non-local method the corpus attempted — the N-Frame
cross-branch cone-excess line — is frozen at exactly the non-locality (Valiant matrix rigidity).  So the
P-vs-NP-via-magnification frontier and the corpus's frozen N-Frame line are the SAME obstruction: non-locality.
No corpus asset is magnification-eligible; the missing ingredient is a non-local lower-bound method, which is
open and rigidity-strength.**

## 1. The magnification target and why it reshapes the bridge

Hardness magnification (Oliveira–Santhanam; McKay–Murray–Williams; Chen–Jin–Williams): a **near-linear** lower
bound (`n^{1+ε}` circuits, `n·polylog` formulas/branching programs, or the sharp sparse threshold) for a
**sparse meta-complexity** problem — `MCSP[s]`, `Gap-MCSP`, `MKtP` — implies a **superpolynomial** separation
(`NP ⊄ P/poly`, `EXP ⊄ P/poly`, etc.).  The leverage: you no longer need a superpolynomial measure; a *slightly
superlinear* bound suffices, and the problem's self-improving/sparse structure amplifies it.

This dissolves the four-constraint tension of the previous audit (`SCOPE_QF_CALIBRATION_AUDIT`, and the P-vs-NP
"bridge" note).  Against `SAT` directly, a measure had to be (1) semantic, (2) decision-level, (3) superpolynomial,
(4) easy-calibrated — four demands in genuine barrier-tension.  With an **MCSP** target:

* (1) semantic — MCSP is the *circuit complexity of the input function*, semantic by definition;
* (2) decision — MCSP is a decision problem, magnification gives *its* size lower bound;
* (3) superpolynomial — **now cheap**: near-linear suffices, magnification supplies the rest;
* (4) calibration — MCSP-hardness methods do not misfire on low-complexity inputs.

So the *right target exists* and satisfies the shape.  The obstruction is no longer "no measure."  It moves to a
**fifth, method-level constraint** the four-constraint framing did not name.

## 2. The fifth constraint: LOCALITY — and every corpus bound violates it

**Locality barrier** (Chen–Hirahara–Oliveira–Pich–Rajgopal–Santhanam 2020): a lower-bound method is *local* if it
certifies hardness through a small window / restriction / oracle-respecting structure.  Such methods **provably
cannot** prove the near-linear MCSP magnification triggers — a local proof of MCSP hardness would also hold
relative to an oracle under which MCSP is easy, a contradiction.  Essentially every classical technique is local:
Nečiporuk subfunction-counting, random restrictions, gate elimination, communication/crossing sequences,
shifted-partial-derivatives.

Audit of the corpus's proved lower bounds against this — **all local, all for the wrong (non-sparse) problems:**

| asset | method | local? | sparse/MCSP? |
|---|---|---|---|
| `neciporuk_sum_lower_bound`, `NeciporukCeilingTotal` (`n²/log n`) | subfunction count on disjoint blocks | **yes** (textbook local) | no (`hardF`/addressing) |
| `hardF_litCount_lower`, `hardF_blockBoundary_ge` | single address block's subfunctions | **yes** | no |
| `identity_minor_lower_bound` (SPDP, Tseitin) | shifted-partial / submatrix minor | **yes** | no (Tseitin) |
| BSW expander–Tseitin proof width | local proof-complexity measure | **yes** | no |
| tensor/entanglement bond (`exists_global_best_partition_bond`) | rank across one cut | **yes** (communication-local) | no (`QF A`) |

The closest in *shape* is Nečiporuk (`n²/log n` is a genuine **superlinear formula** bound in a **weak model** —
exactly a magnification trigger's shape).  But it is the *canonical* local method, explicitly barred, and it is
for `hardF`, not a sparse meta-complexity problem.  Transporting Nečiporuk to `MCSP` fails twice: wrong problem
(MCSP lacks the disjoint-block many-subfunction structure Nečiporuk needs) and, even if forced, the locality
barrier bars the resulting bound.  **No corpus asset is magnification-eligible.**

## 3. The unification: magnification-locality = N-Frame cross-branch = Valiant rigidity

The corpus already contains one attempt at a **non-local** measure: the **N-Frame cross-branch cone-excess** arc
(`…NFrameRigidAdditiveMixer`, `…NFrameConeIntersection`, `…NFrameShareChargeBound`, …).  Cone-excess is a
*global, amortized* quantity (a direct-sum charge across recursive branches) — precisely a non-local measure, by
design.  Its single open inequality is

```text
CE(F_{k+1}) ≥ 2·CE(F_k) + cN     (cross-branch direct-sum / no-amortization)
```

which the repo audit already reduced to **Valiant matrix rigidity** (linear mixer horn) / **Uhlig sharing**
(nonlinear horn) — both open.  That is *exactly the non-locality* the locality barrier says a magnification
method must have: a global amortization that no local window can certify.

So the two frozen frontiers coincide:

> **P-vs-NP via magnification is blocked by locality ⟺ the corpus needs a non-local method ⟺ the N-Frame
> cross-branch inequality ⟺ Valiant rigidity.**

They are the same obstruction wearing two costumes.  This is not a solution, but it is a genuine unification: it
shows the remaining hope does not spread across many independent ideas — it **concentrates in a single object**, a
non-local / global-amortization / rigidity-breaking lower-bound method, and the corpus's own N-Frame line is
already parked at that exact object.

## 4. Verdict and the one honest target

* **No corpus asset feeds magnification.**  All proved bounds are local (barred) and for non-sparse problems.  The
  best-shaped one (Nečiporuk `n²/log n`) fails on both counts.
* **The bridge refines** from "a semantic decision measure for SAT" to **"a non-local lower-bound method for a
  near-linear MCSP/MKtP bound."**  This is a *method*, not a measure — the four-constraint framing was one level
  too high.
* **That method is Valiant-rigidity-strength**, and the corpus's N-Frame cross-branch line is already the corpus's
  instance of it, frozen at the direct-sum inequality.  So the honest single target is: **break the cross-branch
  no-amortization inequality `CE(F_{k+1}) ≥ 2·CE(F_k) + cN` for the truncated recursive family** — equivalently,
  construct a non-local amortization lower bound / a rigidity-type bound.  It is open, it is famous-open-strength,
  and it is the *one* place where a genuinely new idea would break the wall rather than restate it.

Recommendation: this is where a direct attack belongs — not a new invariant, not another route, but the N-Frame
cross-branch inequality, now understood as *the same object* as the magnification frontier's missing non-local
method.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`; it names the target as sharply as the corpus permits.
