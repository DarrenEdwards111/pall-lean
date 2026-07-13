# SCOPE: the step-(4) dynamic invariant (paper-first)

Task: define an invariant from the charged program/trace, minimized over legal layouts/gauges, satisfying HAL's
laws — (1) gauge/layout invariance, (2) no oracle-loading, (3) `Inv ≤ poly(actual resources)`, (4) polynomial value
for every calibration program (especially `QF A`), (5) horizon/reconstruction derived from the trace. **Verdict:
the law system as stated is satisfiable but empty; every information-type instantiation is provably capped at
`n`; every clock-type instantiation is circular. The corridor between them is empty for information measures — a
formal no-go is buildable. The genuine step-4 deliverables are the no-go plus a real restricted instance (a
charged-space lower bound). The hardness axiom the route needs is not derivable from any law list — it IS step 6.**

## 1. The trivial-invariant observation: the laws are all upper bounds

Every law (1)–(5) is a consistency or upper-bound constraint. **`Inv ≡ 0` satisfies all of them** — gauge-invariant,
loads no oracles, `0 ≤ poly`, polynomial on every calibration, and derives whatever is asked from the trace
vacuously. So the law system cannot force usefulness; all separating content lives in the absent sixth law —
"`Inv` is superpolynomial for every correct SAT program" — which is exactly step 6.

## 2. The no-free-lunch: law (3) makes step 6 a ONE-WAY reduction to the separation (audit-corrected)

Suppose `Inv` satisfies law (3): `Inv(P) ≤ poly(cost(P))` for every charged program `P`. Then

> "every SAT program has superpolynomial `Inv`"  ⟹  "every SAT program has superpolynomial cost"

— invariant hardness implies computational hardness. **The converse does NOT follow** (audit correction): even if
every SAT program had superpolynomial cost, `Inv ≡ 0` satisfies law (3) and stays zero, so the invariant-hardness
claim can be false while the separation is true. Equivalence would additionally require `cost ≤ poly(Inv)` — which
makes the invariant clock-equivalent (Horn B). So the correct statement: proving the step-6 hardness side is
**at-least-separation-hard** (it implies the separation), and any sound invariant adds attack structure without
reducing that strength.

## 3. The two horns, now with proofs available

**Horn A — instantaneous and min-over-programs information caps (audit-corrected to its provable strength).**

* *Instantaneous information caps at `n` universally, trivially*: at any fixed time the state is a function of the
  `n`-bit input, so its range has `≤ 2^n` elements — for every program, no normalization needed
  (`instantaneous_info_le_n`).
* *Cumulative input-driven growth is bounded by reads, NOT by `n`, per program*: logic gates cannot increase the
  image count; an input gate at most doubles it (`stateImage_card_le`: states `≤ 2^{reads}`). A single program may
  forget and re-read — `qfProg A` re-reads quadratically — so per-program cumulative growth scales with reads
  (`≤ cost`), and claiming a per-program `n`-cap would be FALSE.
* *But the min over programs computing `f` caps at `n`*: read-once normalization (`readOnce`: load the `n` inputs
  into `n` low wires, replace re-reads by two-`NOT` copies; semantics-preserving, `n` reads, cost `≤ n + 2·cost`)
  gives every computable `f` a program whose reachable-state count stays `≤ 2^n` at every prefix (`info_cap`).
  Since hardness claims quantify over all programs (the *minimal* charge), any invariant dominated by
  prefix-state-counts has `min ≤ n` on every computable function — below even the Nečiporuk ceiling.

  What this does NOT cover (audit correction): **cut-communication, congestion, and layout-movement measures** —
  these charge logic across cuts and are bounded by neither argument. Each such candidate needs its own
  collapse-or-survive test (against `qfProg A` and the proved collapses) before any conclusion. The log-rank
  observation stands: log-rank of any `n`-bit function is `≤ n` across any cut (`QF A`: raw rank `2^{Ω(n)}` every
  cut, log-rank `≤ n`), so static rank in either normalization is sound-and-capped or unsound.

**Horn B — the proved collapses (audit-corrected: specific, not universal).** Charging every logic step uniformly
makes `Inv = Θ(cost)` and the hardness claim a time lower bound restated. The corpus proved this for three specific
measures — `ChargedCanonicalQueryAudit.canonical_schemeResource_eq_clock`, `ChargedLengthObserverCollapse`,
`ChargedDynamicQueryCollapse`. These refute *their* measures; they do NOT prove a universal dichotomy for every
logic-sensitive invariant. Measures that charge only cross-cut communication, congestion, novelty, or
layout-sensitive movement are refuted by neither horn as it stands.

**Corrected corridor statement**: the corridor is closed for instantaneous-state information (universal `n`-cap)
and for min-over-programs input-driven growth (read-once `n`-cap); it is **open** for cumulative cut-flow /
congestion measures, which must be tested candidate-by-candidate (first gates: polynomial on `qfProg A`; not
clock-equivalent; then confront the collapse precedents). A two-sided invariant with provable superpolynomial SAT
hardness would additionally have to contend with natural proofs (if truth-table-computable and random-large) and,
for algebraic-rank routes, with all-cut rank robustness — a cut-rank/rank-width–type property, related to but
**distinct from** Valiant matrix rigidity (earlier "= Valiant" phrasing retracted).

## 4. What is genuinely buildable as step (4)

1. **The trace-level information bound** (`info ≤ reads`): `log₂|image(state_t)| ≤ #input gates before t` — the
   trace generalization of `cost_ge_deps`, and laws (2)+(3) for `Inv_info`. Small, clean induction.
2. **The cap theorem (the formal no-go)**: `∀ f, ∃ P computing f with Inv_info(P) ≤ n`. Needs (a) `BForm`
   universality (Shannon expansion — standard, ~100 lines), (b) read-once normalization (replace re-reads by
   2-NOT copies from loaded wires). This machine-checks Horn A: **no information-type dynamic invariant can
   separate** — the honest closure of the invariant design space, same species as `NeciporukCeilingTotal`.
3. **The restricted instance — CONDITIONAL only (audit-corrected)**: bridging `Prog → LevBP` (width `2^w`) is
   buildable, but `hardF_bp_width_ge` assumes the address block is read in one contiguous level interval. An
   arbitrary program interleaves and re-reads freely, so the valid theorem is: **any charged program whose
   input-read schedule reads the chosen `hardF` address block contiguously needs `2^b − 1 ≤ 2·2^w`**. The
   unconditional version is FALSE: `hardF` is computable with `O(1)` wires by re-reading (compare each address to
   each hardwired cell on the fly), exactly as `qfProg A` (3 wires, quadratic re-reads) warns — static ordering
   bounds do not transfer to repeated-read programs.
4. Horn B needs no new build — cite the three collapse theorems.

## 5. Verdict

* HAL's laws (1)–(4) are mutually satisfiable — by `Inv ≡ 0`, by `Inv_info`, by restricted space measures — but
  they are upper bounds; they admit trivial and capped instances and cannot force hardness. (Law (5) is not yet
  formal; the `Inv ≡ 0` observation applies to it only under a vacuous-upper-bound formalization.)
* Instantaneous information and min-over-programs input-driven growth are **provably capped at `n`**; three clock
  measures are **proved collapsed**; cut-flow/congestion candidates remain **open** and need per-candidate tests.
* The honest step-4 deliverable is: the caps + honest growth bounds + the conditional (contiguous-schedule)
  space instance + the explicit statement that the step-6 hardness side is at-least-separation-hard (one-way).
* Step 5's horizon laws inherit this scoping: "reconstruction cost derived from the trace" is an information
  quantity (Horn A) unless it charges the clock (Horn B); the derived-horizon route should be scoped against the
  same dichotomy before building.

Recommendation: build items 1–3 (all clean-axiom, all honestly labelled — one no-go, one restricted bound), and do
**not** attempt a "hardness law" for the invariant — it would either be false, vacuous, or the separation assumed.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
