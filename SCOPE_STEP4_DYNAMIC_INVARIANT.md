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

## 2. The no-free-lunch: law (3) makes step 6 ⟺ separation

Suppose `Inv` satisfies law (3): `Inv(P) ≤ poly(cost(P))` for every charged program `P`. Then

> "every SAT program has superpolynomial `Inv`"  ⟺  "every SAT program has superpolynomial cost"

(⇒ by law (3) contrapositive; ⇐ because a poly-cost SAT program would need poly `Inv` by law (3)... the forward
direction is the content; the equivalence with the compiler of step 3 in hand is immediate). This is not a defect
of any particular `Inv` — it is what *sound* means. The invariant can only add **attack structure** to the
separation; it cannot reduce its strength. HAL marked step 6 separation-strength; this makes it precise: *any*
sound invariant's step 6 is the separation, verbatim.

## 3. The two horns, now with proofs available

**Horn A — information-type measures are capped at `n` (provable no-go).** Take the canonical information
invariant, `Inv_info(P) := max_t log₂ |image(x ↦ state_t(x))|` (any variant — cut log-rank, accumulated growth,
total variation — is dominated by the same argument):

* *It satisfies every law*: logic gates cannot increase the image count (the next state is a function of the
  current one); an `input` gate at most doubles it. Hence `Inv_info ≤ #input gates ≤ cost` — laws (2), (3) — and
  it is wire-permutation invariant (1) and polynomial on all calibrations (4).
* *It is capped at `n` for every function*: every `f` has a **read-once** program — read the `n` inputs into `n`
  dedicated wires (`n` input gates; image count ≤ 2^t ≤ 2^n during this phase), then compute by pure logic (image
  count never increases). Copying a wire needs no input gate (`copy = two NOTs`), and every Boolean function is a
  `{¬,∧,⊕}` straight-line program on loaded wires (Shannon expansion / `BForm` universality). Hence
  `min_P Inv_info(P) ≤ n` for **every** `f`, SAT included.

  So the information horn cannot separate anything — it is capped at **linear**, worse even than the Nečiporuk
  ceiling (`n²`, `NeciporukCeilingTotal`). The log-rank warning is subsumed: log-rank of any `n`-bit function is
  `≤ n` across any cut, so even the "right" (growth) normalization caps. The corpus holds the exact witness pair:
  `QF A` has raw rank `2^{Ω(n)}` at every cut (`exists_global_best_partition_bond`) but log-rank `≤ n` — raw rank
  fails law (4), log rank caps at `n`. There is no setting of the rank dial that is both sound and unbounded.

**Horn B — clock-type measures are circular.** If `Inv` charges logic steps (to escape the cap), then
`Inv = Θ(cost)` up to the charging weights, and the hardness claim for SAT is *verbatim* a time lower bound — the
separation restated. This is not hypothetical: the corpus already proved it for the charged measures —
`ChargedCanonicalQueryAudit.canonical_schemeResource_eq_clock` (the maximally-rich scheme's innovation is exactly
the clock), `ChargedLengthObserverCollapse` / `ChargedDynamicQueryCollapse` (charged observer/dynamic measures
collapse). Horn B is the machine-checked history of this project.

**The corridor is empty** (for information measures): anything logic-free caps at `n` (Horn A); anything
logic-charging is the clock (Horn B). A two-sided invariant with provable superpolynomial SAT hardness must be a
*non-information* semantic measure — and the known candidates are the known walls (algebraic degree/rigidity =
Valiant; any truth-table-computable, random-large measure = natural proofs, which its hardness side would need to
evade by non-constructivity or non-largeness).

## 4. What is genuinely buildable as step (4)

1. **The trace-level information bound** (`info ≤ reads`): `log₂|image(state_t)| ≤ #input gates before t` — the
   trace generalization of `cost_ge_deps`, and laws (2)+(3) for `Inv_info`. Small, clean induction.
2. **The cap theorem (the formal no-go)**: `∀ f, ∃ P computing f with Inv_info(P) ≤ n`. Needs (a) `BForm`
   universality (Shannon expansion — standard, ~100 lines), (b) read-once normalization (replace re-reads by
   2-NOT copies from loaded wires). This machine-checks Horn A: **no information-type dynamic invariant can
   separate** — the honest closure of the invariant design space, same species as `NeciporukCeilingTotal`.
3. **The genuine restricted instance**: bounded wires. A charged program on `w` wires with its fixed gate sequence
   is an oblivious computation of width `2^w`; bridging `Prog → LevBP` and applying the proved BP bound
   (`hardF_bp_width_ge`: `2^b − 1 ≤ 2·width`) gives: **any charged program computing `hardF` needs
   `w ≥ b − O(log b)` wires** — a real, unconditional charged-space lower bound (small — `Ω(log n)` — but genuine,
   and it connects the step-2 language to the BP arc). This is what a *sound and true* step-4 invariant can
   actually deliver: space-type bounds in the restricted regime.
4. Horn B needs no new build — cite the three collapse theorems.

## 5. Verdict

* HAL's laws (1)–(5) are mutually satisfiable — by `Inv ≡ 0`, by `Inv_info`, by restricted space measures — but
  they are all upper bounds; they admit trivial and capped instances and cannot force hardness.
* The information instantiations are **provably capped at `n`** (buildable no-go, item 2), and the clock
  instantiations are **circular** (already machine-checked). The corridor is empty for information measures.
* The honest step-4 deliverable is: the cap theorem + the charged-space restricted bound + the explicit statement
  that the missing hardness axiom *is* step 6 (separation-strength, not derivable from trace bookkeeping).
* Step 5's horizon laws inherit this scoping: "reconstruction cost derived from the trace" is an information
  quantity (Horn A) unless it charges the clock (Horn B); the derived-horizon route should be scoped against the
  same dichotomy before building.

Recommendation: build items 1–3 (all clean-axiom, all honestly labelled — one no-go, one restricted bound), and do
**not** attempt a "hardness law" for the invariant — it would either be false, vacuous, or the separation assumed.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
