# SCOPE: step (6), the SAT-forcing theorem — honest assessment before any attempt

The target: *every uniform legal exact SAT program has superpolynomial minimal dynamic charge*, which with the
compiler yields no polynomial-time SAT program. **Verdict: the target, stated in the charged model, is a
non-uniform circuit lower bound for SAT — `SAT ∉ SIZE(poly)` strength, strictly STRONGER than `P ≠ NP`. Every
tool in the corpus is machine-checkably capped, collapsed, vacuous, conditional, or natural-proofs-shaped against
it. No known technique passes all the gates below. The recommendation is not to attempt a direct proof; the
scope's job is to fix the gates any future attempt must pass, so that an attempt is either genuine or fails fast.**

## 1. The target, precisely (now formal)

`Step6Target.lean` pins it: `Step6 F := ¬ ProgPoly F` — no polynomial-cost charged program family for the family
`F`. Note the quantifier: one program per input length. The charged model is **non-uniform**, so for an
NP-complete family the target is `SAT ∉ SIZE(poly)` — stronger than `P ≠ NP` (which would follow, but which also
tolerates SAT having small non-uniform circuits). A uniform weakening would need a uniformity notion the model
does not currently carry (the corpus's `ChargedMachine`/RAM arc is the natural place, and connecting them is a
substantial separate build). Machine-checked height marker: `step6_implies_no_poly_formulas` — the target implies
superpolynomial formula size (programs are straight-line circuits; the compiler makes the formula direction
formal with overhead exactly 1). With step (4)'s one-way soundness (invariant hardness ⟹ cost hardness, never
the converse), "at-least-separation-hard" is now a theorem-shaped statement, not a slogan.

## 2. The gates any attempt must pass (each with a machine-checked anchor)

1. **The QF A gate** (`qf_dynamic_easy_static_hard`): `QF A` has maximal all-order entanglement (`2^{Ω(n)}` bond
   under every ordering) and a `4n²`-step program. Any measure of the function's *static* structure
   (entanglement, rank profile, correlation complexity) that would call SAT hard calls `QF A` hard — and is
   therefore false as a time lower bound. An attempt must state, up front, what its measure sees in SAT that it
   provably does not see in `QF A`.
2. **The normalization gates** (`info_cap`, `readOnce`, `cutflow_vacuous`, `embProg`): the measure must survive
   read-once normalization, localization/padding, and wire duplication — all semantics- and (near-)cost-
   preserving. Instantaneous information caps at `n`; min-over-programs input growth caps at `n`; unpinned
   cut-flow is identically zero.
3. **The clock gate** (`canonical_schemeResource_eq_clock`, `ChargedLengthObserverCollapse`,
   `ChargedDynamicQueryCollapse`): if the measure escapes the caps by charging steps, it must be shown NOT to be
   clock-equivalent — otherwise its hardness claim is the time lower bound restated (circular).
4. **The schedule gate** (`hardF_prog_width_conditional`, and the falsity of its unconditional form): residual/
   fooling structure dissolves under re-reading; any argument leaning on read order must either prove its
   schedule hypothesis for ALL programs (it cannot — re-reading is legal) or account for repeated reads.
5. **The classical barriers**, which the model does not evade:
   - *Natural proofs*: every counting/rank/state measure in the corpus is truth-table-computable and large on
     random functions — exactly the natural-proof shape, barred (under standard crypto) from proving superpoly
     bounds against general programs. An attempt must be non-constructive or non-large, explicitly.
   - *Relativization*: every trace-semantics lemma built here (forward determinism, decoder-is-the-suffix,
     congruence arguments) is a simulation argument and relativizes. The target does not.
   - *Algebrization*: likewise for the algebraic-rank machinery.

## 3. The one structural handle that remains

`QF A` and SAT are indistinguishable to every static and generic-dynamic measure in the corpus. What
distinguishes SAT is **problem-specific structure**: NP-completeness, self-reducibility, paddability. The known
programs that exploit it, and their honest status:

* **Williams' algorithms-to-lower-bounds**: real and proven, but reaches `NEXP ⊄ ACC⁰` (the corpus's socket map
  already charts this); scaling to `P`-vs-`NP` needs breakthroughs beyond the method's current reach.
* **Hardness magnification**: the modern frontier — near-linear lower bounds for MCSP-like sparse problems in
  weak models would imply superpolynomial ones. But the needed weak bounds are open, they sit adjacent to the
  natural-proofs boundary (the "locality barrier"), and the corpus's genuine restricted bounds (`hardF`,
  Nečiporuk family) are for the wrong problems and wrong models to feed magnification.
* **GCT**: occurrence obstructions are dead (Bürgisser–Ikenmeyer–Panova); the live program is far from Boolean
  `P`-vs-`NP`.
* **Proof complexity / ironic complexity**: active, real, and not currently within superpolynomial reach of
  general models.

No candidate simultaneously (i) passes the QF A gate, (ii) evades naturalization/relativization/algebrization,
and (iii) has a proven mechanism at general-program strength. That conjunction is the actual open problem.

## 4. Verdict and recommendation

* The step-(6) target is **`SAT ∉ SIZE(poly)`-strength** — the non-uniform separation, formally pinned, with its
  implication chain machine-checked. It is not bookkeeping, not a residue of steps 0–5, and not approachable by
  any measure the corpus has built or tested: each is capped (`n`, `n²`), collapsed (clock), vacuous (cut-flow),
  conditional (schedules), existential-only (best-partition), or natural-proofs-shaped.
* **Recommendation: do not attempt step (6) directly.** The honest value of the charged-model arc is the map:
  every law derivable is derived, every measure testable is tested, every conditional is explicit, and the wall's
  height is now a theorem. If an attack is ever mounted, it must open by naming its SAT-specific, non-natural,
  non-relativizing mechanism and passing the QF A gate — in that order, before any formalization. Anything else
  will be another socket, and the corpus's audit machinery will find it.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
