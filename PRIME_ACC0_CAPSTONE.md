# Prime `AC⁰[p]` Capstone & Scope Ledger

*One-page ledger for the prime Razborov–Smolensky route, now complete, and the honest boundary between what
is **proved unconditionally** in this repo and what remains **conditional / open / equivalent to the
theorem**. Capstone: `PallLean/Paper93/DeepMath/PathB/ComputationalDepthACC0PrimeCapstone.lean`.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.*

---

## The capstone (PROVED, `sorry`-free, custom-axiom-free)

Each name below is verified by `#print axioms` to depend on **only** `propext, Classical.choice,
Quot.sound` — on **none** of the arc's separation-strength axioms (`beigelTarui_faithful`,
`williams_decider_in_NEXP`) or SPDP/gauge axioms. Complete proofs, not shells.

| Capstone name | Statement | Backed by |
|---|---|---|
| `parity_not_ac0p` | `PARITY ∉ AC⁰[p]` (odd prime `p`): a depth-`d`, parity-computing `AC⁰[p]` circuit on `2m+1` inputs has `> p^t/4` subcircuits for `8·((p-1)t)^{2d} ≤ m` — `2^{Ω(n^{1/2d})}` | `Layer3.parity_function_lower_bound` |
| `mod_q_not_ac0p_indicators` | `MOD_q ∉ AC⁰[p]` (distinct primes `p≠q`), residue-indicator form over `𝔽_{p^{q-1}}` | `Layer4.mod_q_indicators_false` |
| `mod_q_not_ac0p_literal` | `MOD_q ∉ AC⁰[p]`, literal-family form (via `padTrue`) | `Layer4.mod_q_family_false` |
| `quantitative_bridge` | the discharged polynomial-method bridge `QuantitativeDepthBound _ (t^{cdepth C}) E`, `2^t·E ≤ size·2^n` | `ACC0QuantBridgeWiring.quantitativeDepthBound_of_circ` |

**State of the prime route:** the polynomial-method assembly now has **no remaining socket** but the
Smolensky wall `SmolenskyNonNativeLowerBound`, and for prime `q` that wall is itself a theorem
(`algExpander_forces_high_degree`). So the prime `AC⁰[p]` lower bound is complete end-to-end.

---

## Proved unconditionally elsewhere in the arc (this session's real assets)

| Result | File | Scope |
|---|---|---|
| Restricted **Freshness** (formula / linear / monotone) ⇒ super-linear | `…NFrameRestrictedFreshness` | circuit direct-sum, restricted classes |
| Explicit **monotone KRW depth ≥ 10000** at `N=2^100` | `…NFrameKRWMonotoneExplicit` | monotone formula depth, `> NC¹`-depth |
| **Scale ceiling** — log-depth accumulation caps at `poly(N)` | `…NFrameScaleCeiling` | proves the N-frame reaches only super-linear |
| **Binomial-tail** discharge of the prime route residual | `…ACC0BinomialTail` | `lowDegreeDim n D' < 2^n − C(n,D'+1)` |
| **Quant-bridge wiring** (socket → theorem) | `…ACC0QuantBridgeWiring` | `QuantitativeDepthBound` discharged |
| **Nečiporuk `Ω(N²/log N)`** formula-size LB (+ method, + ceiling no-go) | `…NeciporukCapstone` | De Morgan formula size; ceiling at `N²/log N` (see `NECIPORUK_CAPSTONE.md`) |
| **Håstad switching bound (`hnf` regime)** + weak general + modulo-decoder | `…SwitchingCapstone` | `AC⁰`/depth-3; **partial** — tight general open (see `SWITCHING_CAPSTONE.md`) |
| **Forster sign-rank** `≥ n/‖·‖` + Walsh UPP `≥ k/2` (+ isotropic crux) | `…ForsterCapstone` | complete for sign-rank/UPP; circuit application fenced (see `FORSTER_CAPSTONE.md`) |
| **Tseitin proof-space** `Ω(\|V\|)` (resolution, incl. min-over-refutations) | `…TseitinSpaceCapstone` | resolution proof-space; restricted (see `TSEITIN_SPACE_CAPSTONE.md`) |

All `sorry`-free, axioms ⊆ `{propext, Classical.choice, Quot.sound}`.

---

## Conditional / socketed / open (NOT proved)

| Target | What it rests on | Honest status |
|---|---|---|
| `NEXP ⊄ ACC⁰` | axioms `beigelTarui_faithful`, `williams_decider_in_NEXP` | **conditional cash-out**; each axiom self-audited `↔ NEXP ⊄ ACC⁰` (separation-strength) |
| Composite-MOD ACC⁰ | `CarryRefinementCrossing` | **open frontier**; proved un-crossable by the `𝔽_p` polynomial method (`composite_lift_not_single_field_reducible`); needs Williams' algorithmic method |
| SPDP / Cook–Levin `P≠NP` | P-side rank `≤ poly` | **false** — trivial DTMs have rank `> n^200` (`compiledPoly_rank_gt_npow200_at_large_n`) |
| Flexible-boundary projection | a non-flat rank-reducing `Π` (`CookLevinRichProjectionTarget`) | **≡ the theorem** — separating a machine-independent floor by hardness = super-poly circuit LB |
| N-frame / FOER `P≠NP` | super-polynomial scale bridge (H4) | **≡ the theorem** — accumulation caps at `poly(N)`; H4 = a single-scale super-poly LB |
| KRW / IC `P⊄NC¹` | fixed-known-`g` no-amortization | **open**, and `NC¹`/formula-depth scale, not full `P≠NP` |
| Tight *general* Håstad switching lemma | `hinj` decoder (Razborov forward decoder) | **open** — proved on `hnf` regime; `AC⁰`/depth-3 scale, not `P≠NP` |
| Forster ⇒ general circuit LB | poly circuit ⇒ cheap UPP protocol (`happrox`/`hmargin`) | **open** — sign-rank/UPP proved; circuit application socketed |
| Tseitin general observer / spacetime | non-resolution machine-decomposition observer; spacetime volume | **open** — resolution space proved; general observer `P≠NP`-strength; Arc-2 spacetime is a socket harness |
| RHA extraction (`…RamanujanHolographicAmplituhedron…`) | `preservesLabels` field | **socket, provably VACUOUS** — `impossible` proves the structure self-contradictory (pigeonhole: preserve `2^m` labels in `≤ m^k < 2^m` cells); cash-out is ex-falso; Ramanujan/holographic/amplituhedron payloads are decorative `Prop` fields |
| Tseitin-expander RHA (`…TseitinExpanderRHA…`) | `preservesTseitinLabels` field | **socket, provably VACUOUS + field FALSE** — same pigeonhole vacuity; and `preservesTseitinLabels` over all P-solvers is refuted by Gaussian elimination (Tseitin ∈ P), so the "final hard theorem" is a false statement, not an open one |
| Hard-residual decoder extraction (`…HardResidualFamily…`) | `decode_correct_of_decides_for_hard_residuals` field | **socket, CIRCULAR (not vacuous)** — improved: conditional (`DecidesSAT →`) field, so inhabitable when `¬DecidesSAT` rather than empty. But via the built-in `not_decidesSAT` pigeonhole, `HardResidualDecoderExtractionForAllMachines U ⟺ ¬SATDecisionInP U`, so the cash-out is `(≡¬SAT∈P)→¬SAT∈P`. The field = `¬DecidesSAT` per machine: FALSE for P-easy families (Gaussian), = the theorem for shortcut-free ones. `not_easy_linear_payload` fence unproven = the missing explicit object outside P |
| Dynamic trace geometry (`…DynamicTraceGeometry…`) | `boundary_sound_of_decides` field | **socket, CIRCULAR (same as hard-residual, relabeled)** — `SoundOnFoolingFamily` = the preservation/injectivity field renamed "sound"; `decodeOfBoundary_correct_of_sound` is the trivial `injective⟹decodable` direction (`Classical.choose`), so no level is lowered; `not_decidesSAT` delegates to the same pigeonhole. The file's own `boundary_soundness_is_the_gap` proves `¬SoundOnFoolingFamily` under poly+gap, so `boundary_sound_of_decides ≡ ¬DecidesSAT`; cash-out ex-falso/circular. "Non-circular preservation" claim is backwards — it's the pigeonhole-impossible field |

---

## Bottom line

**Proved:** genuine restricted circuit lower bounds — `PARITY/MOD_q ∉ AC⁰[p]` (prime `p`), monotone KRW
depth, restricted Freshness — real classical mathematics, machine-checked, custom-axiom-free.

**Not proved, and the honest gap for `P ≠ NP`:** a **non-natural separating invariant** `μ` that is (i)
intrinsic (not "runs in poly time"), (ii) proved `≤ poly` on all of `P` by a per-gate structural induction,
(iii) super-polynomial on an NP-complete object, (iv) non-natural (evading Razborov–Rudich). Every route in
this repo is **false**, **wrong-scale** (super-linear / `NC¹`), **restricted-class** (`AC⁰[p]`, prime), or
**equivalent to the theorem itself**. The missing object is not a design step; it is the theorem.

**Productive direction:** consolidate and extend the restricted-class lower bounds (the prime `AC⁰[p]`
capstone here; Nečiporuk `n²/log n`; switching-lemma `AC⁰`; Forster sign-rank; Tseitin proof-space
observer) — these are real and provable. Full `P ≠ NP` needs a new idea beyond the current framework.

*Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.*
