# ACC⁰ theorem map — at-a-glance status

Consolidated status of the ACC⁰ lower-bound programme (pall-lean, PathB). Companion to `ACC_ROADMAP.md`
(narrative) and `WHAT_IS_PROVED.md` (full ledger). Updated 2026-06-14.

## Tier 1 — AC⁰ (switching method): **DONE & FENCED**

| result | theorem | file |
|---|---|---|
| clause-count-free switching tail | `hastad_switching_prob_tail` (`∑_Bad pweight ≤ (4pw/(1-p))^s`) | `…Depth3SwitchingProbTail` |
| depth collapse whp | `depth_collapse_mass_ge` (width-`w` DNF → depth ≤ 2 on `1-(4pw/(1-p))^s`) | `…Depth3SwitchingDepthReduction` |
| **switching cannot cross MOD** | `mod_gate_parity_nonconstant` (MOD gate non-constant on any free-support cube) | `…ACCSwitchingModBridge` |

⇒ Switching kills AC⁰ depth; provably does **not** reduce MOD/ACC⁰ depth.

## Tier 2 — AC⁰[p] (polynomial / Razborov–Smolensky, `p` prime): **DONE & FENCED**

| result | theorem | file |
|---|---|---|
| PARITY ∉ AC⁰[p] | `parity_function_lower_bound` (`2^{Ω(n^{1/2d})}`) | `…Layer3Smolensky` |
| N-frame target = parity | `fParity_univ_eq_parity`, `nframe_parity_target_size_lower_bound` | `…Layer3NFrameParityRS` |
| socket 1: target escapes `V_D` | `holonomy_parity_not_lowDegEval` | `…Layer3LowDegHolonomy` |
| socket 2: AC⁰[p] ⊆ low-rank | `acc0_approx_by_lowRankPredictor`, `eval_mem_lowDegSpan` | `…Layer3ACC0LowRank` |
| socket 3: modulus boundary | `fermat_indicator`, `modp_eval_mem_lowDegSpan` (`MOD_p` ∈ `V_{p-1}` over `F_p`) | `…Layer3ModulusBoundary` |
| MOD_q ∉ AC⁰[p], `q≠p` prime | `mod_q_indicators_false` (Smolensky) | `…Layer4ModqChar` |

⇒ Polynomial method linearises exactly `MOD_p` gates over `F_p`; the lower bound is real.

## Tier 3 — general ACC⁰ (mixed / composite MOD): **OPEN — the genuine frontier**

The wall is precisely **mixed modulus**: no single prime field linearises gates of different moduli.

| structural fact | theorem | file |
|---|---|---|
| `F_p` statistic = count mod p | `fp_statistic_eq_count` | `…Layer3MixedModulus` |
| **MOD_6 = MOD_2 ∧ MOD_3** (CRT) | `mod6_eq_mod2_and_mod3` | `…Layer3MixedModulus` |
| MOD_2 low-degree over `F_2` | `mod2_detector_lowdeg_F2` (∈ `V_1`) | `…Layer3MixedModulus` |
| MOD_3 low-degree over `F_3` | `mod3_detector_lowdeg_F3` (∈ `V_2`) | `…Layer3MixedModulus` |
| hybrid observer | `MixedModulusStratifiedObserverSocket` (named OPEN socket) | `…Layer3MixedModulus` |
| **mixed-modulus SAT speedup** | `mod_circuit_sat_speedup` / `mod6_circuit_residue_speedup`: `∏q_j<2^n` ⇒ `<2^n` residue cells | `…ACC0ModResidueSpeedup` |
| **operational residue machine** | `residueSearch` (timed algorithm); `residueSearch_decides`, `residueSearch_beats_bruteforce` (`steps≤∏q_j`, `<2^n`) | `…ACC0ResidueMachine` |
| **branched residue cost** | `branched_residue_beats_bruteforce` / `…_mod6_…`: `2^killed·∏surviving q_j < 2^n` past the `∏q_j<2^n` base regime | `…ACC0BranchedResidue` |
| **restriction ⇒ few survivors** | `residue_cells_le_surviving_moduli`: `\|cells(C↾L)\| ≤ ∏_{surviving} q_j` (discharges step 2's per-branch bound) | `…ACC0ResidueRestriction` |
| **depth iteration (socket)** | `acc0_depth_reduction_speedup`: `MixedACCDepthReductionSocket` (Yao–Beigel–Tarui depth-2 normal form, OPEN) ⇒ residue search decides `Satisfiable(eval C)` in `<2^n` | `…ACC0ResidueDepthReduction` |
| **Williams cash-out (interface)** | `residue_cashout_bundled`: depth socket + `UniformWilliamsRealizationSocket` ⇒ `NEXP⊄ACC⁰`; self-audit `*_iff_separation` (sockets ⟺ separation) | `…ACC0WilliamsCashout` |
| **residue-observer algebra** | `ObservedBy`, `observed_top_pi` (composition law), `.and`/`.or`/`.comp`, cell-count bounds | `…ACC0ResidueObserver` |
| **toy Beigel–Tarui (attacking the wall)** | `toy_bounded_bottom_searchable`: SYM-of-`AND_w` (fan-in `≤w` bottom) searchable in `<2^n` — depth-reduction socket **discharged for the bounded-bottom fragment** | `…ACC0BeigelTaruiToy` |
| **depth-3 MIXED fragment** | `depth_mixed_searchable`: arbitrary top over a bottom **mixing** `MOD_q` + bounded-`AND_w` gates is searchable in `<2^n` when `∏(per-gate states)<2^n` — socket **discharged for the mixed-bottom fragment** | `…ACC0Depth3Mixed` |
| **support normal form (syntax-level)** | `acc0_observed_by_projection`: ANY `ACC0Circuit` observed by projection to its `support` (`eval_depends_on_support`, induction); `acc0_junta_searchable` (junta ⇒ `<2^n`); `acc0_top_over_subcircuits_searchable` (top over ACC⁰ subcircuits jointly reading `<n` vars ⇒ `<2^n`, union support) — `ACC⁰⊆mixed-bottom` chipped at circuit syntax | `…ACC0SupportNormalForm` |
| **depth-3 MOD normalization (residue gain)** | `and_of_mods_searchable`: syntactic `MOD_{q₁}∧MOD_{q₂}` ⇒ `Depth2ModCircuit`, residue-searchable `<2^n` when `q₁·q₂<2^n` **regardless of support** (junta gives nothing here); `mod_bottom_circuit_searchable` (arbitrary top over MOD family) | `…ACC0Depth3ModNormalize` |
| **AC⁰-over-MOD normalization (general)** | `modComb_normalizes`: ANY AND/OR/NOT combination of a MOD-gate family `= Depth2ModCircuit.eval ⟨gates, combTop C⟩` (factors through MOD outputs, induction); `modComb_searchable` (residue-searchable `<2^n` when `∏q_i<2^n`) | `…ACC0ModCombNormalize` |
| **observer extracted from raw syntax** | `acc0_residueObserved`: by induction on `ACC0Circuit`, ANY circuit (positive MOD moduli) is `ObservedBy` a product statistic of state count `≤ stateBound C` (occurrence product: `q` per MOD, `2` per var, mult. through `∧`/`∨`) — `MOD` leaf→`modGate_observedBy`, `var`→coord projection, gates→`.comp`/`.and`/`.or`; `acc0_modcircuit_searchable` (`stateBound C<2^n` ⇒ `<2^n` cells). Bottom *derived*, not assumed | `…ACC0ExtractObserver` |
| **deduplicated state bound (collapses occurrence overcount)** | `acc0_dedupObserved`: by induction, `eval C` observed by `(mod-residue, ONE projection to `varSupp C`)` — `MOD`-internal vars absorbed into residue (`modOcc C`, no `2` cost), `var`-leaves counted by *deduplicated* union support (the `∧`/`∨` arms share a single projection onto `varSupp a ∪ varSupp b`, recovered by restriction); `acc0_dedup_searchable` (`modOcc C·2^\|varSupp C\| < 2^n` ⇒ `<2^n` cells). Strictly tighter than `stateBound` (vars once, not per occurrence) | `…ACC0DedupShrink` |

**Progress on the depth-reduction wall:** the residue-observer algebra (`observed_top_pi`) makes depth composition
reusable, the toy discharges the socket for the bounded-bottom (`SYM`-of-`AND_w`) fragment, and `acc0_residueObserved`
now *derives* the residue/mixed observer from the raw `ACC0Circuit` inductive (no assumed bottom) — every circuit is
observed by a product statistic of state count `stateBound C` (the occurrence product). The honest gap is unchanged:
that bound is the *occurrence* product, so the gain holds only for few-leaf circuits where MOD gates supply the
compression; getting a *small* bound for an *arbitrary* `ACC⁰` circuit is the structural shrinkage of full
Yao–Beigel–Tarui — still open.

**Architecture closed (conditionally):** the residue-speedup chain (steps 1–4, proved) cashes out to `NEXP ⊄ ACC⁰`
through exactly **two named open sockets**, both separation-strength (proved equivalent to the separation by the
self-audit theorems):
1. `MixedACCDepthReductionSocket` — Yao–Beigel–Tarui depth-2 normal form (switching can't give it: the MOD no-go).
2. `UniformWilliamsRealizationSocket` — uniform `2^{n−n^ε}` realization + Williams' algorithmic method.
The only *proved* link in the cash-out is `mixedACC_speedup_of_depthReduction` (the residue chain). `NEXP ⊄ ACC⁰`
remains an abstract `Prop` — **not defined, not proved**. This is the honest architecture, not a result.

**Why the *lower bound* is open:** `MOD_6`'s two CRT components are each low-degree but over *incompatible* fields —
`MOD_3` over `F_2` and `MOD_2` over `F_3` are high-degree (Smolensky). A single-`F_p` polynomial observer captures
only one component; a *modulus-stratified / hybrid* observer is needed, and whether it yields a lower bound is the
ACC⁰ frontier.

**The route that does cross it — STARTED:** not more RS, but **Williams' algorithmic method** (faster ACC⁰-SAT +
the nondeterministic time hierarchy → `NEXP ⊄ ACC⁰`). The **SAT-speedup kernel is now proved**
(`…ACC0ModResidueSpeedup`): a depth-2 `MOD`-circuit factors through its *residue vector* (∈ `∏ ZMod q_j`), so SAT is
a search over `≤ ∏ q_j` cells (`sat_iff_residue_image`, `residue_cell_count_le`) — `< 2^n` whenever `∏ q_j < 2^n`
(e.g. `6^k < 2^n` for `MOD_6`). This is the structural residue-compression Williams exploits. **Remaining gap:**
realising the speedup as a uniform (nondeterministic) algorithm + the time-hierarchy cash-out (the named gap in
`…NFrameACC0Master`) — that is what `NEXP ⊄ ACC⁰` needs, and this cell-count bound does not supply it.

## Honest ceiling

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`. Tier 1 = genuine AC⁰ switching; Tier 2 = genuine `PARITY ∉ AC⁰[p]`
(classical, constant depth, prime `p`); Tier 3 = open, needs a different (algorithmic) tool.
