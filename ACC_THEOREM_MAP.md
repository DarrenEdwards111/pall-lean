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
