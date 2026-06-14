# ACC⁰ lower-bound road-map (pall-lean, PathB)

A standing orientation doc for the ACC⁰ programme, so effort does not circle back into capped routes.
Updated 2026-06-14.

## 0. Where we are

The **switching (AC⁰) route is capped** — both halves are proved and fenced:

- AC⁰ depth-collapse: the clause-count-free Håstad tail `hastad_switching_prob_tail`
  (`∑_{Bad} pweight ≤ (4pw/(1-p))^s`) and its complement `depth_collapse_mass_ge`
  (a width-`w` DNF collapses to depth `≤ 2` on a `1 - (4pw/(1-p))^s` fraction of restrictions).
- The **MOD no-go**: `…ACCSwitchingModBridge.mod_gate_parity_nonconstant` — a MOD/parity gate is non-constant on
  any restriction cube leaving a support coordinate free, so switching (which leaves coordinates free) provably
  **cannot** drive `switch_step` (which needs the full support fixed). The two models do not compose into a
  switching-driven ACC⁰ bound. This is the Razborov–Smolensky vs. switching wall, formalized.

⇒ **Do not re-enter switching for the MOD layer.** The ACC⁰ layer needs the polynomial method.

## 1. The polynomial (Razborov–Smolensky) layer — ALREADY SUBSTANTIALLY PROVED

Surprisingly complete in `…Layer3*`. All clean axioms, no `sorry`:

| piece | theorem | file |
|---|---|---|
| circuit → exact polynomial | `toPoly`, `toPoly_eval_AC0` | `…Layer3AC0pPoly` |
| probabilistic low-degree approximant | `genOrApprox`, `orApprox_error_rate` (`p^{-t}` error) | `…Layer3AC0pApprox` |
| degree ≤ `((p-1)t)^depth` | `toAgree_totalDegree_le`, `ApproxDegreeData.approxDegree_le` | `…Layer3DegreeComposition` |
| low-degree monomial count `∑_{k≤D} C(n,k)` | `lowDegMonomials_card`, `…_lt_two_pow` | `…Layer3DimensionCount` |
| **effective-dimension deficit** | `finrank_span_lowDegEval_le_card`, `lowDegEval_span_ne_top` (D<n ⇒ proper subspace) | `…Layer3DimensionCount` |
| squarefree monomials span the cube | `squarefreeSpan_eq_top`, `mem_squarefreeSpan` | `…Layer3DimensionCount` |
| **PARITY ∉ AC⁰[p]** (full RS) | `parity_circuit_false`, `parity_function_lower_bound` (`2^{Ω(n^{1/2d})}`) | `…Layer3Smolensky` |

So the "low-degree polynomial approximation" tool the pivot called for is **built**. The
"low-degree ⇒ low effective dimension" bridge is `finrank_span_lowDegEval_le_card` + `lowDegEval_span_ne_top`.

## 2. The N-frame / holonomy correlation layer — PROVED

In `…Holonomy*`, `…ModQGateBalance`, all clean:

- target: `fParity D` / `parityCharge D` (holonomy parity), `modQStat q` (MOD statistic);
- `agreement_le_sum_majority`, `low_rank_predictor_low_correlation_with_full_holonomy` (correlation engine seed);
- `restricted_fragment_low_correlation` (a predictor factoring through `< |D|` variables can't correlate);
- `modQ2_gate_zero_correlation`, off-diagonal balance for MOD_q.

## 3. The connection (the genuine open work)

The polynomial layer and the holonomy layer are two *complete but separate* proofs of related facts. The
pivot's real content is to **fuse them via effective dimension** and cash out through the Williams scaffold.

**Done this round:** `…Layer3NFrameParityRS.nframe_parity_target_size_lower_bound` — the N-frame holonomy
target `fParity univ` **is** the literal parity `decide(Odd #ones)`, so the proved RS size lower bound applies
to it directly: any AC⁰[p] circuit computing the N-frame parity target needs `2^{Ω(n^{1/2d})}` size. This is
the first `nframe_target_has_high_rs_degree`-style bridge.

**Still open (the sockets):**

1. `low_degree_predictor_correlation_bound` — fuse the *effective-dimension* bound
   (`finrank_span_lowDegEval_le_card`) with the *correlation* engine (`agreement_le_sum_majority`): a predictor
   whose evaluation lands in a dimension-`< 2^{m}` span cannot correlate with the holonomy parity beyond a
   controlled bound. (The RS counting and the holonomy balance currently prove correlated facts by different
   means; unifying them in the finrank/effective-dimension language is the bridge.)
2. `ACC0ApproximatesByLowRankPredictors` — the named socket: an ACC⁰ circuit's behaviour on the agreement set
   is captured by a low-rank/low-effective-dimension predictor. (RS gives this *with* an error set, via the
   probabilistic approximant; turning the error set into a correlation/agreement statement is the work.)
3. The MOD-modulus mismatch: `parity_function_lower_bound` needs the circuit's MOD gates to all have modulus
   `= p` (the RS field prime). True ACC⁰ allows *composite/other* moduli; handling `MOD_q` for `q` coprime to
   `p` is the genuine ACC⁰-vs-AC⁰[p] gap (the part that is `NEXP ⊄ ACC⁰`-hard via the Williams method, not RS
   alone).

## 4. Cash-out target

If the effective-dimension/correlation fusion (socket 1/2) yields a SAT-speedup or correlation failure for
ACC⁰, plug into the master bridge `NFrameGivesACC0SatSpeedup` (`…NFrameACC0Master`) and the Williams scaffold.

## 5. Honest ceiling

Everything here is model-relative / restricted. The RS layer is a genuine `PARITY ∉ AC⁰[p]` (`p` odd prime,
constant depth) — a real classical theorem, **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`. The composite-modulus and
general-ACC⁰ cases (socket 3) are the hard frontier. No file here claims `P ≠ NP`.
