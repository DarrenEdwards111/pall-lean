# Scope: Razborov–Smolensky low-degree approximation + dimension argument

**Status:** the *exact* circuit → `MvPolynomial (Fin n) (ZMod p)` representation is **built and verified**
(`…AC0pPoly`, `…AC0pPolyMod`, `…AC0pPolyFull`: `toPoly_eval_AC0p` exact on all of `IsAC0pSyntax p`,
`sorry`-free). This doc scopes the **remaining frontier** — the *low-degree approximation* and the
*dimension argument* — that turn the (high-degree) exact representation into the lower bound
`MOD_q ∉ AC⁰[p]` (`q ≠ p` prime). **Far below P vs NP; AC⁰[p] is a higher circuit-lower-bound layer.**

---

## Why approximation (the exact degree is too high)

`toPoly` is exact but `∧`/`∨` have degree = fan-in (`∏` / `1 - ∏(1-·)`). Smolensky's argument needs the
*whole circuit* to collapse to a polynomial of degree `≈ (p-1)·(log size)^d` — polylog, not linear. So
each `∧`/`∨` gate is replaced by a **probabilistic low-degree approximant** that agrees with the gate on
a `1 - ε` fraction of inputs; over `s` gates and `d` layers the errors union-bound.

## The construction (per gate)

- **OR of fan-in `m`** (Razborov): for random `r : Fin m → ZMod p`, the form `∑ r_i x_i` is `0` on the
  all-zero input and **nonzero with probability `≥ 1 - 1/p`** on any nonzero `{0,1}` input. The Fermat
  indicator `(∑ r_i x_i)^{p-1}` is then `≈ OR`. Taking `t` independent forms and combining
  `1 - ∏_{k≤t}(1 - (∑ r^{(k)}_i x_i)^{p-1})` gives a degree-`(p-1)·t` polynomial agreeing with OR with
  error `≤ p^{-t}`. **Degree atom built:** `linFormTest` + `linFormTest_totalDegree_le` (`≤ p-1`).
- **AND**: De Morgan from OR (`¬∘OR∘¬`), same degree.
- **`MOD_p`**: already *exact* and low degree (`p-1`) — `toPoly_modGate_eval`.
- **`¬`/inputs/consts**: degree `≤ 1`, exact.

## The composition

A depth-`d`, size-`s`, `AC⁰[p]` circuit ⇒ choosing all gates' random forms with `t = O(log(s/δ))`, a
**single** polynomial `P` over `ZMod p` of degree `((p-1)·t)^d` that agrees with the circuit on
`≥ 1 - sδ` of all inputs (union bound over the `s` gates). Degree `= (O(p·log s))^d`; for constant depth
`d` and `s = exp(o(n^{1/2d}))` this is `o(√n)`.

## The dimension / counting contradiction (Smolensky)

Suppose `MOD_q` (`q ≠ p` prime) ∈ `AC⁰[p]` of small size. Then it has a degree-`Δ = o(√n)` polynomial
approximant `P` agreeing on a set `G ⊆ {0,1}^n`, `|G| ≥ (1 - 1/4)·2^n`. Smolensky:
1. On `G`, *every* function `{0,1}^n → ZMod p` agrees with a polynomial of degree `≤ n/2 + Δ` (multiply
   by the `MOD_q`-approximant and reduce via `x_i^2 = x_i` — `boolToZMod_sq`).
2. So the space of functions `G → ZMod p` has dimension `≤ #{monomials of degree ≤ n/2 + Δ} < 2^n·(1-c)`.
3. But `|G| ≥ (3/4)·2^n` forces dimension `≥ |G|` — contradiction.
The slack between `n/2 + Δ` and the function-count is where `Δ = o(√n)` (hence small depth/size) bites.

## What exists vs. the frontier

| piece | status |
|---|---|
| exact representation (all `AC⁰[p]` gates) | ✓ built, verified (`toPoly_eval_AC0p`) |
| `boolToZMod_sq` (`x² = x`, the reduction lever) | ✓ built |
| Fermat indicator (`MOD_p`, single-form atom) | ✓ built (`fermat_indicator`, `linFormTest`) |
| single-form test **degree** `≤ p-1` | ✓ built (`linFormTest_totalDegree_le`) |
| OR single-form **agreement** (`#{form ≠ 0} = p^m - p^(m-1)`) | ✓ built (`orForm_agreement`) — exact hyperplane count via the nonzero functional's kernel (`finrank_range_add_finrank_ker` + `Module.card_eq_pow_finrank`) |
| gate → approximant **degree composition** `(p-1)t` | ✓ built (`orApproxProd`, `orApprox`; `orApproxProd_totalDegree_le`, `orApprox_totalDegree_le` ≤ `(p-1)·t` via `totalDegree_finset_prod` + `linFormTest_totalDegree_le`; plus `orApprox_eval_allFalse` = `0` on all-zero input) |
| **per-gate recurrence** over sub-circuits (degree `×(p-1)t`) | ✓ built (`ComputationalDepthLayer3AC0pApprox.lean`): `genLinFormTest`/`genOrApprox` — gate approximant with `X_j` replaced by child polys `q_j` (`genLinFormTest_eq_linFormTest`: recovers `linFormTest` at `q_j=X_j`); `genLinFormTest_totalDegree_le` ≤ `(p-1)·D`, `genOrApprox_totalDegree_le` ≤ `(p-1)·t·D` for children of degree `≤ D` — each gate multiplies degree by `(p-1)t` |
| **structural depth lift** `deg ≤ ((p-1)t)^{depth}` | ✓ built (`ComputationalDepthLayer3DegreeComposition.lean`): `foldl_max_pow_le` (foldl-max power bound matching `BoolCircuitSyntax.depth`); `ApproxDegreeData` bundles the per-gate recurrence (factor `K=(p-1)t`); `approxDegree_le` — any approximant obeying the recurrence has `deg(A C) ≤ K^{depth C}` by structural induction over the circuit |
| **concrete approximant** `toApprox` + its `((p-1)t)^{depth}` degree | ✓ built (same file): `toApprox`/`toApproxList` — concrete `genOrApprox`-based approximant of a circuit (mutual recursion mirroring `toPoly`; `∨`/`∧`→`genOrApprox`, `MOD`→Fermat indicator deg `p-1`, leaves deg `≤1`), form-oracle `R` per fan-in; `toApproxData` discharges all `ApproxDegreeData` gate hypotheses; `toApprox_totalDegree_le` — `deg(toApprox C) ≤ ((p-1)t)^{depth C}` for a concrete approximant. (Form-sharing is a degree-only simplification.) **Remaining:** `MOD_q`-reduction + band margin |
| `t`-fold amplification **agreement/error** `≤ p^{-t}` | ✓ built (`orForm_zero_count` single-form bad count `p^{m-1}`; `orApprox_error_count` t-fold bad count `(p^{m-1})^t` via `Fintype.piFinset` independence; `orApprox_sample_count` total `(p^m)^t`; `orApprox_error_rate` bad·`p^t` = total, i.e. error rate exactly `p^{-t}`) |
| **per-gate evaluation agreement** (Fermat) | ✓ built (`ComputationalDepthLayer3AC0pApprox.lean`): `orApprox_eval` — `eval(orApprox) = 0` iff all forms vanish, else `1` (via `ZMod.pow_card_sub_one_eq_one`); `orApprox_disagree_count` — for nonzero input the approximant errs (output `≠ OR = 1`) on exactly the `(p^{m-1})^t` bad-form set. The one-sided-error half over the form space |
| **gate eval over child values** (`genOrApprox`) | ✓ built (same file): `genOrApprox_eval` — `eval pt (genOrApprox p R q) = 0` iff every form `∑_j R s j · eval pt (q_j)` vanishes, else `1` (Fermat); `genOrApprox_eval_eq_orApprox_eval` recovers the variable case; gate-correctness steps `one_sub_boolToZMod` (NOT) and `genOrApprox_eval_orOfChildren` (OR computes children's OR given children correct + form-goodness) |
| **recursive agreement lift** (full AC⁰[p]: OR/AND/NOT/MOD/leaf) | ✓ built (`ComputationalDepthLayer3Agreement.lean`): `toAgree` faithful single-function approximant (`termination_by sizeOf`, clean `Fin cs.length` indexing; `∨`→`genOrApprox`, `∧`→De Morgan, `¬`→`1-child`, `MOD`→Fermat indicator `1-(∑child-r)^{p-1}`, leaves→`X`/`C`); `AgreeGood` per-input goodness (per `∨`/`∧` gate: gate fires ⇒ some form over relevant true values nonzero; `MOD` gate: `q=p`); `orGate_eval_iff`/`andGate_eval_iff` (`.any`/`.all` ↔ indexed ∃/∀); `sum_boolToZMod_get` (modular count: ∑ boolToZMod = #true cast); `toAgree_eval` — **AgreeGood x R C ⇒ eval_x(toAgree C) = boolToZMod(C.eval x)** by structural induction over *all* AC⁰[p] gates. The circuit approximant computes the circuit exactly on every *good* input. **Remaining:** probabilistic "most inputs good" + `MOD_q`-reduction + band margin |
| depth-`d` **union bound** over gates | ✓ counting core built (`ComputationalDepthLayer3DimensionCount.lean`): `badUnion_card_le` (`|⋃ B_i| ≤ ∑|B_i|`); `agreement_card_ge` — agreement set `|G| ≥ 2^n - s·δ`; `agreement_card_ge_three_quarters` — `4sδ ≤ 2^n ⇒ 3·2^n ≤ 4|G|` (the `|G| ≥ ¾·2^n` input). **Remaining:** per-gate approximants wired in + depth-`d` degree `((p-1)t)^d` |
| **probabilistic averaging** (first moment) | ✓ built (`ComputationalDepthLayer3Averaging.lean`): `exists_card_mul_le_sum` (min-≤-mean: `s.card·f ω ≤ ∑f` for some `ω`); `orApprox_badForm_card_le` (per-input bad-form count `≤ (p^{m-1})^t`, eq for nonzero, 0 for all-false); `exists_form_few_errors` — via Fubini (`sum_comm`) + averaging, **∃ a form tuple `R` with `(p^m)^t·E ≤ 2^m·(p^{m-1})^t`** erring inputs `E` (input-error rate `≤ 2^m·p^{-t}`) for one OR gate. Turns per-input/over-forms error into ∃-form/over-inputs error |
| **circuit-level averaging** (joint form space) | ✓ built (same file): `exists_le_sum_of_sum_le` (first moment over a sum of per-gate error functions); `exists_form_total_errors` — with `Φ` the joint form space, composed bad ⊆ ∪ per-gate bads (`hsub`) and per-gate column-sum bounds `Bᵢ`, **∃ a single joint form `ω` with `Φ.card·\|cbad ω\| ≤ ∑ᵢ Bᵢ`** (composed-error rate `≤ (∑Bᵢ)/\|Φ\|`). Combines per-gate averaging + union bound into one form choice — the structural lift |
| **composed error ⊆ goodness failure** (`hsub` ingredient) | ✓ built (`ComputationalDepthLayer3Agreement.lean`): `toAgree_bad_imp_not_good` (contrapositive of `toAgree_eval`: approximant errs at `x` ⇒ `¬AgreeGood x R C`); `toAgree_cbad_subset` (Finset form: composed-error set ⊆ `{x : ¬AgreeGood}`). **Remaining (architectural):** decompose `¬AgreeGood` into a union over *independently-formed* gates — needs a per-gate-indexed form space (the shared-fan-in oracle blocks the faithful joint instantiation) + `MOD_q`-reduction + band margin |
| Smolensky **dimension** bound (#low-degree monomials) | ✓ count built (`ComputationalDepthLayer3DimensionCount.lean`): `lowDegMonomials_card` = `∑_{k≤D} C(n,k)`; `_full` = `2^n`, `_le_two_pow`, `_lt_two_pow` (strict for `D<n`); `_halfway` exact `2^{2m}=2^{n-1}` at the half-degree; `boolToZMod_pow_succ` (`x^{e+1}=x`) the multilinear lever. **Remaining:** quantitative band margin `< (3/4)·2^n` at `D=n/2+o(√n)` (central-binomial/entropy estimates) |
| **dimension ≤ #monomials** linear-algebra bridge | ✓ built (same file): `squarefreeEvalMonomial` (cube eval `x↦∏_{i∈S} x_i`); `finrank_span_lowDegEval_le_card`/`_le_sum` — the span of the degree-`≤D` squarefree eval functions has `finrank ≤ (lowDegMonomials n D).card = ∑_{k≤D} C(n,k)` (`finrank_span_le_card`); `squarefreeEvalMonomial_mem_span` (generators in span). **Remaining for this half:** every cube function lands in this span after the `MOD_q`-reduction (the composition step) |
| **dimension deficit** (low-degree can't span the cube) | ✓ built (same file): `finrank_cubeFunctions_eq` = `2^n`; `lowDegEval_span_ne_top` — for `D<n` the degree-`≤D` squarefree evals do **not** span `(Fin n→Bool)→ZMod p` (else `2^n ≤ #monomials < 2^n`); `exists_cubeFunction_not_lowDegEval` — a concrete unrepresented Boolean function. The contradiction skeleton: `MOD_q`-reduction would force everything into a degree-`<n` span |
| **algebraic lever** (monomials closed under × on cube) | ✓ built (same file): `squarefreeEvalMonomial_mul` — `e_S·e_T = e_{S∪T}` (overlap absorbed by `x²=x`); `squarefreeEvalMonomial_empty` — `e_∅ = 1`; `squarefreeEvalMonomial_mul_card_le` — degree **subadditive** `deg(e_S·e_T) = |S∪T| ≤ |S|+|T|`. Function-level form of the `boolToZMod_sq`/`_pow_succ` lever; the algebraic engine for the composition step |
| **spanning** (monomials span the whole cube space) | ✓ built (same file): `squarefreeSpan` = span of all squarefree evals; `mul_mem_squarefreeSpan` (span is a subalgebra, via `span_mul_span` + the lever); `prod_mem_squarefreeSpan`; `single_eq_prod_factor` — `Pi.single y 1 = ∏_i (y_i? x_i : 1-x_i)`; `squarefreeSpan_eq_top` — the monomials span `(Fin n→Bool)→ZMod p` (indicators are a basis); `mem_squarefreeSpan` — **every Boolean function is a multilinear polynomial over ZMod p**. The full easy direction `dim = #monomials` (D=n); the `MOD_q`-reduction lowering this to degree `n/2+Δ` on the agreement set `G` is the remaining composition piece |
| final `MOD_q ∉ AC⁰[p]` | the capstone (do **not** build until the above are real) |

## Suggested brick order (bricks 1–2 now built)

1. ✓ **OR single-form agreement:** `∀` nonzero `{0,1}` input `x`, `#{r : ∑ r_i x_i ≠ 0} = p^m - p^{m-1}`
   (counting, via the nonzero linear form being surjective / a hyperplane complement). *The genuine
   first analytic brick.* (`orForm_agreement`)
2. ✓ **`t`-fold amplification:** product of `t` tests ⇒ error rate exactly `p^{-t}`, degree `≤ (p-1)t`
   (`orApproxProd`/`orApprox`, `orApprox*_totalDegree_le`; `orApprox_error_count`/`_sample_count`/
   `_error_rate`).
3. ✓ **Dimension count + linear-algebra bridge:** `#{monomials of degree ≤ D}` = `∑_{k≤D} C(n,k)` with
   `= 2^n` / `< 2^n` / half-degree `= 2^{n-1}` comparisons, the `x²=x` reduction lever, AND the
   `dimension ≤ #monomials` span bridge `finrank_span_lowDegEval_le_card/_le_sum`
   (`ComputationalDepthLayer3DimensionCount.lean`). *Remaining sub-frontiers: (a) the quantitative band
   margin `< (3/4)·2^n` at `D = n/2 + o(√n)`; (b) every cube function in the span after the
   `MOD_q`-reduction.*
4. Only then the composition + final separation.

*Roadmap for the analytic frontier; the exact-representation foundation it refines is complete. Not P vs
NP.*
