# P vs NP project — Phase 1: actual starting point (dependency map)

Prepared 2026-10-31 (Europe/London, GMT). Author: Grok Bot (research agent for Dr. Darren Edwards).
Honesty convention: every claim below is tagged **[K]** kernel-checked in Lean (with the axiom
list stated), **[C]** computed (script in `scripts/spdp_obstruction/`), **[I]** informal argument in the
paper only, **[X]** disproved (with the disproof's status), **[O]** open/conjectured.
Nothing here proves or claims P ≠ NP or P = NP.

## 0. Sources read (commit hashes)

| Source | Commit | Notes |
|---|---|---|
| `pall-lean` main | `7f539465ca9a850d525517dc8196dd9cb9b68840` | merge of `research/decision-invariant-audit-20261026` (422103fe) into main; HEAD contains 7f53946 ✔ |
| **PRIMARY paper** `P vs NP Paper.pdf` | added in `6db143865713f7258adc4a95a64a7ffa833d4659` | sha256 `c39b7045…26240`; **byte-identical** to `p-vs-np1.pdf`/`paper.pdf` in the repo = arXiv 2512.11820 **v5** (8 Jan 2026, 280 pp). arXiv lists v5 as the latest version (checked 2026-10-31). |
| `pall-lean` `codex/godmove-gap-repairs` | `219219589f742d6e8cb104d0a3b12f3557efcd6a` | 226 commits **not merged** into main (Sep 2026 God-Move gap-repair audits, `WHAT_IS_PROVED.md`, `research-audits/`) |
| `pall-lean` `paper-faithful` | `4c5c2d0029ed40abbd13e6bf4963c4e41d46624e` | Mar 2026; `TRUST_BOUNDARY.md`, `ARCHITECTURE_MISMATCH.md` |
| `mikoshi-geometric-intuition` main / `research/partition-robust-rank` | `548e9630…` / `3563c26838aee34ca2a74988814e53d3d4992a70` | latest note 27 Oct 2026 (God-Move 26 boundary response). **No "God-Move 36" (29 Oct) artefact exists in either repo.** |
| `spdp-observer-p-vs-np` | `45382ae1f43d51d9533ab26529156fa514505cf6` | reference only |
| `cicw-spdp-p-vs-np-proof` | `d6203d134d14c4b3a373736c9379f3531a025181` | reference only (2025 TeX) |

Mikoshi notes reference desktop PDFs `pall (50).pdf` and `n_np (1).pdf` that are **not in any repo**.

## 1. Build and audit status (main @ 7f53946)

* Toolchain `leanprover/lean4:v4.28.0`, Mathlib `v4.28.0` (rev 8f9d9cff6b), Mathlib cache via `lake exe cache get`.
* `lake build PallLean` (default target = active entrypoint `PallLean.lean`, 42 project modules, ~97.5k lines,
  `Step4Compiler.lean` alone 54.8k lines): **Build completed successfully (8068 jobs), 0 errors.**
  The project modules were first compiled on the byte-identical `codex/godmove-gap-repairs` closure, then
  `lake build` on main replayed them by content hash (all 42 closure files are byte-identical; only `PallLean.lean`
  differs: gap-repairs adds two imports). Warnings only (linter).
* The full repository has 5,159 `.lean` files; **only the entrypoint closure was built**. The other ~5,100 files
  (Paper93/DeepMath/…, Archive/…) were only text-scanned, not compiled.

### 1.1 Comment-aware scan (strings and comments stripped) — whole repo, main
| token | live (non-archive) | archive |
|---|---|---|
| `axiom` | 5 | 90 |
| `sorry` | 4 (all in `Paper93/Concrete/RamanujanGraph.lean`) | 43 |
| `admit` | 0 | 1 |
| `native_decide` | 50 | 20 |
| `opaque` | 2 | 0 |
| `implemented_by`, `@[extern]`, `unsafe`, `debug.skipKernelTC`, `ofReduceBool` | 0 | 0 |

Live axioms: `PAC.gadget_spdp_subspace_factoring`, `PAC.gadget_spdp_subspace_factoring_paperFaithful`,
`MatrixSPDP.gadget_factoring_linearmap_form` (**all three in the active entrypoint closure**),
`ComputationalDepthRAMBeigelTaruiAxiom.beigelTarui_faithful`, `ComputationalDepthRAMNexpAxiom.williams_decider_in_NEXP`
(+ `opaque acc0Sim`, `opaque WilliamsNEXP`; not in the entrypoint closure).
In the entrypoint closure: 3 axioms, 0 sorry, 11 `native_decide` (all in `BinomialBound2.lean`; the load-bearing
`BinomialBound.binomial_lower_bound_concrete` does **not** depend on them — see 1.2).

### 1.2 `#print axioms` (file `research-audits/dependency-map/KeyAxioms.lean`) [K]
| declaration | axioms |
|---|---|
| `Step4Compiler.P_ne_NP_Lean` (only `P ≠ NP` theorem in the closure) | propext, Quot.sound — **but it takes two hypotheses, see §3** |
| `PaperFaithfulSeparation.separation_3sat`, `no_rank_sandwich_at_large_n`, `rank_sandwich_axiom_iff_no_bounded_sat_decider`, `isAmplituhedronGauge_uninhabited_for_sat_decider` | standard 3 |
| `GodMoveReal.compiled_np_lower_bound_any_dtm`, `compiledPoly_rank_gt_npow200_at_large_n` | standard 3 |
| `GlobalGodMoveGauge.theorem207RawSourcePSideUpperBound_not_for_local_compiledPoly`, `theorem207PaperSource_transport_false` | standard 3 |
| `Step4Compiler.P_side_rank_concrete_bound`, `P_side_rank_concrete_lt_NP_side`, `BinomialBound.binomial_lower_bound_concrete` | standard 3 |
| `PAC.gadget_multiplication_rank_bound` | + **`PAC.gadget_spdp_subspace_factoring`** |
| `MatrixSPDP.gadget_multiplication_rank_bound_matrix_form` | + **`MatrixSPDP.gadget_factoring_linearmap_form`** |

A full census of every theorem in the closure (`AxiomCensus.lean`, meta `#eval` over all `PallLean.*` constants) was started but **did not finish**: it was killed after 28 min wall / 14 min CPU (uncached `collectAxioms` per constant, box shared, pinned to 3 cores). No census output exists; the axiom picture above rests on the comment-aware token scan of all files plus targeted `#print axioms` (KeyAxioms.lean). Re-run on an idle machine to complete it.

### 1.3 New kernel-checked audit results (this phase) [K]
* `research-audits/dependency-map/AxiomInconsistency.lean`:
  `Phase1Audit.gadget_spdp_subspace_factoring_false : False` — axioms `[propext, Classical.choice, PAC.gadget_spdp_subspace_factoring, Quot.sound]`;
  `Phase1Audit.gadget_factoring_linearmap_form_false : False` — axioms `[…, MatrixSPDP.gadget_factoring_linearmap_form, …]`.
  **Both custom axioms in the active entrypoint are refutable; the Lean environment of `PallLean.lean` is
  inconsistent** (anything is derivable from either). Instance: N=2, gadget X₀, p=X₁, κ=1, ℓ=0, singleton blocks
  (the repo had documented this counterexample in `Archive/GadgetSubspaceFactoringCounterexample.lean` but had
  not derived `False`). The inclusive-κ `…_paperFaithful` axiom is not refuted by this instance (status open).
  Currently no headline theorem depends on them (per 1.2), so their effect is confined to the gadget-rank lemmas,
  but they must be removed or turned into hypotheses.
* `research-audits/dependency-map/PeqNPPaperInhabited.lean`:
  `Phase1Audit.trivialPeqNP : PeqNP_Paper` and `hsep_refuted : ¬ (PeqNP_Paper → False)` — axioms `[propext, Quot.sound]`.

## 2. Definitions audit

### 2.1 Machine model, P, NP (active closure: `TuringMachine.lean`, `Step4Compiler` §142)
* `TuringMachine.DTM`: single tape, **binary alphabet with no blank / end marker**, ≥3 states (0 start, 1 accept,
  2 reject), and a declared exponent `timeBound`; `accepts M n` := accept state reached within `n^timeBound` steps on
  a tape of length `n^timeBound+1` (clocked machines). Nonstandard: the machine cannot see where the input ends,
  and the time bound is a field, not a measured quantity. Equivalence of the resulting class with textbook P is
  **not proved** (and is doubtful for length-sensitive languages).
* `Step4Compiler.P := ⋃ k, DTIME(n^k+1)` and `NP` := verifier-based with `V x w ↔ Mv accepts (x ++ w)` (no
  separator between x and w), witnesses `|w| ≤ p|x|`. Uniform. Standard *in shape*, but built on the
  nonstandard DTM; `DTM_Decides` ignores the empty string.
* **SAT (legacy, used by the God-Move route): `PaperFaithfulSeparation.ThreeCNF` has only positive literals**
  (clauses are triples of variable indices), so every formula is satisfiable; `DecidesSAT M` never relates the
  accepted input to the formula. Kernel-checked (repo + this phase): `DecidesSAT M ↔ ∀ n ≥ 1, ∃ input accepted`,
  inhabited by a 3-state always-accept machine. **Verdict: not SAT.**
* `PeqNP_Paper` additionally fixes `timeBound ≤ 4` and `numStates ≤ 2^804` "WLOG" — **not WLOG** (padding changes
  the language/encoding; state counts are unbounded). Irrelevant now, because the structure is trivially inhabited.
* **Faithful target (not in the entrypoint closure):** `Paper93/DeepMath/PathB/ComputationalDepthSeparationTarget.lean`,
  `SeparationTarget.SAT_not_in_P := ¬ InP SATLang` with `ComposableMachine` (finite control, halt flag, tape
  extendable, decision at halt, correctness on **every** input within a `C·n^k+C` clock) and a self-delimiting
  coordinate codec with signed literals (`SATLang_encode` proved). This is a reasonable uniform "SAT ∉ P"; the machine
  also cannot see input end, but the codec reads missing bits as `false`, so `SATLang` is plausibly
  padding-invariant. Suggested sanity lemmas (not yet proved): `SATLang (x ++ [false]) = SATLang x` and
  `InP` = textbook P on padding-invariant languages. **No theorem anywhere proves this target** (the file says so).
* Uniform vs non-uniform: everything is uniform (Turing machines). Nothing claims SAT ∉ P/poly. The rank
  arguments themselves are per-length (non-uniform in character), so a correct version would prove the stronger
  non-uniform statement — relevant for the natural-proofs obstruction (§5).

### 2.2 The SPDP measure — exact definitions
* **Paper Def. 12 (v5, p.32):** p ∈ F[x₁..x_N], block partition B (blocks of size O(1)); rows (τ,u): multi-index τ
  with |τ| = κ (strict) and block support ≤ κ, u **any** monomial of degree ≤ ℓ; columns = multilinear monomials of
  degree ≤ deg p − κ + ℓ, ambient "multilinear basis modulo ⟨x_i² − x_i⟩"; entry coeff_{x^β}(u·∂^τ p);
  Γ^B_{κ,ℓ}(p) = rank over F, char 0 (or p > poly(n)). Parameters κ, ℓ = Θ(log n) (Thm 5; Thm 92 uses ⌊α log n⌋, ⌊β log n⌋).
  Elsewhere (Lemma 40(c), Def. 12 recap) the paper uses |α| ≤ κ (inclusive) — the paper is internally inconsistent
  on strict vs inclusive κ (the repo documents this).
* **Lean `MultilinearSPDP.mlBlockedSpdpSubspace B κ ℓ p`** = span{ mlProj(m · ∂_S p) : S ordered list, |S| = κ,
  Nodup, ≤1 variable per block, m monomial with totalDegree ≤ ℓ **and vars(m) ⊆ S** }, rank = `finrank ℚ`.
  `mlProj` **deletes** non-multilinear monomials (Finsupp.filter), it does **not** reduce x² → x.
  Differences from the paper: (i) shift restricted to vars ⊆ S ("Lemma 18"), (ii) drop vs reduce, (iii) strict κ;
  `…Inc` variant is inclusive. `compilerBlockPartition` = identity (singleton blocks), so block admissibility is
  vacuous apart from Nodup.
* **Which polynomial:** Item 1 is about the compiled tableau polynomial P_{M,n} (Thm 92: "constant-degree",
  P = Y·V with V = Σ C², Y = κ padding variables, `TuringMachine.compiledPoly`); the Lean God-Move route instead
  uses `cook_levin_compilation` (toy: N = n vars, booleanity/adjacency/skeleton constraints) with the **product**
  form ∏(1 − C_i). Item 2 is about the coupled clause-sheet Q×_Φ = ∏_C (1 − z_C V_C²) for a Ramanujan–Tseitin
  family. Sections 11.1 / Thm 10 / Thm 46 / Cor 47 apply the measure to the multilinear extension χ_L of a P
  language (function level), with **constant** ℓ ∈ {2,3} (Thm 46) or κ ≤ (log n)^C (Thm 10).

## 3. Final statement(s)

* **Paper (primary):** Theorem 5 (single-statement form, p.19) and Theorem 207 (Route B, "Global God-Move
  separation", declared the main theorem): P ≠ NP (uniform, textbook classes) from three items, at κ = ℓ = Θ(log n),
  same block partition B:
  1. ∀ M ∈ DTIME(n^c): Γ^B_{κ,ℓ}(P_{M,n}) ≤ n^{O(1)} (Thm 92 / Thm 23 / Lemma 31 / Thm 170);
  2. explicit 3SAT family Φ_n with Γ^B_{κ,ℓ}(Q×_{Φ_n}) ≥ n^{Θ(log n)} (Thm 128, Lemma 89);
  3. witness-free, instance-uniform T_Φ with T_Φ(P_{M′,N(Φ)}) = Q×_Φ and Γ(T_Φ p) ≤ Γ(p) ∀p (Def. 6, Lemma 7, Thm 223).
  Route A (Thm 12 / Thm 147) additionally relies on Lemma 13 "normal-form invariance" (two descriptions of the same
  Boolean function compile to rank-equivalent objects).
  The paper claims P ≠ NP outright ("unconditional in the logical sense"), not SAT ∉ P/poly.
* **Lean (main):** the only theorem concluding `P ≠ NP` in the entrypoint closure is
  `Step4Compiler.P_ne_NP_Lean (hsep : PeqNP_Paper → False) (hExtract : P = NP → PeqNP_Paper) : P ≠ NP`.
  **hsep is false** [K, this phase], hExtract is trivially true; the theorem is vacuous. The old
  `P_ne_NP_unconditional` was moved to `Archive/Paper93Unsafe` (it derived False from the inconsistent
  `spdp_profile_generators` axiom, documented in `PaperFaithfulSeparation.lean`). The many `P_ne_NP_*` theorems
  under `Paper93/` and `Archive/` are wrappers over hypotheses/axioms, not imported by the entrypoint.
  The repo's own `WHAT_IS_PROVED.md` (gap-repairs branch) states: "This is not a proof of P ≠ NP."
* **Does the formal statement express the separation?** The `P`/`NP` of §142 roughly do (modulo the DTM model
  issues), but the route to it goes through the non-SAT `DecidesSAT`. The faithful target `SAT_not_in_P` exists
  but nothing connects the God-Move machinery to it.

## 4. Proof-dependency map (critical path of Theorem 5 / 207)

```
Thm 5 / 207  P ≠ NP
 ├─ Item 1  P-side: ∀M∈P, Γ^B(P_{M,n}) ≤ n^O(1)                     ← EARLIEST GAP (see §6)
 │    ├─ Lemma 19 / Thm 93 sorting-network compiler, CEW = O(log N)      [I]
 │    ├─ Lemma 20/29 profile count |H(R)| ≤ R^O(1)  (stars & bars)        [I, elementary, fine]
 │    ├─ Lemma 25 bounded normal forms in a finite monoid                 [I, fine if the monoid is finite]
 │    ├─ Lemma 26 canonical windows preserve rows                         [I]
 │    ├─ Lemma 27 permutation-invariance ⇒ "only the histogram matters"   [X as an inference: equal rank ≠ common span
 │    │                                                                     (mikoshi REVIEW, joint dim C(R,R/2) vs 1, Python)]
 │    ├─ Lemma 31 rows of profile h lie in ⊗_σ Sym^{h(σ)}(W_σ)            [X as stated: distinct interfaces are distinct
 │    │                                                                     coordinates; identifying them loses rank]
 │    ├─ Thm 23 Width⇒Rank                                                [I; depends on Lemma 31]
 │    ├─ Thm 92(2) for the SoS encoding P = Y·ΣC²  (degree ≤ 6+κ)         [K trivially: rank 0 once κ > deg — 
 │    │                                                                     `mlBlockedSpdpRank_eq_zero_of_totalDegree_lt_kappa`; vacuous]
 │    ├─ Lean product encoding ∏(1−C_i): `CookLevinProfileTemplateCollapseLemma` [X, K: `existing_product_template_collapse_false`
 │    │                                                                     (gap-repairs branch) and `compiledPoly_rank_gt_npow200_at_large_n`]
 │    ├─ old axiom `spdp_profile_generators`                              [X, K: inconsistent with `compiled_np_lower_bound_any_dtm`; archived]
 │    ├─ `PAC.gadget_spdp_subspace_factoring`, `MatrixSPDP.gadget_factoring_linearmap_form` (Lemma 40(c)) [X, K this phase]
 │    └─ function-level variants (Thm 10, Thm 46/Cor 47, `ptime_spdp_collapse` on `paper-faithful`)
 │                                                                         [X at κ=Θ(log n): AND/x₁⋯x_n, parity, point indicator — §5.1 [C];
 │                                                                          vacuous at constant κ,ℓ: Γ ≤ n^{κ+ℓ} for every polynomial]
 ├─ Item 2  NP-side: Γ^B(Q×_Φn) ≥ n^Θ(log n)
 │    ├─ identity minor / binomial bound C(n/3, log n) ≥ n^{log n/4}      [K for the Lean objects: `compiled_np_lower_bound_any_dtm`,
 │    │                                                                     `binomial_lower_bound_concrete`, standard axioms]
 │    └─ BUT the Lean bound holds for compiledPoly of **every** DTM       [K] → shows the Lean "NP side" is structural (booleanity
 │                                                                          factors), not about SAT; Ramanujan–Tseitin specifics [I]
 ├─ Item 3  God-Move T_Φ, witness-free, rank-monotone, T_Φ(P_{Msol}) = Q×_Φ
 │    ├─ rank monotonicity of coordinate restriction/projection            [K: GaugeMonotonicity, `GodMoveProductSourceExtraction` (gap-repairs)]
 │    ├─ nonlinear elimination is not rank-monotone                        [X generic monotonicity, K: `GodMoveAccumulatorRankCheck` (gap-repairs)]
 │    ├─ local-energy source does not dominate the product                 [X no-loss bridge, K: `GodMoveLocalEnergyRankObstruction` (gap-repairs)]
 │    ├─ T_Φ(P_{M′}) = Q×_Φ for the actual compiler                         [O; Lean only has abstract interfaces
 │    │                                                                     `Theorem207PaperSourcePSideUpperBound` + `…ToTargetRankBridge`]
 │    └─ Witness-free + machine-independent ⇒ "proves too much"            [obstruction, §5]
 └─ classical bridge P=NP ⇒ PeqNP_Paper                                    [vacuous: PeqNP_Paper inhabited, K]
```

## 5. Obstructions and which apply

### 5.1 Computed small-n tests of the exact measure [C]
Script `scripts/spdp_obstruction/spdp_rank.py` (results `results.json`, `run.log`; exact `Fraction` cross-check
`exact_check.py`/`exact_check.log`, all cases agree with the mod-(2³¹−1) ranks). Singleton blocks
(= `compilerBlockPartition`), κ = ℓ = ⌊log₂ n⌋. Columns: LEAN-drop (Lean definition), PAPER-reduce (Def. 12
with x²→x), PAPER-drop.

| polynomial (cheap circuit) | n | κ=ℓ | LEAN-drop | PAPER-reduce | PAPER-drop | C(n,κ) |
|---|---|---|---|---|---|---|
| x₁⋯x_n (n−1 ANDs) | 4 / 8 / 9 / 10 / 11 | 2/3/3/3/3 | 11 / 93 / 130 / 176 / 232 | same | same | 6 / 56 / 84 / 120 / 165 |
| parity (MLE, O(n) gates) | 4 / 8 / 10 / 11 | | 11 / 93 / 176 / 232 | 16 / 247 / 848 / 1486 | 16 / 247 / 848 / 1486 | |
| point indicator (n ANDs, ≤n NOTs) | 8 / 10 / 11 | | 93 / 176 / 232 | 93 / 176 / 232 | 236 / 762 / 1209 | |
| e_{n,⌊n/2⌋} (O(n²) DP) | 8 / 9 / 10 | | 148 / 213 / 405 | 162 / 255 / 627 | 162 / 255 / 627 | 56 / 84 / 120 |
| det₃ (9 vars) | 9 | 3 | 34 | 130 | 130 | 84 |
| det₂ (4 vars) | 4 | 2 | 7 | 11 | 11 | 6 |
| IMM 2×2, d=2, entry (1,1) | 8 | 3 | 0 | 0 | 0 | 56 | 
| IMM 2×2, d=3, entry (1,1) | 12 | 3 | 25 | 299 | 299 | 220 |
| x₁⋯x_n at κ=n/2, ℓ=0 | 4 / 6 / 8 / 10 | 2/3/4/5 | 6 / 20 / 70 / 252 | same | same | 6 / 20 / 70 / 252 (= C(n,n/2), exponential) |

(IMM d=2 is degree 2 < κ=3, so every κ-th derivative vanishes; the 0 is trivial, not informative.)

**Analytic fact (all three conventions):** for p_n = x₁⋯x_n, the ℓ=0 rows ∂_S p_n = x_{[n]∖S} are distinct
multilinear monomials, so Γ_{κ,ℓ}(p_n) ≥ C(n,κ) ≥ (n/κ)^κ = n^{Ω(log n)} at κ = ⌊log₂ n⌋ (Lean convention exactly:
Σ_{j≤ℓ} C(n, n−κ+j), matching the table, e.g. 93 = 56+28+8+1). This is the **same order** as the NP-side bound
C(n/3, log n) used in Item 2. Hence at the paper's parameters the measure on function polynomials cannot separate a
trivially easy function from the hard family; at constant κ,ℓ (Thm 46) every polynomial has Γ ≤ C(n,κ)·n^ℓ = poly,
so no superpolynomial lower bound is possible. This confirms Darren's 29 Oct finding (God-Move 36) for the **exact**
Lean and Def. 12 measures, and matches `paper-faithful/ARCHITECTURE_MISMATCH.md` (parity). Applies to: Thm 10,
Thm 46/Cor 47 at κ = Θ(log n), `ptime_spdp_collapse`, and any "all-circuit upper bound on the function polynomial".
It does **not** by itself refute Item 1 for compiled tableau polynomials (different object); there the kernel
results of §4 do the work.

### 5.2 Structural obstructions
* **Proves too much / semantics-free P-side bound.** Items 1+3 give Γ(Q×_Φ) ≤ Γ(P_{M,·}) for the solver. If the
  P-side bound is proved structurally (degree, locality, profile counting — as in the paper) it holds for every
  machine, and if T_Φ is witness-free and machine-independent the chain contradicts Item 2 for *any* M, i.e. it
  would refute a true statement. In Lean this already happened (`compiled_np_lower_bound_any_dtm` holds for every
  DTM; `spdp_profile_generators` was inconsistent). Any repair must make Item 3 depend on M's SAT-correctness. **Applies.**
* **Encoding dilemma (kernel-checked on both horns):** constant-degree SoS encoding ⇒ Γ = 0 for κ > deg (Item 1
  trivially true, Item 2/3 impossible on that object); product encoding ∏(1−C_i) ⇒ Γ ≥ C(n/3, log n) for every
  machine (Item 1 false). **Applies.**
* **Natural proofs (Razborov–Rudich).** Γ of the multilinear extension is computable in 2^{O(n)} time from the truth
  table (constructive) and, from §5.1, large for most functions (parity/point indicator/AND already near maximal) —
  the function-level measure is natural; the paper's "sparse hard family ⇒ not large" argument (§11.8) does not
  address largeness of the *property*. Applies to function-level variants; for compiled-object variants unclear. **Partially applies.**
* **Relativization (BGS).** The paper's claim that it is non-relativizing is informal [I]; arithmetization-based
  arguments typically face **algebrization** (Aaronson–Wigderson) — not addressed formally. **Open/likely applies.**
* **Known limits of partial-derivative measures:** shifted-partials lower bounds are known only for restricted
  (depth-4, homogeneous, etc.) models; polynomial-size circuits compute polynomials of near-maximal shifted-partial
  rank (e.g. det, IMM, or simply x₁⋯x_n at κ=Θ(log n) as above). **Applies** to any all-circuit upper bound.
* **Paper inconsistencies:** strict vs inclusive κ (repo-documented); Lemma 13 (Route A) "normal-form invariance"
  would make Γ a function of the Boolean function, which §5.1 shows is superpolynomial for AND — so Route A's
  Lemma 13 + Step 4 are jointly false at κ = Θ(log n). **Applies.**

## 6. Earliest substantive gap on the critical path

The first load-bearing step that is not established is **Item 1 (P-side Width⇒Rank)**, and inside its proof the
earliest failing inference is **Lemma 31 (with Lemma 27)**. Stated exactly:

> **Lemma 31 (paper v5, p.43–44).** Let p = P_{M,n} be the compiled polynomial of a DTM M ∈ DTIME(n^c) under the
> radius-1 diagonal-basis compiler, with block partition B, at most R = C(log n)^c live interfaces per step, local
> alphabet Σ, finite local monoid with normal forms of length ≤ q = O(1), and κ = ℓ = Θ(log n). Then for every
> interface-anonymous profile h : Σ^{≤q} → ℕ, all rows of M^B_{κ,ℓ}(p) whose interface type statistics equal h lie in
> one subspace V_h with dim V_h ≤ (log n)^{O(1)}; consequently Γ^B_{κ,ℓ}(p) ≤ Σ_h dim V_h ≤ n^{O(1)}.

Status: **the proof is invalid** — it places the joint contribution of h(σ) *distinct* interfaces (distinct
variables/coordinates) in Sym^{h(σ)}(W_σ), i.e. it identifies different coordinates; Lemma 27 only gives equality of
ranks under permutation, not a common span. Generic counterexample: C(R,R/2)-dimensional joint span vs 1-dimensional
symmetric quotient (mikoshi `paper_compression_audit/REVIEW.md`, Python). The *conclusion* is false for the Lean
product compiler [K], vacuous for the SoS compiler [K], and false for function polynomials at κ = Θ(log n) [C + analytic].

Because the lemma as stated is false/unprovable, the earliest **open** statement worth attacking is its repaired
form (this is what any continuation must supply):

> **Gap G (semantic compiled bound — same object, correctness-dependent).** There exist an explicit polynomial-size
> encoding (M,n) ↦ (S_{M,n} ∈ ℚ[x₁..x_N], B_{M,n}), N ≤ n^{O(1)}, and constants such that
> (G1) for every DTM M with time n^c: Γ^{B}_{κ,ℓ}(S_{M,n}) ≤ n^{d(c)} at κ = ℓ = ⌊log₂ n⌋, n ≥ n₀(M);
> (G2) for every M that decides SAT in the faithful sense of `SeparationTarget.Decides M SATLang T`, there is a
> composition T of coordinate restrictions/projections and invertible block-local linear maps with
> Γ^{B′}_{κ,ℓ}(T(S_{M,n})) ≥ C(n/3, ⌊log₂ n⌋) (the identity minor of Q×_{Φ_n});
> (G3, necessary sanity) (G2) fails for some polynomial-time M that does not decide SAT (otherwise G1+G2 is
> refutable outright — "proves too much"), and S_{M,n} must not contain any cheap product such as x₁⋯x_m with
> m ≥ n^{Ω(1)} multiplicatively (otherwise G1 fails by §5.1 via `GodMoveProductSourceExtraction`).
>
> G1 ∧ G2 ⇒ `SeparationTarget.SAT_not_in_P`. G is at least as hard as P ≠ NP and must evade natural proofs,
> relativization and algebrization; no candidate S is known. [O]

## 7. Next actions
1. **Hygiene (Lean, now):** delete or demote to hypotheses the three refuted/unsupported axioms in `PAC.lean` /
   `MatrixSPDP.lean` (two are refuted by `AxiomInconsistency.lean`); fix or quarantine `ThreeCNF`/`DecidesSAT` and
   `PeqNP_Paper` (use signed literals + `SeparationTarget` semantics); retire `P_ne_NP_Lean` or restate it against
   `SAT_not_in_P`.
2. Prove the sanity lemmas `SATLang (x++[false]) = SATLang x` and (harder) equivalence of `ComposableMachine.InP` with
   a standard TM class on padding-invariant languages, so the faithful target is certified to mean "SAT ∉ P".
3. Formalize the §5.1 analytic fact in Lean: `mlBlockedSpdpRank (singletons) κ 0 (∏ X i) ≥ Nat.choose n κ` — turns the
   God-Move 36 finding into a kernel-checked no-go for any function-level all-P upper bound at κ = Θ(log n).
4. Decide with Darren whether to (a) abandon Item 1 in its rank-of-compiled-polynomial form, or (b) propose a concrete
   S_{M,n} for Gap G and test G1 at small n (compiled tableaux of 2–3 tiny machines; script skeleton in
   `scripts/spdp_obstruction/`), checking G3 first.
5. If a newer manuscript than arXiv v5 exists (e.g. `pall (50).pdf`, `n_np (1).pdf`), re-run this audit against it.

## 8. Run log / reproducibility
* Build: `lake build PallLean` on main 7f53946 → success (warnings only). Toolchain via elan; `lake exe cache get`.
* Axiom outputs: `research-audits/dependency-map/KeyAxioms.lean`, `AxiomInconsistency.lean`,
  `PeqNPPaperInhabited.lean` (`lake env lean <file>`), census `AxiomCensus.lean`.
* SPDP tests: `python3 scripts/spdp_obstruction/spdp_rank.py results.json`; `python3 scripts/spdp_obstruction/exact_check.py`.


## 9. Branch
`research/dependency-map` in pall-lean, based on main `7f539465ca9a850d525517dc8196dd9cb9b68840` (includes merge 7f53946; re-fetched 31 Oct 2026, unchanged). Commit hash: `81a085b1c9d0cfef44569bb92da85a497d2fd69b` (pushed 31 Oct 2026; no PR opened).

---

# Phase 2 — Gap G1 (repaired P-side Width⇒Rank for COMPILED TABLEAU polynomials)

Prepared 2026-10-31 (Europe/London, GMT), branch `research/gap-g1` (based on `research/dependency-map` 81a085b).
Same tags: [K] kernel-checked (axioms listed), [C] computed, [I] informal proof written here, [X] disproved, [O] open.
**Nothing here proves or claims P ≠ NP or P = NP.**

## G1.0 Current lemma (exact statement attacked)

Paper v5 object (§17.1, Thm 92, Thm 218, §40.4): for a DTM M with T(n) = n^c, variables b_{t,i}, s_{t,q}, h_{t,i}
on a (T+1)×(T+1) tableau with b_{0,i} = x_i, local constraints C (booleanity, one-hot, head/tape transition,
init, accept), each of degree ≤ d₀ = O(1). Three compiled polynomials occur:
* PROD  P_{M,n} = ∏_C (1 − C)               (paper's first definition; Lean `CookLevinDefs.compiledPoly` shape),
* SOS   P̃_{M,n} = 1 − Σ_C C²                (paper: "from now on write P_{M,n} for this", Thm 92/218; degree ≤ 2d₀),
* YV    Y·V, Y = y₁⋯y_κ, V = Σ_C C²         (Lemma 39 κ-padding; Lean `TuringMachine.compiledPoly`).
For the God-Move route the object also carries the verifier wiring (§40.4 clarification, Def. 53, Lemma 222):
P_{M,Φ}(u,z,v) = V_{M,Φ}(u,z) + R_{M,Φ}(v) with V containing Q×_Φ = ∏_C(1 − z_C V_C(u)²) (Lemma 123).

**G1 (Lemma 27/31 repaired, Thm 23/92(2)).** ∃ d(c): ∀ M ∈ DTIME(n^c), Γ^B_{κ,ℓ}(P_{M,n}) ≤ n^{d(c)} at
κ = ⌊α log n⌋, ℓ = ⌊β log n⌋ (we test α = β = 1, log₂), B = compiler partition (Lean: singletons), for the SAME
object that Item 3 maps onto Q×_Φ by a block-local T_Φ = basis ∘ affine ∘ restriction ∘ projection (Thm 223), and
with Item 2: Γ(Q×_Φ) ≥ C(n/3, ⌊log₂ n⌋). Measures: LEAN-drop (shifts with vars ⊆ S, `mlProj` drops), PAPER-reduce
(Def. 12 literally: any shift u of degree ≤ ℓ, x_i² → x_i), PAPER-drop.

## G1.1 Results

**(R1) Degree obstruction for Item 3 [K + I].** `research-audits/gap-g1/G1DegreeObstruction.lean`:
* `GapG1.totalDegree_aeval_le`: any algebra map sending each variable to a polynomial of degree ≤ 1 (restriction to
  constants, affine relabelling, renaming, basis change by linear substitution) does not increase total degree;
  `totalDegree_mlProj_le` (multilinear projection), `totalDegree_piSubst_le`, `totalDegree_piPhi_le` (the repo's
  God-Move restriction) likewise; `DegNonincr.comp` closes under composition.
* `GapG1.coupledSheet_totalDegree`: deg ∏_C (1 − z_C g_C) = Σ_C (1 + deg g_C) for nonzero gadgets (repo
  `coupledSheetFromList`), hence ≥ #clauses (`coupledSheet_totalDegree_ge_length`).
* `GapG1.no_extraction_from_padded_SoS`: for EVERY DTM M and constraints of degree ≤ 3, no degree-non-increasing T maps
  `TuringMachine.compiledPoly` (= Y·ΣC², degree ≤ κ+6) onto a coupled sheet with > κ+6 clauses.
* `GapG1.no_extraction_from_constant_degree_SoS`: same for the paper's constant-degree 1 − ΣC² with > 6 clauses.
* Axioms of all of these: `[propext, Classical.choice, Quot.sound]` (no sorry, no custom axioms).
Informal consequence [I]: on the constant-degree SOS object of Thm 92/218, G1 is TRUE trivially (every κ-th
derivative vanishes once κ > deg, so Γ = 0 at κ = Θ(log n), in every convention) but Thm 223 / Lemma 7 / Lemma 123
(T_Φ(P_{M′}) = Q×_Φ with T_Φ built from basis/affine/restriction/projection) is impossible for ANY machine M′ once
m > deg P (the full Q×_Φ has degree ≥ 3m). The paper's Thm 218 ("degree O(1)") and Lemma 123 ("P_{M′} = Q×_Φ + R(v)",
degree ≥ 3m) are mutually inconsistent. So a compiled object usable for Item 3 must have degree ≥ #clauses = Ω(n).
(Caveat: the "activated" sheet Q×_{Φ,S} with |S| = Θ(log n) has degree Θ(log n); the K-results then apply when
|S|·min(1+deg g_C) > κ+6, which depends on constants not fixed in the paper.)

**(R2) Product horn — explicit easy machine [K].** `GapG1.alwaysAccept_product_rank_ge_NP_bound`:
for the 3-state always-accept DTM and n ≥ 2^804, C(n/3, ⌊log₂ n⌋) ≤ mlBlockedSpdpRank(partition, log n, log n,
compiledPoly(cook_levin_compilation alwaysAccept n)), and `alwaysAccept_product_rank_gt_npow200`: n^200 < that rank.
Axioms `[propext, Classical.choice, Quot.sound]`. (Instantiation of the repo's `compiled_np_lower_bound_any_dtm`;
caveat: `cook_levin_compilation` is a toy with numVars = n, not a full tableau.) **G1 is false for the product
encoding, already for the trivial machine.** Mechanism = the x₁⋯x_n obstruction: ∏_v(1 − v + v²) over the
booleanity factors is a product of univariate factors in distinct variables, present for every M.

**(R3) Literal Def. 12 kills G1 for the padded SoS object, every machine [I + C].**
Claim: let p = Y·V with V = Σ_C C², and suppose some constraint C₀ takes a nonzero value at some Boolean
assignment ρ of its own variables (e.g. the init constraint 1 − s_{0,q₀}). Under Def. 12 with x²→x (PAPER-reduce),
Γ_{κ,ℓ}(p) ≥ Σ_{j≤ℓ} C(N − |vars C₀|, j) ≥ C(N−1, ⌊log₂ n⌋) ≥ C(n, ⌊log₂ n⌋) > C(n/3, ⌊log₂ n⌋).
Proof: row τ = (y₁,…,y_κ) gives ∂^τ p = V; with shifts u = x_A (A ⊆ W := vars ∖ vars(C₀), |A| ≤ ℓ) the rows are
reduce(x_A V). Restricting the Boolean cube to the subcube {vars(C₀) = ρ} is a linear map on multilinear polynomials
(it commutes with x²→x), sending reduce(x_A V) ↦ x_A · V|ρ. On that subcube V|ρ ≥ C₀(ρ)² > 0 pointwise (a sum of
squares of rationals), so multiplication by V|ρ is injective on functions, and the x_A are linearly independent
functions on {0,1}^W. Column-degree guard is respected (deg(x_A V) ≤ ℓ + deg p − κ). ∎ This holds for the
always-accept machine and for every M. [C] check: `scripts/gap_g1/ranks.py yv` (rows τ = padding, shifts over 30
variables) gives full rank 466/466 for ACC and AND at n = 4, 5 (mod 2³¹−1, a lower bound).
The same argument shows the literal Def. 12 is "large" for essentially every polynomial with a nowhere-vanishing
κ-th derivative on a large subcube; the Lean measure avoids this only through the shift restriction vars(u) ⊆ S,
which is paper **Lemma 18's** claim "admissible shifts can be chosen with support contained in S".
**Lemma 18 is false [C, hand-checkable]:** p = x₁ + x₂x₃, N = 3, κ = ℓ = 1: rows 1·{1,x₁,x₂,x₃}, x₃·{1,x₁,x₂},
x₂·{1,x₁,x₃} span {1,x₁,x₂,x₃,x₁x₂,x₁x₃,x₂x₃}: Γ = 7 > C(3,1)·2¹ = 6 (both reduce and drop). Random dense
multilinear p violate it for N = 3…6 (e.g. N=6, ℓ=1: 42 > 12; N=6, ℓ=2: 64 > 60). The Lean rank of the same
p is 5. So Lean's `mlBlockedSpdpRank` is not Def. 12, and the paper's measure needs to be fixed before G1 means anything.

**(R4) Lean measure on the SoS objects: G1 true but structural, machine-independent [C + I].**
`scripts/gap_g1/ranks.py lean` (exact Fraction for n ≤ 5, mod p for n = 6, 8), real tableaux of ACC and AND:

| n | N_tab | κ=ℓ | rank SOS (deg 8) ACC / AND | rank YV ACC / AND | C(n,κ) | C(n/3,κ) |
|---|---|---|---|---|---|---|
| 4 | 65 | 2 | 236 / 236 | 493 / 493 | 6 | 0 |
| 5 | 90 | 2 | 343 / 343 | 699 / 699 | 10 | 0 |
| 6 | 119 | 2 | 470 / 470 | 941 / 941 | 15 | 1 |
| 8 | 189 | 3 | 1585 / 1585 | 5148 / 5148 | 56 | 0 |

Identical for the trivial and the AND machine. Informal bound [I]: for the Lean measure, a nonzero row needs
S∩tableau ⊆ vars(one constraint) (≤ 6 variables, Lean `width_bound`; for SOS also |S| ≤ deg = 8), shifts are
≤ C(2κ, κ) ≤ 4^κ = n² monomials in S, so Γ ≤ #constraints · 2^6 · κ^6 · n² = n^{O(1)} for every M — degree/locality only, no semantics. Hence G1 holds
for SOS/YV under the Lean measure, but (R1) shows such objects cannot carry Item 3, and the bound is the same for
a SAT-solver and for always-accept (no information).

**(R5) Real tableau product encoding, PAPER-reduce, ℓ = 0 [C, small n only].** `ranks.py prod`: rank lower bounds
(rows ∂_S ∏(1−C) for all 2-sets S, evaluated at sampled Boolean points near valid tableaux):
n = 4: ACC ≥ 223, AND ≥ 105 (C(4,2) = 6); rows with S ⊆ inputs only: ACC 6 = C(4,2), AND 4.
(Lower bounds limited by the point sample; ACC vs AND not comparable — AND has one accepting tableau.)
n = 5: ACC ≥ 324, AND ≥ 141 (C(5,2) = 10); S ⊆ inputs: ACC 10 = C(5,2), AND 5.
At these n the NP-side bound C(n/3, log n) is 0 or 1, so small-n data cannot "exceed the NP bound" meaningfully;
the asymptotic statements are (R2) [K] and (R3) [I].

**(R6) "Proves too much" for the verifier-wired object [I].** In the paper the compiled object fed to Item 3 is
P_{M,Φ} = V_{M,Φ}(u,z) + R_{M,Φ}(v) where the verifier/clause-sheet part comes from the fixed templates T_ver and
depends only on Φ (Def. 53, Lemma 222, Thm 223(iii)). Then the same Lemma 123 extraction applies to the always-accept
machine wired the same way, and Γ(P_{M_acc,Φ}) ≥ Γ(Q×_Φ) ≥ C(n/3, log n) by the paper's own monotonicity — G1 fails
for M_acc. (In Lean, `PaperFaithfulCompilation.templatePMn σ Q` does not mention any machine at all.)

**Kill loop (Einstein's `killloop`, code b86b551 + their uncommitted edits; external plugin, Einstein repo not
modified):** plugin `scripts/gap_g1/killloop_spdp_plugin.py` registers `spdp_lean_logn` and
`spdp_def12_reduce_logn` (SPDP of the multilinear extension χ_f, κ=ℓ=⌊log₂ n⌋). Runs (`killloop_run.log`,
`killloop_ledger.jsonl`): invariance under permutation/input negation — SURVIVED for both (finite tests, n ≤ 8/7);
"Γ(χ_f) ≤ s²" and "≤ (s+1)²" — KILLED (first kills are degenerate n=1 instances; the non-degenerate one is
AUDIT_INDSET_matching8: Lean Γ = 174 > (11+1)² = 144 with an 11-gate circuit). These are function-level checks
(relevant to Thm 10/46, already refuted by x₁⋯x_n); compiled tableaux are not Boolean functions, so the kill loop
does not apply to G1 directly.

## G1.2 Verdict

* **Refuted (with counterexample machine = always-accept)** for every compiled-tableau encoding in the paper/Lean that
  can feed Item 3: product encoding [K, R2]; verifier-wired P_{M,Φ} [I, R6]; and the padded SoS Y·V under the
  paper's literal Def. 12 [I + C, R3].
* **True but vacuous** for the constant-degree SOS P_{M,n} (Γ = 0, all conventions) and for SOS/YV under the Lean
  measure (structural n^{O(1)}, machine-independent, R4) — and for exactly these objects Item 3 is impossible by
  degree [K, R1].
* **The Phase-1 encoding dilemma does kill G1-with-Item-3 for both paper encodings**: proved precisely as R1 (SoS horn,
  now a kernel-checked degree obstruction rather than "Γ = 0") and R2 (product horn, explicit trivial machine).
* **Open in the abstract** (Gap G: ∃ encoding S with G1 ∧ G2 ∧ G3). Precise obstacle: by R1 the object must have
  degree ≥ #clauses; by R2/R6 any construction in which the clause sheet (or any product of Ω(n) factors in distinct
  variables) is present syntactically, independent of whether M is correct, violates G1 for always-accept. So S_{M,n}
  must contain high-rank structure **only when M is SAT-correct on all inputs**, i.e. the compiled object must depend on
  a global semantic property of M; no local/syntactic compiler (all those in the paper and in Lean) has this property.
  No candidate is known [O].

## G1.3 Attempts / counterexamples log
* x₁⋯x_n (function level): Phase 1, [C]+analytic.
* p = x₁ + x₂x₃: counterexample to paper Lemma 18 (Def. 12 vs Lean shift restriction) [C, by hand].
* Always-accept machine: counterexample to G1 for the product compiler [K] and for Y·V under Def. 12 [I+C].
* Degree mismatch Thm 218 vs Lemma 123/Thm 223 [K for the Lean objects, I for the paper].

## G1.4 Next actions (recommended next subproblem)
1. **G3-first (correctness dependence):** before any further P-side work, any candidate encoding must pass the
   kernel-checkable sanity test "Γ(T_Φ(S_{M_acc,n})) < C(n/3, log n)" for the always-accept machine with the SAME T_Φ.
   Recommended next subproblem: formalize this as a Lean predicate `PassesG3 S T` and prove it FAILS for every encoding
   whose T_Φ is witness-free and whose sheet is template-generated (generalizing R6 into a theorem), to settle whether
   the God-Move architecture can be repaired at all.
2. Fix the measure: decide between Def. 12 (with R3 it is superpolynomial for almost everything) and the Lean measure
   (vars(u) ⊆ S, which is not Def. 12; Lemma 18 false). Record the choice in the paper.
3. Phase-1 hygiene still pending (remove/demote the refuted PAC/MatrixSPDP axioms, fix ThreeCNF/DecidesSAT).
4. Optional: formalize R3 in Lean (needs a Def.-12 measure with unrestricted shifts and x²→x reduction).

## G1.5 Reproducibility
* Lean: `lake env lean research-audits/gap-g1/G1DegreeObstruction.lean` (imports only already-built modules
  `TuringMachine`, `MultilinearSPDP`, `PiStarConcrete`, `PaperFaithfulCompilation`, `GodMoveReal`; no `lake build` needed).
* Python: `cd scripts/gap_g1; python3 ranks.py lean|yv|prod` (outputs `lean.jsonl`, `yv.jsonl`, `prod.jsonl`);
  tableau semantics are checked by `tableau.sanity` (unique valid tableau per input; accept iff machine accepts).
* Kill loop: `cd /workspace/einstein/repo && PYTHONPATH=<pall-lean>/scripts/gap_g1 python3 -m killloop --max-n 10
  --plugins killloop_spdp_plugin --spec <pall-lean>/scripts/gap_g1/killloop_specs.jsonl --ledger <...>/killloop_ledger.jsonl`.
* Box was heavily loaded (load avg 16–30); computations ran niced, ≤ 3 processes.

## G1.6 Branch
`research/gap-g1` in pall-lean, based on `research/dependency-map` 81a085b. Content commit
`ea1ba8856225…` (pushed 31 Oct 2026, ~21:55 GMT; no PR opened); this hash line added in the following commit.
