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
`research/dependency-map` in pall-lean, based on main `7f539465ca9a850d525517dc8196dd9cb9b68840` (includes merge 7f53946; re-fetched 31 Oct 2026, unchanged). Commit hash: see `git log` on that branch (recorded in the report).
