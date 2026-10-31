# Read-only audit of `codex/godmove-gap-repairs` against `main`

Prepared 31 Oct 2026 (Europe/London, GMT) by Grok Bot for Dr. Darren Edwards.
**Nothing was merged. No PR was opened for any of the repairs proposed below.**
**Nothing here proves or claims P ≠ NP or P = NP.**

| | commit |
|---|---|
| branch audited | `codex/godmove-gap-repairs` @ `219219589f742d6e8cb104d0a3b12f3557efcd6a` (12 Sep 2026) |
| compared with | `main` @ `7f539465ca9a850d525517dc8196dd9cb9b68840` |
| merge base | `688fb6629d17` ("Prove witness-padding obstruction to trace lifting") |

Tags: **[K]** kernel-checked by me in this audit (axioms listed), **[K-b]** kernel-checked according to the branch's own
recorded checker run, which I did *not* re-run, **[R]** read from source, **[I]** informal.

A clean `lake build` does **not** establish that the assumptions are consistent. `main` built cleanly while it
contained two refutable axioms (see PR "Remove contradictory PAC/MatrixSPDP gadget axioms from trusted path"). Each
theorem has to be checked with `#print axioms`, and every non-standard axiom or hypothesis has to be judged on
its own merits.

## 1. What the branch changes

226 commits not in main (16 Aug to 12 Sep 2026); main has 3 commits not on the branch (the PDF, the 26 Oct
decision-invariant audit and the merge). Three-dot diff: 389 files, +111,075 / −25 lines.

| theme | where | files (Lean) | theorems/lemmas | dates |
|---|---|---|---|---|
| A. God-Move / N-Frame fixed-invariant audits | `research-audits/nframe-fixed-invariant/` (standalone modules, importing each other by bare name, checked by `check_godmove_circuit.py`) | 243 (194 `.lean`, 46 `.md`, 3 `.py`) | 2,155 | 9–12 Sep |
| B. ComputationalDepth / switching (AC⁰, 2-/3-CNF, multi-switching, cross-branch rank, XOR/parity) | `PallLean/Paper93/DeepMath/PathB/` (library, **not** in the `PallLean` build target) | 86 (83 new, 3 modified: `…Depth3WitnessSeqProps`, `…RestrictionCardinality`, `…SwitchingTokenCount`, additions only) | 2,236 | 16 Aug – 3 Sep |
| C. Representation-invariant wrappers | `PallLean/SemanticEntanglementBridge.lean`, `PallLean/DynamicGraphEntanglement.lean`, **both added to `PallLean.lean` (default target)** | 2 | 20 | Sep |
| D. 8 Sep dynamic-Lagrangian / curiosity-search audits | `research-audits/2026-09-08/` | 6 `.lean` + reports/JSON | 22 | 8 Sep |
| E. Entanglement follow-up experiments | `research-audits/entanglement-followup/` | Python + JSON + notes only | – | Sep |
| F. Docs/tools | `README.md` (+144 lines of continuation reports), `SCOPE_GODMOVE_OBLIGATION.md`, `SCOPE_OBSERVER_PROGRAMME_CAPSTONE.md`, `MULTISWITCHING_FRONTIER.md`, `QUATERNION_MOMENT_AUDIT.md`, `tools/search_indexed_pair_profiles.cpp`, `scripts/multiswitching_polarity_selector_audit.py`, `.gitignore` | – | – | – |

The branch changes **no** existing definition, compiler or theorem statement in the default build closure. The
42 closure files are byte-identical to main's, and `PallLean.lean` only gains the two imports in theme C. The
contradictory axioms `PAC.gadget_spdp_subspace_factoring` and `MatrixSPDP.gadget_factoring_linearmap_form` are
therefore **still present on the branch**, which is just as inconsistent as main was. The axiom-removal PR has to
land first, or be rebased under any port.

## 2. Trust-token scan (comment- and string-aware) of every added/modified `.lean` file (289 files)

| token | live occurrences |
|---|---|
| `axiom` | **0** |
| `sorry` / `admit` | **0** / **0** |
| `native_decide` | **0** |
| `opaque`, `implemented_by`, `@[extern]`, `unsafe`, `debug.skipKernelTC`, `ofReduceBool` | **0** |

(Raw grep finds only doc-comment mentions such as "no `sorry`, no `native_decide`".) So the branch introduces no
new trust assumptions. It inherits main's.

## 3. `#print axioms` on the branch's final theorems

See §3.1 (my run) and §3.2 (what the branch's checker records).

### 3.1 My run [K]: `lake env lean` on the branch tree (default-target closure built)
Run on 31 Oct 2026 in a worktree at `21921958` (default-target closure built; `lake env lean`):

| declaration | axioms |
|---|---|
| `SemanticEntanglementBridge.separation_of_semantic_entanglement` | propext, Classical.choice, Quot.sound |
| `DynamicGraphEntanglement.separation_of_sourced_graph_barrier` | propext, Classical.choice, Quot.sound |
| `DynamicGraphEntanglement.separation_of_dynamicExtraction` | propext, Classical.choice, Quot.sound |
| `Step4Compiler.P_ne_NP_Lean` (unchanged from main; its hypothesis `hsep` is refuted, Phase 1) | propext, Quot.sound |
| `PAC.gadget_multiplication_rank_bound` | propext, Classical.choice, **`PAC.gadget_spdp_subspace_factoring`** (refutable), Quot.sound |
| `MatrixSPDP.gadget_multiplication_rank_bound_matrix_form` | propext, Classical.choice, **`MatrixSPDP.gadget_factoring_linearmap_form`** (refutable), Quot.sound |
| `GodMoveExistingCompilerVerdict.existing_product_template_collapse_false` (standalone audit file, compiled by me) | propext, Classical.choice, Quot.sound |
| `GodMoveAccumulatorRankCheck.elimination_strictly_increases_rank`, `…elimination_not_rank_monotone`, `…product_rank_pos`, `…output_rank_zero` (compiled by me) | propext, Classical.choice, Quot.sound |

So the branch's own final theorems carry no custom axiom, but the branch environment still contains the two
refutable axioms. Everything kernel-checked on the branch is therefore checked in an inconsistent environment.
That costs nothing for a theorem whose `#print axioms` list omits them, but it is one more reason to land the
axiom-removal PR before any port.

### 3.2 Branch-recorded [K-b]
The branch's `GodMoveSATRuntimeBoundAudit.md` records that `check_godmove_circuit.py` passed on 10 Sep 2026 with
**83 modules, 649 printed axiom checks, zero warnings, every dependency ⊆ {propext, Classical.choice, Quot.sound}**.
Later continuation notes report the same for modules added on 11–12 Sep. I did **not** re-run the checker. Its
closure needs about 360 library modules outside the default target, and the box was saturated (load average
40–70, another worker building the same PathB closure). Re-run it on an idle machine:
`python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py --module GodMoveSATRuntimeFrontier --module GodMoveSATDesignatedProjection --module GodMoveLinearTimeRankObstruction --module GodMoveSATLocalClockObstruction`.

### 3.3 Hypotheses that are contradictory or equivalent to the missing result [R + K-b]
No axiom on the branch is new. Its "final theorems" are all **conditional**, and each premise is either the whole
missing result or something provably equivalent to it:

* `SemanticEntanglementBridge.separation_of_semantic_entanglement` and
  `DynamicGraphEntanglement.separation_of_sourced_graph_barrier` / `separation_of_dynamicExtraction`
  (default target): here `InP`, `InNP` are **arbitrary predicates**, `SAT` an arbitrary family. The proof is
  two lines of logic, and the premise `hSAT : HasSuperpolynomialSemanticEntanglement M SAT` (or
  `hSATBarrier`/`E`) together with `p_has_poly_realizations` *is* the separation. The file says so honestly.
  These are wrappers, not progress.
* `GodMoveSATRuntimeFrontier.separation_of_SATPolynomialClockRankBound (hbound : SATPolynomialClockRankBound) : SAT_not_in_P`
  together with **`satPolynomialClockRankBound_iff_separation : SATPolynomialClockRankBound ↔ SAT_not_in_P`** [K-b].
  The premise is *provably equivalent* to the target, so it is the missing result restated. (The reverse direction
  is vacuous, as the branch notes.)
* `GodMoveExistingCompilerVerdict`: proves **¬ `WithinProfileBound.CookLevinProfileTemplateCollapseLemma`** for
  the raw product compiler (`n ≥ 2^804`, `timeBound ≤ 4`, `numStates ≤ n`). Main's named P-side target for the
  existing compiler is therefore **contradictory**. Any main theorem that takes it as a hypothesis is vacuous.
  This is a refutation of a hypothesis, not a new axiom.

## 4. The latest repaired construction (exact definitions)

**Where:** `codex/godmove-gap-repairs`, `research-audits/nframe-fixed-invariant/`. Core commits: `3bda8850`
(10 Sep 2026, 19:05 BST: exact sheet extraction, source canonicity), **`d105443a` (10 Sep 2026, 19:22 BST:
source rank at the exact paper window, the P-side frontier)**, `07195f6e` (linear-time obstruction) and
`fccad5a2` (12 Sep, 01:25 BST: local-clock obstruction). The later commits up to `21921958` (11–12 Sep) only
add runtime and arithmetic accounting for building the wire projection. They do not change the source, the
measure or the bound.
Other branches checked: `mikoshi-geometric-intuition` `research/partition-robust-rank` @ `3563c26` (27 Oct 2026)
contains only informal notes (God-Move 26 boundary response: Kron reduction and graph-Laplacian energy, "not
Lean-certified"). It has no compiled polynomial and no SPDP construction newer than this one. `pall-lean`
`paper-faithful` @ `4c5c2d0` is older (17 Mar 2026). **So the construction below is the latest one.**

* **Compiled ("source") polynomial.** `GodMoveMachineFaceExtraction.machineSource M T φ n :=
  circuitTarget (circuitFor M L (T L))` with `L = (inputTemplate φ n).length`. This is the **Boolean-normalized
  (multilinear-interpolated) output of the machine `M` unrolled for `T L` steps on all `L`-bit inputs**. The
  instance used is `φ = unitFormula (n/3)` (positive unit CNF), `L = paperInputLength n = unitInputLength (n/3)`
  (with `n/3 ≤ L` and `2L ≤ n³` for `n ≥ 2^20`). Augmented form: `GodMoveSATDesignatedProjection.augmentedSource
  M T n` (the same polynomial embedded with `n/3` extra output coordinates).
* **Canonicity [K-b].** `GodMoveSATSourceCanonicity.machineSource_eq_SATCharacteristic`: if `Decides M SATLang T`,
  then `machineSource M T φ n = languageCharacteristic SATLang L`, the multilinear extension of SAT on length `L`.
  `machineSource_independent_of_SAT_decider`: every correct SAT decider gives *the same* polynomial. So the source
  is a **function-level object**, the multilinear extension of SAT|_L.
* **Measure.** The repository's strict multilinear blocked SPDP rank `MultilinearSPDP.mlBlockedSpdpRank B k ℓ p`
  (strict `|S| = k`; shifts `u` with vars(u) ⊆ S and deg ≤ ℓ; `mlProj` drops non-multilinear monomials). It uses
  `B = discreteBlocks L` (singleton blocks) and **`k = ℓ = Nat.log 2 n`** (`⌊log₂ n⌋` of the *formula* size `n`,
  not of `L`). This is **not** paper Def. 12, which allows any shift `u` and reduces x²→x (see §5, item 4).
  `paperSourceRank M T n := mlBlockedSpdpRank (discreteBlocks (paperInputLength n)) (log₂ n) (log₂ n) (machineSource M T (unitFormula (n/3)) (n/3))`.
* **Restriction / projection (extraction).** `pinnedGauge φ n = piSubst (pinnedKeep φ n) (bit ∘ pinnedFixed φ n)`:
  it fixes the formula/header bits and keeps the assignment bits. It is a witness-free, idempotent constant
  restriction, and it is rank-monotone (`pinnedGauge_extracts_compactTarget`). `designatedProjection n =
  projection (sheetExtraction n)` is an idempotent linear map with no machine/clock/witness parameter. It uses the
  degree-raising substitution X_i ↦ 1 − X_i + X_i² into the extracted unit monomial, and
  `designatedProjection_correct` sends `augmentedSource M T n` (for correct SAT deciders `M`) to the embedded
  production sheet `(cookLevinStrictFOBTarget D n …).coupledPoly`. That sheet holds for **any** DTM `D` with
  `timeBound ≤ 4`, `numStates ≤ n`.
* **NP side [K-b].** `GodMoveSATPaperWindowLower.paper_window_rank_ge_power`: `Decides M SATLang T → 2^20 ≤ n →
  n^(⌊log₂ n⌋/4) ≤ paperSourceRank-type rank` (via the unit face: `C(n/3, log₂ n)` from
  `BinomialBound.binomial_lower_bound_concrete`). `designatedProjection_rank_gt_npow200`: `n^200 <` rank of the
  extracted sheet for `n ≥ 2^804`.
* **P side: what is claimed and proved.**
  - Proved, for **every** machine and clock, with no correctness assumption:
    `paperSourceRank_le_quasipolynomial : paperSourceRank M T n ≤ n^(3·⌊log₂ n⌋)` (from
    `GodMoveShiftedRankUpper.strict_rank_le_two_mul_vars_pow`, rank ≤ (2L)^k). This bound is quasi-polynomial.
  - **Not proved; stated as a `Prop`:** `SATPolynomialClockRankBound := ∀ M T, PolyBounded T → Decides M SATLang T →
    ∃ C d n0, ∀ n ≥ n0, paperSourceRank M T n ≤ C·(L_n + T(L_n) + 1)^d`. It is
    `↔ SAT_not_in_P` (`satPolynomialClockRankBound_iff_separation`). So the needed P-side bound is
    **exactly the missing result**. The rank contributes nothing beyond restating it.

## 5. Do the `research/gap-g1` (f32d764) results apply to the repaired construction?

"Previously known" = already on the godmove branch, on main, or in Phase 1, before `research/gap-g1`.

| # | gap-g1 result | applies to the repaired construction? | exact statement / counterexample on the repaired definitions | known vs new |
|---|---|---|---|---|
| 1 | **Degree obstruction** (`GapG1.no_extraction_from_padded_SoS`, `no_extraction_from_constant_degree_SoS`: no degree-non-increasing map sends `TuringMachine.compiledPoly` = Y·ΣC², or 1 − ΣC², onto a coupled sheet with > κ+6 / > 6 clauses) [K in gap-g1] | **Doesn't apply.** | The repaired source is `machineSource`, a multilinear polynomial of degree up to `L`, not the constant-degree SoS or padded object. The extraction `designatedProjection` uses X ↦ 1 − X + X², which is **degree-raising**, so it is outside `GapG1.DegNonincr`. The obstruction only explains why the repaired route had to abandon the SoS objects. | gap-g1 result is **new**, but irrelevant here |
| 2 | **Always-accept product rank ≥ NP bound** (`GapG1.alwaysAccept_product_rank_ge_NP_bound`: C(n/3, log n) ≤ rank of `compiledPoly (cook_levin_compilation alwaysAccept n)`) [K] | **Doesn't apply to the source; the analogue holds and is already proved.** | For always-accept `M` the normalized output is the constant 1, so all strict k-th derivatives (k ≥ 1) vanish and `paperSourceRank = 0`. The same phenomenon reappears with another easy machine: `GodMoveLinearTimeRankObstruction.no_general_polynomial_machine_rank_bound : ¬ ∀ M language T, Decides M language T → PolyBounded T → ∃ C d L0, ∀ L ≥ L0, mlBlockedSpdpRank (discreteBlocks L) (log₂ L) (ell L) (circuitTarget (circuitFor M L (T L))) ≤ C·(L+T L+1)^d`. Witness: a small linear-time scanner (states `Bool ⊕ Bool`) (`easyLanguage`, clock L+1) whose source has a nonzero top coefficient on x₁⋯x_L (`choose_le_scannerSource_rank`). The *target* sheet `cookLevinStrictFOBTarget D` has rank > n^200 for every `D`, including always-accept D (`designated_sheet_rank_gt_npow200`; main `compiled_np_lower_bound_any_dtm`). | **Previously known**: main (`CookLevinFrontierRefutation`), branch 8 Sep (`EasyMachineProfileRefutation`), branch 10 Sep (scanner), Phase 1 (x₁⋯x_n). gap-g1's R2 is an explicit restatement, not new in substance. |
| 3 | **Literal Def. 12 rank superpolynomial for every machine** (R3: for Y·ΣC² with a constraint that is nonzero somewhere, Γ ≥ C(N−1, log n)) [I + C] | **Doesn't apply as stated.** | The R3 argument needs the padding Y and a sum of squares V that vanishes nowhere on a subcube. `machineSource` has neither. Under the strict convention (|τ| = κ ≥ 1) the always-accept source 1 has Def. 12 rank 0, so "every machine" fails. Variant [I, hand-check, **new**]: under the *inclusive* convention (|τ| ≤ κ, used in the paper's Lemma 40(c)) with Def. 12's unrestricted shifts, τ = ∅ rows give reduce(x_A·1), |A| ≤ ℓ. These are independent, so a constant-1 source has rank Σ_{j≤ℓ} C(L, j) ≥ C(n/3, log₂ n). That already reaches the NP bound for a trivial machine. Whether this holds for *every* nonzero source is **unknown**: x_A·f can collapse under x²→x. | R3 is new (gap-g1). Inclusive-convention variant is **new** (this audit, informal). |
| 4 | **Lemma 18 counterexample** p = x₁ + x₂x₃, N = 3, κ = ℓ = 1: Def. 12 rank 7 > C(3,1)·2 = 6; Lean rank 5 [C, by hand] | **Applies to the paper alignment, not to the branch's internal theorems.** | The repaired construction uses the Lean measure (shifts with vars(u) ⊆ S). The branch says so explicitly: `GodMoveShiftedRankUpper` is "not a claim about definitions allowing shifts on arbitrary ambient variables". So its upper bound `n^(3 log n)` and its lower bounds are about `mlBlockedSpdpRank`, not Def. 12. Paper Lemma 18 is what would identify the two, and the counterexample shows it is false. So none of the repaired construction's numbers can be quoted as Def. 12 statements via Lemma 18. | Measure mismatch: **previously known** (`paper-faithful` `ARCHITECTURE_MISMATCH.md`; branch doc). Explicit Lemma 18 counterexample: **new** (gap-g1). |
| 5 | **Template-only sheet extracting Q×_Φ for always-accept** (R6: if the clause sheet is template-generated and independent of M, the extraction applies to the always-accept machine too, giving Γ(P_{M_acc,Φ}) ≥ C(n/3, log n)) [I] | **Doesn't apply to the repaired source; it applies to the target sheet.** | The repaired source is semantic: `designatedProjection_correct` and `paper_window_rank_ge_power` both *require* `Decides M SATLang T`. For always-accept `M` the source is 1, and its projection is not the sheet. So the "proves too much" argument does not go through. The target `cookLevinStrictFOBTarget D n …` *is* template-only (`D` arbitrary, including always-accept), which confirms R6's diagnosis of where the hardness sits. The price of avoiding R6 is §4's canonicity: the source equals the SAT multilinear extension for *every* correct decider. The rank is then a function-level invariant of SAT, and the P-side bound is equivalent to `SAT_not_in_P` (§3.3). Function-level SPDP rank is refuted as a complexity measure by item 2 (scanner, x₁⋯x_n). | R6 is new (gap-g1, informal). The repaired construction's escape from R6 and the resulting circularity are **previously known** (branch 10 Sep: `machineSource_independent_of_SAT_decider`, `satPolynomialClockRankBound_iff_separation`, `GodMoveSATLocalClockObstruction`). |

**Net verdict [K-b + R].** The latest repaired construction escapes every syntactic obstruction in gap-g1
(1, 3, 5) by making the source semantic: the normalized output of a correct SAT decider. That moves all the
difficulty into a P-side estimate that is *provably equivalent* to `SAT_not_in_P`. The only general route to such
an estimate is a runtime-to-rank bound for all machines, and the branch's own scanner theorem (item 2) refutes
that. The earliest gap is therefore unchanged: **no P-side bound that uses correctness of a SAT decider in an
essential, non-circular way is known.** gap-g1's suggested next step (a `PassesG3` sanity predicate for
always-accept) is passed trivially by the repaired construction (rank 0). It needs strengthening, e.g. to "passes
for every *easy* machine", which the scanner fails.

## 6. Proposed small, reviewable PRs (NOT opened)

All proposals assume the axiom-removal PR lands first. Each item is standalone; none changes the default build
target except where stated.

1. **Refutation of main's named P-side target**: port `GodMoveExistingCompilerVerdict.lean`
   (imports only `PallLean.ProfileCompression`, `PallLean.GodMoveReal`, both on main), proving
   `¬ CookLevinProfileTemplateCollapseLemma` for the raw product compiler. Add a `-- GAP:`/refuted marker to that
   definition's docstring on main. *Value: marks a contradictory hypothesis on main.* Status: [K-b]. Re-check
   with `lake env lean` before opening.
2. **Generic-monotonicity counterexample**: port `GodMoveAccumulatorRankCheck.lean` (imports only
   `PallLean.MultilinearSPDP`). Eliminating X₀ ↦ (1−X₁)(1−X₂) strictly increases `mlBlockedSpdpRank`
   (κ = 2, ℓ = 0). *Value: rules out a tempting general lemma.* [K-b]
3. **Measure sanity pack** (research-audits only, with the checker script): `GodMoveSATSourceCanonicity`,
   `GodMoveShiftedRankUpper` (universal (2L)^k cap), `GodMoveLinearTimeRankObstruction` (easy scanner has
   superpolynomial rank), plus their GodMove import closure (`GodMoveMonomialMinor`, `GodMoveCircuitConnection`,
   `GodMoveUnitCharacteristic`, `GodMoveBooleanFace`, `GodMoveTopCoefficientMinor`, …). All library deps are
   already on main. *Value: kernel-checked versions of the Phase-1 x₁⋯x_n obstruction and the function-level
   circularity.* [K-b]
4. **Frontier statement**: `GodMoveSATPaperWindowLower` + `GodMoveSATRuntimeFrontier` (the `↔ SAT_not_in_P`
   equivalence) as the honest "what remains" record for the God-Move route. [K-b]
5. **(Optional, low value) theme C wrappers** `SemanticEntanglementBridge`/`DynamicGraphEntanglement` into the
   default target. They are correct but purely logical. If ported, the docstrings should state that the
   premises are the separation.
6. **Not proposed:** theme B (PathB switching/AC⁰ lemmas, 2,236 theorems). This is solid-looking restricted-model
   work but not on the P vs NP critical path. It is large and outside the build target, so it should come as
   its own review after the checker is re-run. Theme A runtime/arithmetic accounting (11–12 Sep) is likewise not
   on the critical path.

## 7. Reproduce
```
git fetch origin && git worktree add ../gm origin/codex/godmove-gap-repairs
cd ../gm && lake exe cache get && lake build PallLean
lake env lean <file with the #print axioms lines of §3.1>
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py --module GodMoveSATRuntimeFrontier   # full focused check
```
