# Consolidated status of the P vs NP proof audit (pall-lean / arXiv v5 + God-Move branch)

As of 01 Nov 2026 07:05 GMT. Written from research/gap-g4; every item cites the commit where it lives.
**Nothing here proves or claims P ≠ NP or P = NP.** This file records what is established about the paper's proof
architecture and its Lean formalisation.

Labels:
* **[K]** kernel-checked; `#print axioms` gives ⊆ {propext, Classical.choice, Quot.sound} unless stated otherwise.
* **[C]** computed (exact rational unless marked mod-p).
* **[I]** informal argument written in the notes.
* **[O]** open.
* **new**: found in this project. **known**: already in the paper or repo, or folklore.

Sources:
* Paper: arXiv v5 (`P vs NP Paper.pdf`, sha256 c39b7045…26240, 8 Jan 2026), the primary source. The newer manuscripts
  `pall (50).pdf` and `n_np (1).pdf` are leads only and have not been verified.
* Repo: DarrenEdwards111/pall-lean, `main` @ 7f53946.
* Darren's repaired branch: `codex/godmove-gap-repairs` @ 21921958, core commits 3bda8850 / d105443a.

## Phase 1: definitions, axioms, dependency map (branch research/dependency-map 81a085b)
| item | exact statement | label | new/known |
|---|---|---|---|
| P1.1 | `Phase1Audit.gadget_spdp_subspace_factoring_false : False` and `Phase1Audit.gadget_factoring_linearmap_form_false : False` (research-audits/dependency-map/AxiomInconsistency.lean). Axioms used: the custom `PAC.gadget_spdp_subspace_factoring` and `MatrixSPDP.gadget_factoring_linearmap_form`, respectively. **The environment of PallLean.lean at main 7f53946 is inconsistent.** | [K] | new as a derivation of False. The repo already had the counterexample (Archive/GadgetSubspaceFactoringCounterexample.lean) |
| P1.2 | `Phase1Audit.trivialPeqNP : PeqNP_Paper` and `hsep_refuted : ¬(PeqNP_Paper → False)`: the hypothesis `hsep` of `P_ne_NP_Lean` is false, because the Lean SAT/NP notions are trivial | [K] (axioms [propext, Quot.sound]) | new |
| P1.3 | the SPDP measure on function polynomials is refuted by x₁⋯x_n (the multilinear-extension rank of AND is large) | [C]+analytic | known in content (shifted-partials folklore); recorded here |
| P1.4 | the earliest substantive gap on the critical path is paper Lemmas 27/31 (Width ⇒ Rank, "Gap G1") | [I] | new (dependency map) |
| PR #2 | branch `fix/remove-contradictory-axioms` @ fb867692 turns both refuted axioms into `Prop`s `PAC.GadgetSpdpSubspaceFactoring` and `MatrixSPDP.GadgetFactoringLinearMapForm`, used as explicit `-- GAP:` hypotheses. No headline theorem depended on them. PR open, not merged. `…_paperFaithful` (inclusive κ) remains, with 0 dependents; its status is [O] | [K] builds | new (our PR) |

## Phase 2: Gap G1 (repaired Width ⇒ Rank on compiled tableau polynomials; research/gap-g1 f32d764)
| item | exact statement | label | new/known |
|---|---|---|---|
| R1 | `GapG1.no_extraction_from_padded_SoS` and `GapG1.no_extraction_from_constant_degree_SoS`: for every DTM, no degree-non-increasing T maps the SoS/padded compiled polynomial onto a coupled sheet with more clauses than its degree allows. The paper's Thm 218 ("degree O(1)") and Lemma 123 (degree ≥ 3m) are mutually inconsistent | [K] | new |
| R2 | `GapG1.alwaysAccept_product_rank_ge_NP_bound` and `…_gt_npow200`: for the 3-state always-accept DTM and n ≥ 2^804, C(n/3,⌊log₂n⌋) ≤ mlBlockedSpdpRank(compiledPoly) and n^200 < rank. **G1 is false for the product encoding.** Caveat: `cook_levin_compilation` is a toy | [K] | new |
| R3 | under literal Def. 12, Γ(Y·V) ≥ C(n,⌊log₂n⌋) for every machine (padded SoS) | [I]+[C] | new |
| R4 | under the Lean measure, the SoS/YV ranks are structural n^{O(1)} and identical for ACC and AND (G1 is true but vacuous) | [C]+[I] | new |
| R6 | for the verifier-wired P_{M,Φ}, the same extraction applies to always-accept, so G1 fails | [I] | new |
| L18 | **paper Lemma 18 is false**: p = x₁+x₂x₃, N = 3, κ = ℓ = 1 gives Γ = 7 > C(3,1)·2 = 6 (both conventions). Kernel-checked as `Lemma18Counterexample.lemma18_fails` (research/gap-g3 d560b69f); the gap-g1 version was [C] | [K] | new |

## Phase 3: Gap G3 (does extraction tell a correct machine from a trivial one?; research/gap-g3 d560b69f, head 45ab9a05)
| item | exact statement | label | new/known |
|---|---|---|---|
| G3-A | `GapG3.g3_fails_of_mblind_extraction`, `g3_fails_additive`, `g3_fails_multiplicative`, `routeB_witnessFree_not_PSide`, `g3_fails_of_answer_view`, with non-vacuity `concrete_*` and `routeB_hypotheses_satisfiable`. For every witness-free, template-generated extraction (Lemma 222/123 additive, `templatePMn` multiplicative, Route-B Thm 207, answer-only), always-accept inherits the solver's extracted rank. **The v5/main reconstruction is refuted** | [K] | new (formal); the principle "machine-blind invariants cannot separate" is known (branch `invHard_diag`) |
| G3-B | B1 `acceptAll_passesG3`: in the repaired construction, accept-all has source 1 and rank 0. B2 `extraction_depends_only_on_face`. B3 `*_of_faceCorrect`: the whole lower-bound chain needs only correctness on the 2^m unit-CNF face queries (an easy family [I]) | [K] (trimmed faithful import path, G3.7) | new (formal); B3 is known in prose in the branch |
| B4 | the branch's own `satPolynomialClockRankBound_iff_separation`: the P-side bound is **equivalent** to SAT ∉ P (circular) | [K] in the branch | known (Darren's branch) |
| G3-C | C1 `rank_le_two_pow_mul_scanner` and C2 `rank_le_two_pow_mul_and`: every p has Lean rank ≤ 2^k · rank(scanner) (resp. AND). C3 `sat_source_le_n_mul_scanner`: rank(SAT source) ≤ n · rank(scanner). C4 `no_superpoly_gap_over_scanner` | [K] | new combinations of known parts |
| Def12≠Lean | Def. 12 differs from `mlBlockedSpdpSubspace` in 5 ways: shift support, drop vs reduce, repeated τ, strict vs inclusive κ, columns. The paper itself is inconsistent on strict vs inclusive (Lemma 40(c)) | [I] (G3.4) | new (precise list) |

## Phase 4: G4 (Def. 12 measure, easy-function ceiling; research/gap-g4, see NOTES_G4.md)
All of the following are [K] in `research-audits/gap-g4/Def12Measure.lean` (Mathlib only). The Lean measure is restated
there verbatim, so its fidelity is textual (caveat).
| item | Lean name: exact statement | new/known |
|---|---|---|
| D0 | `def12Rank c B κ ℓ p` is the faithful Def. 12 (both conventions, degree guard, literal block condition). Faithfulness lemmas: `blockCondition_vacuous`, `row_colRestrict_eq` (columns harmless), `def12Span_finiteDimensional`, `pderiv_comm`, `iterDerivList_perm` | new formalisation |
| D1 | `lean_le_def12_drop`: `mlBlockedSpdpRank B κ ℓ p ≤ def12Rank .drop B κ ℓ p` for all p | new (was [I]) |
| D2 | `and_def12_lower`: `Σ_{j≤κ} C(N,j) ≤ def12Rank c B κ κ (x₁⋯x_κ)` | new (was [C]) |
| D3 | `subset_def12_lower`: `C(m,κ)·Σ_{j≤ℓ}C(m,j) ≤ def12Rank c B κ ℓ (subsetPoly m κ)`, where subsetPoly = χ_f for the linear-time f(x,y) = [\|y\| = κ ∧ y ≤ x] on 2m bits | **new** |
| D4 | `lemma18_fails_subset_family`: for m ≥ 4, `C(2m,1)·2 < def12Rank c B 1 1 (subsetPoly m 1)`. **Lemma 18 fails for an infinite Boolean family** | **new** (strengthens L18) |
| D7 | `def12Rank_le_rowCeiling`: `IsMultilinear p → def12Rank ≤ C(N,κ)·Σ_{j≤ℓ}C(N,j)` | new as Lean; standard content |
| D9/D11 | `multilinear_le_four_pow_mul_subset` (N = 2m) and `…_odd` (N = 2m+1, covering the branch's always-odd `unitSourceLength`): for every multilinear p, `Γ(p) ≤ 4^{κ+ℓ}·Γ(easy)` (even N) and `Γ(p) ≤ 4^{κ+ℓ+1}·Γ(easy)` (odd N), when 3κ, 3ℓ ≤ 2m. **Under Def. 12, SAT's MLE is within poly(n) of a linear-time function**, which extends C1–C4 from the Lean measure to the paper's measure | **new** |
| D10 | `def12Rank_le_rename`: adding a variable never decreases Def. 12 rank (G3-A transfer property (c)) | new (was [I]) |
| G4-C | computed [C]: at the branch's smallest real length L = 15 (κ = ℓ = 1), SAT_15 has Def. 12 rank 202/190 (drop/reduce), against ceiling 240, easy SUBSET 196/168 and SCANNER 133/133; the Lean ranks are ≤ 30 | new data (guidance only) |

## Overall verdict
1. **The Lean development at main 7f53946 proves nothing about P vs NP.**
   * Its environment is inconsistent (P1.1; fixed only on PR #2's branch).
   * Its separation hypothesis is false (P1.2).
2. **The paper's v5 architecture (reconstructed) is blocked on every known route.**
   * Gap G1 is refuted for the encodings that can feed extraction (R1, R2, R6).
   * Extraction is machine-blind (G3-A).
   * Lemma 18 is false (L18, D4).
3. **Darren's repaired construction (21921958):**
   * Its extraction and NP-side lower bound are sound (G3-B, [K] in the branch).
   * The remaining P-side bound is equivalent to the separation itself (B4, known).
   * In the Lean measure every function is within a factor n of a linear-time function (C1–C4).
   * In the paper's own Def. 12, every multilinear function, SAT's MLE included, is within poly(n) of a linear-time
     function (D9/D11).
   * So **neither measure can separate SAT from P-computable functions by more than a polynomial factor at
     κ = ℓ = Θ(log n)**. The measure carries no SAT-specific lower bound that an easy function does not also have.
     This is a property of the measure, independent of any proof strategy.
4. **[O] what would be needed:**
   * a different invariant, one that is not maximised, up to poly factors, by linear-time functions; or
   * a restricted-model lower bound (for example homogeneous depth-4 or multilinear formulas, where shifted partials
     are known to work), which would not give P ≠ NP.
   No justified next cycle remains within the SPDP/God-Move architecture.

## Unverified or soft points (honest list)
* Fidelity of local verbatim copies (D1, D7's `IsMultilinear`) is textual, not a kernel link.
* "easy" (linear time) for f is [I]; it is not a `ComposableMachine`.
* SAT_L multilinear is [I] here (true by construction in the branch).
* The G3-B build used a trimmed import path for one module (G3.7). The faithfulness argument is recorded there.
* The axiom census of the whole main closure did not finish (Phase 1 §1.2).

## Update 01 Nov 2026 21:xx GMT (in-model Def. 12 comparator)
Kernel-checked (`ContLink.lean`): at the paper parameters, Γ^{Def12}(SAT_L) ≤ n^6·Γ^{Def12}(χ_contLang at L), where
`contLang` is `InP` in the branch's own `ComposableMachine` model (`satChar_def12_le_cont_paper`). The same bound holds for
every language (`lang_def12_le_cont`). SATLang is false-padding invariant (`SATPad.SATLang_append_false`). The
architecture remains blocked.
