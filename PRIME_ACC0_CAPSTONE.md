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

## Cross-model bridge: uniform SAT ↔ `AC⁰[p]` capstone (COMPLETE — unconditional restricted LB)

Goal: connect the repo's uniform `MachineModel`/CNF-SAT world to the non-uniform `AC⁰[p]` prime capstone,
yielding a machine-checked **`SAT ∉ AC⁰[p]`** (an elementary result — *not* `P ≠ NP`). Built from scratch
against the real `CNF` type and the real `BoolCircuitSyntax` substrate. Each brick is a genuine theorem, not
a socket; all `sorry`-free, axioms ⊆ `{propext, Classical.choice, Quot.sound}`.

| Brick | File | What is PROVED |
|---|---|---|
| **1 — reduction** | `…PvsNPParityToSATReduction` | `parityCNF_sat_iff_even : Satisfiable (parityCNF x) ↔ ⊕x = 0` — a genuine two-sided many-one reduction `MOD₂ ≤ SAT` into the repo's real `CNF`. Forward: forced prefix-parity assignment; converse: any satisfying assignment is *forced* to the prefix-parity assignment (`negLit_forces`+`linkClauses_forces`+`chain_forces`), so `¬pₙ` forces `⊕x = 0`. Non-circular: the map decides nothing |
| **2 — composition** | `…PvsNPCircuitComposition` | circuit substitution `subst` on `BoolCircuitSyntax` + `eval_subst` (composition-eval), `isAC0pSyntax_subst`/`isAC0Syntax_subst` (`AC⁰[p]`/`AC⁰` closed under substitution), `depth_subst_le` (additive depth), and `subst_size_le` (`size (subst C f) ≤ size C · M`). Genuine composition-closure of `AC⁰[p]`; `rec_size` size-bounded induction principle for the nested inductive |
| **3 — transfer** | `…PvsNPParitySATBridge` | `decider_size_ge_of_parity_LB`: an `AC⁰[p]` decider for the parity-CNF family through an `AC⁰`, depth-`≤1` encoding, composed via bricks 1+2, is an `AC⁰[p]` circuit computing `PARITY` of depth `≤ Dec.depth+1` — so any parity `AC⁰[p]` size LB (`RealAC0pParitySizeLowerBoundAt`) forces `lower ≤ size(subst Dec enc)`. `enc` is fixed/input-local, so all deciding is in `Dec` — non-circular |
| **4 — concrete SAT decider** | `…PvsNPParitySATDecider` | `no_small_ac0p_parityCNF_decider`: any `AC⁰[p]` circuit `Dec` with `(Dec.eval x = true ↔ Satisfiable (parityCNF (ofFn x)))` has `lower ≤ Dec.size + 1` under a parity `AC⁰[p]` size LB — a statement *literally about `Satisfiable (parityCNF …)`*, via brick 1 (`parityCNF_sat_iff_even`) and `bxor_ofFn : bxor (ofFn x) = parityFunction n x`. Identity encoding, so `not Dec` computes `PARITY` |
| **5 — interface discharge** | `…PvsNPParityInterfaceDischarge` | `realAC0p_parity_LB` proves `RealAC0pParitySizeLowerBoundAt` from the *subcircuit-form* capstone (`subcircuits_card_le_size` : `#subcircuits ≤ size`; `boolParity_eq_decide_odd` : `parityFunction` = Odd-count parity; `Layer4.hmod_of_isAC0p`). ⇒ `no_small_ac0p_parityCNF_decider_unconditional`: **no lower-bound hypothesis left** — for `t ≈ m^{1/(2(d+1))}`, any `AC⁰[p]` decider of the parity-CNF family on `2m+1` bits has *super-polynomial* size |
| **6 — model bridge** | `…PvsNPParityAC0pClass` | `no_SATDecisionInClass_smallAC0pParity`: a genuine `RestrictedCapstoneTransfer` instance in an abstract `MachineModel U`. Class = decision machines whose parity-family decision `x ↦ decisionRun M.code (parityCNF (ofFn x))` is realised by a small `AC⁰[p]` circuit; `no_obstruction` from brick 5, `obstruction_of_decides` from `DecidesSAT` + brick 1. ⇒ **no SAT decider has a small `AC⁰[p]` realisation on the parity-CNF family** |

| **7 — generic encoding** | `…PvsNPGenericCNFCodec`, `…PvsNPGenericCNFComposition` | a **general bounded-CNF bit-decoder** `decodeCNF`/`decodeFlat` (arbitrary incidences over `n+1` vars → arbitrary CNFs, incl. `3SAT`), `decodeCNF_sat_iff_even : Satisfiable (decodeCNF …) ↔ ⊕x=0`, and an `AC⁰` depth-`≤1`, size-`≤2` circuit family `bvFamily` realising the parity bit-pattern. `generic_SAT_decider_size_lower_bound` combines the composite lower bound with `subst_size_le` to prove the load-bearing conclusion on the decoder itself: `lower ≤ 2·Dec.size+1`; `…_depth_le` exposes a fixed depth cap `d`. So "correct on all encoded CNFs" is a genuine general-SAT hypothesis and the decoder-size lower bound is explicit |

**Gaps (i)–(iii) all closed:** (ii) discharged unconditionally (brick 5); (iii) closed by the `MachineModel`
`RestrictedCapstoneTransfer` instance (brick 6); (i) closed by brick 7 — a full generic CNF bit-codec so the
decider hypothesis is correctness on *all* encoded CNFs (a real `SAT ∈ AC⁰[p]` hypothesis), with the parity
family reached through a local `AC⁰` encoding.  (Brick 6 already met (i)'s intent in the `MachineModel`
framing; brick 7 delivers the pure-circuit generic encoding.)

**What this is / is not.** *Is:* a machine-checked, `sorry`-free, custom-axiom-free **unconditional restricted
lower bound** — no SAT decider is realisable by a small (`< super-poly`) `AC⁰[p]` circuit on the parity-CNF
family — built from scratch against the repo's real `CNF` and `BoolCircuitSyntax`, backed by the genuine
Razborov–Smolensky capstone (not a pigeonhole socket). *Is not:* general `SAT ∉ AC⁰[p]` (would need the bound
for every `CNF` family, uniformly in the encoding), and emphatically not `P`-time ⊆ `AC⁰[p]` (false) or
`P ≠ NP`. The restriction to the parity family and to fixed input size is inherent and stated.

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
| Dynamic trace invariant (`…DynamicTraceInvariant…`) | `invariant_of_decides` field | **socket, CIRCULAR (same, one more layer)** — `DynamicTraceLabelInvariantFor` *implies* soundness (`soundOnFoolingFamily` proved from its fields) and the file's own `impossible_below_gap` proves it impossible under poly+gap, so `invariant_of_decides ≡ ¬DecidesSAT`; `invariant_of_decides_impossible` says so outright. Correctly *respects* the no-go (excludes the constant projection) and is correctly-shaped, but it is a faithful RESTATEMENT of "family shortcut-free against the class": `invariant_of_decides` for class `C` ⟺ `SAT ∉ C` = a capstone (restricted) or the theorem (general), not a reduction to them |
| **PROVED calibration: invariant target ⟺ `¬SATDecisionInP`** (`…DynamicTraceInvariantEquivalence…`) | — | **genuine correct equivalence** (not a socket): `dynamicTraceInvariant_iff_no_SATDecisionInP` proves `Nonempty (DynamicTraceInvariantForAllMachines U) ↔ ¬SATDecisionInP U`. The `(⇐)` direction is **vacuous** (trivial `hardFamily`, `np_complete_payload := True`, `invariant_of_decides` via `False.elim`), so the target is trivially inhabited under `¬SAT∈P` — the entire content is proving it **non-vacuously** = the lower bound itself. Machine-checks the ledger's circularity finding; correctly points to restricted-class instantiation |
| **Honest architecture: restricted capstone transfer** (`…RestrictedCapstoneTransfer…`) | `no_obstruction` (real LB) + `obstruction_of_decides` (extraction) fields | **correct non-circular transfer** (not a socket): `real capstone ⟹ ¬SAT-in-C ⟹ invariant`, the INVERSE of the circular `invariant⟹LB`. `no_obstruction` is a genuine LB (suppliable by `mod_q_not_ac0p` etc.), not the pigeonhole. Axiom-free cash-outs. Still EMPTY — abstract over `C`, both fields hypotheses; a non-vacuous instance needs `obstruction_of_decides` = the `MOD_q ≤ SAT` reduction across the abstract-machine↔`AC⁰[p]`-circuit bridge |
| **PROVED no-go: `DecidesSAT` ⇏ boundary soundness** (`…DynamicTraceGeometryNoGo…`) | — | **genuine correct no-go** (not a socket): the constant one-cell projection is a valid poly-boundary/exp-gap projection compatible with any decider yet not sound (collapses a one-bit family's two labels), so `boundary_sound_of_decides` cannot come from `DecidesSAT` alone. Correctly forces the next bridge to carry a concrete lower-bound / trace-geometry invariant — i.e. lands back on the restricted lower bound (capstones) or the shortcut-free family (the theorem) |

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
