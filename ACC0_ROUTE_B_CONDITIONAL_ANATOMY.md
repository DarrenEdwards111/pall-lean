# Route B — a machine-checked conditional anatomy of `NEXP ⊄ ACC⁰`

**Status.** This is **not** a proof of `NEXP ⊄ ACC⁰`, and nothing in it is `P ≠ NP`.  It is a complete,
machine-checked **conditional anatomy** of the Williams / Razborov–Smolensky / Beigel–Tarui route: every *gluing*,
*architecture*, and *accounting* step is proved (clean axioms, no `sorry`), and the separation is faithfully
**reduced** to a small set of named classical theorems that remain as sockets.

All theorems live under `PallLean.Paper93.DeepMath.PathB`; the master re-export is
`ComputationalDepthACC0FrontierSummary.lean`.

---

## 0. How we got here — N-Frame / tri-aspect did its job

The N-Frame programme was used as a **selector**, not the engine:

- The *incidence / rank* observer was honestly **refuted**: `NFrameRankShrink` is false for the membership-rank
  observer — adversarial singleton supports have injective patterns, so `RankCellCollapse` never fires
  (`…ACC0RankShrinkWall`).
- Tri-aspect monism was turned into a theorem map (`…ACC0TriAspectBoundary`): one boundary object, three projections
  (incidence / algebraic / cost).  The **incidence projection is refuted**; the **algebraic (effective-dimension)
  projection is viable** for `AC⁰[p]` (parity escapes the low-degree span — RS core).
- Conclusion: the working route is **Route B** (the polynomial method), not the observer route.

---

## 1. The composite-`MOD` object and the product-residue observer

- `MOD₆ = MOD₂ ∧ MOD₃` (`…ACC0CompositeBTTarget.mod6_iff_mod2_and_mod3`).
- **Single-field RS provably fails for composite modulus**: no injective ring hom `ZMod 6 → ZMod p` (the zero-divisor
  `2·3 = 0` cannot survive in a field) — `field_polynomial_projection_fails_for_MOD6`.
- The replacement is the **integer / product observer** `ZMod 6 ≃+* ZMod 2 × ZMod 3` (`compositeResidueObserver`),
  faithful where no single field is.
- Depth-2 `MOD₆∘AND` has an exact `SYM∘AND` representation read by the residue pair (`…ACC0Mod6SymAndDepth2`).

## 2. Composition: what composes, and the wall that is not a wall

- `…ACC0SymAndComposition`: `NOT`, shared-layer `AND`/`OR`, and cross-modulus CRT all compose; cross-layer `AND`/`OR`
  lands in a **joint two-count** representation.
- `…ACC0MiniBTTwoCount`: the two-count collapse is **provable exactly** by a mixed-radix encoding
  (`miniBTCollapse_holds`).  Correcting an earlier guess: the wall is **not** impossibility but the **multiplicative
  size blow-up** (`…ACC0BTSizeRecurrence.iterSize_ge`: `b·(b+1)^k`, exponential in fan-in).

## 3. The probabilistic-polynomial layer (the RS analytic core, PROVED)

- **`MOD` gates are exactly low-degree** — `mod2_indicator` (`1+a`, deg 1), `mod3_indicator` (`1−a²`, deg 2).  No
  probabilism needed for `MOD`.
- The genuine probabilistic ingredient is the **`OR` polynomial**:
  - `linear_form_balance` — a random `F_p`-linear form vanishes on a fixed nonzero vector with probability **exactly
    `1/p`** (additive equidistribution).
  - `orPoly_error` — the `OR` polynomial `(∑ rᵢvᵢ)^{p-1}` has degree `p-1` and error exactly `1/p`.
- **Amplification** (`…ACC0ProbabilisticAmplification`): `t` independent forms ⇒ error `(1/p)^t`
  (`amplified_form_balance`), degree `t(p-1)`.

## 4. Substitution: degree and error both bounded (PROVED interfaces)

- **Circuit substitution error** (`…ACC0CircuitSubstitution.circuit_error_bound`): total error `≤ size·ε` (the hybrid
  union bound over gates).
- **Multilinearisation** (`…ACC0Multilinearisation`): a bounded-degree polynomial on the Boolean cube is a sparse
  `AND`-feature sum; **`…ACC0SubstitutionPoly.circuit_cube_count`**: the circuit *is* an `MvPolynomial` whose accept
  count is the sparse cube sum.
- **Degree composition** (`…ACC0AevalDegree.aeval_totalDegree_le` + `…ACC0LowDegreeSubstitution.psubst_degree`): low
  degree survives constant-depth composition (`δ^{depth}`); the per-gate degree factor is **discharged** from local
  gate degrees.
- **Error averaging** (`…ACC0ErrorAveraging.exists_good_seed`): per-input seed error ⇒ a fixed seed with bounded
  input error.
- **Calibration** (`…ACC0ErrorCalibration`): `p^t > 10·size` ⇒ circuit error `< 2^n/10`.

## 5. Read-off and the Route-B capstone (PROVED conditional)

- **Sparse read-off** (`…ACC0SparsePolyReadoff.sparse_readoff`): the cube sum is a sub-`2^n` count over `≤ (n+1)^D`
  features — the Williams `ACC⁰`-SAT speedup input.
- **`…ACC0RouteBComplete.routeB_to_NEXP_not_ACC0`** (axiom-free conditional): the proved approximation side backs the
  RS representation; with the abstract counting / Williams / hierarchy sockets, `¬ NEXPHasACC0Circuits`.

## 6. The Williams side — architecture proved, deep theorems socketed

- **Williams meta-theorem** (`…ACC0WilliamsMetaTheorem.williams_meta_theorem`, axiom-free): the easy-witness collapse
  + nondeterministic time hierarchy ⇒ `¬ (NEXP ⊆ ACC⁰)` (modus tollens).
- **Easy-witness collapse** (`…ACC0EasyWitness`): decomposed into the **IKW easy-witness lemma** and **guess-and-verify**;
  composition glue proved (`easyWitnessCollapse_from_parts`, axiom-free).
- **Concrete NTM hierarchy infrastructure**:
  - `…ACC0NTM` — abstract nondeterministic model, `NTIME`/`NEXP`, `acceptsWithin_mono`, `reachIn_add`.
  - `…ACC0ConcreteNTM` — concrete **encodable** machine model; `machineEquiv : TMachine ≃ ℕ` (machines enumerable).
  - `…ACC0TimeHierarchyDiagonal` — the **Cantor diagonal core proved** (`diag_not_mem_range`); hierarchy from
    enumerability + diagonal-simulatability.
  - `…ACC0UniversalNTM` — interpreter-level universal simulation; **`enum_covers` discharged** (a hierarchy socket is
    now a theorem); hierarchy down to one socket.
  - `…ACC0SimulationStep` — single-step ⇒ linear overhead `t·B` (`sim_acceptsWithin`).
  - Physical-`U` sub-machine **contracts proved**: tape encoding faithful (`…ACC0TapeEncoding`), rule-lookup correct
    (`…ACC0RuleLookup`), head-movement local (`…ACC0HeadLocation`), tape-rewrite contract (`…ACC0TapeRewrite`), atomic
    step (`…ACC0PhysicalStep`), decode round-trip (`…ACC0UniversalDecode`).

---

## The remaining sockets (the genuine classical mountains)

The separation reduces to these, each a classical theorem and a major formalization project in its own right:

1. **Physical universal Turing machine** (`hstep`) — construct `U` as an actual transition table that decodes `M` from
   its own tape and simulates one `M`-step in `B` of its own steps.  *Status:* model, enumeration, interpreter sim,
   overhead accounting, tape encoding, and all four sub-machine contracts + atomic step + decode round-trip are proved;
   the decode→step→re-encode **loop as `U`-transitions with a `B` bound** remains.
2. **IKW easy-witness lemma** — `NEXP ⊆ ACC⁰` ⇒ accepting `NTIME[2ⁿ]` computations have small `ACC⁰` witness circuits.
3. **Guess-and-verify** — small witness circuits + `ACC⁰`-SAT speedup ⇒ `NTIME[2ⁿ] ⊆ NTIME[2ⁿ/superpoly]`.
4. **Composite Beigel–Tarui degree** — the quasipolynomial composite `SYM∘AND` representation (the only deep open on
   the otherwise-proved approximation side).

**Bottom line.** The ACC⁰ / RS / BT approximation side is essentially worked through and machine-checked.  The route is
no longer vague: it is a precise reduction to named classical complexity-theory theorems.  Proving `NEXP ⊄ ACC⁰`
requires discharging the mountains above — none of which is new, and each of which is its own serious project.

---

## 7. Final consolidation — the composite-`MOD` wall, mapped exhaustively (entries 157–161)

The composite-`MOD` gate is the load-bearing object of the RS/BT approximation side.  The squarefree case is fully
proved (distinct primes → product of fields → Fermat per prime → CRT: `…ACC0CRTFinsetGate`), and the prime-power case
`p^e` is the genuine `ACC⁰[composite]` wall.  Entries 157–161 map that wall exhaustively — *not* by faking a
representation (that would be the open lower bound) but by pinning down precisely what is and is not possible.

### 7a. The prime-power obstruction, made precise (157)

`MOD_{p^e}` is **not a function of the mod-`p` residue** (`…ACC0PrimePowerObstruction.modPrimePower_not_function_of_modP`):
`0` and `p` share their mod-`p` residue yet `MOD_{p^e}` separates them.  So no `F_p` polynomial in the prime-`p`
residue — *at any degree* — computes it.  The working observer is the *ring* residue `ZMod(p^e)`.

### 7b. The observer scorecard — can a richer observer see `MOD_{p^e}`? (158–160)

The N-Frame question: can the tri-aspect boundary select a *richer algebraic observer* than `F_p` that sees `p^e`
information while keeping quasipolynomial control?  Tested four candidates, all proved:

| Observer | Verdict | Field? | Escapes the low-degree wall? | File |
|---|---|---|---|---|
| characteristic-`p` fields (`F_p`, `F_{p^k}`, …) | **REFUTED** — sees only mod-`p` | yes | — | `…ObserverCandidates` |
| #1 ring `ZMod p^e` | sufficient | **no** (zero divisors) | No | `…ObserverCandidates` |
| #2 valuation `v_p` (`MOD_{p^e} ⟺ v_p ≥ e`) | sufficient | no | open | `…ObserverCandidates` |
| #3 residue tower `ZMod p ← … ← ZMod p^e` | sufficient, **≡ #1** | no | No | `…TowerObserver` |
| #4 Witt / `p`-adic digits | sufficient, **≡ #1** | no | No | `…DigitObserver` |

The verdict across all four: **at the field level, no** (every characteristic-`p` field is refuted —
`charP_field_observer_fails`); the genuine sufficient observers are all **non-field** — either provably equivalent to
the zero-divisor ring `ZMod p^e` (#1, #3 via `tower_projection_compatible`, #4 via the digit↔residue bijection) or a
threshold/valuation (#2).  The tower and digit observers add *structure* (the graded ladder `{MOD_{p^i}}`, the Witt
decomposition) and *localise* the field obstruction (depth `e` required; field = lowest digit / case `e=1`), but none
lowers the degree.

### 7c. Route 1 — non-field low-degree theory: why the wall is genuinely open (161)

`…ACC0NonFieldObserverTheory` settles *why* the surviving non-field observers don't immediately help:

- **Over a field, the `MOD_{p^e}` indicator needs degree `≥ p^e-1`** (`modPrimePower_field_indicator_high_degree`): it
  rejects the `p^e-1` consecutive non-multiples, which are distinct in a char-`0` field, so root counting
  (`field_root_card_le_natDegree`) forces exponential degree.  The field route is *quantitatively* blocked.
- **Over the ring `ZMod p^e`, root counting FAILS** (`ring_root_count_fails`): `C(p^{e-1})·X` has degree `≤ 1` but two
  roots `0 ≠ p`.  So the very machinery that blocks the field route has no analogue on the non-field observer.

**Conclusion of the algebraic-observer programme.**  The field route is degree-blocked; every escape is non-field; and
on the non-field observers the degree-bounding machinery collapses — so a low-degree representation can be neither
exhibited nor excluded by these tools.  That is the honest location of the `ACC⁰[composite]` wall: it is the *absence of
a field* (where Fermat and root counting live), not a missing piece of glue.  Constructing a quasipolynomial low-degree
sparse representation over a non-field observer — or proving none exists — *is* the open lower bound.

### 7d. Route 1, sharpened — the sparse top-structure and the carry barrier (162)

`…ACC0ValuationSparseTheory` pushes Route 1 one honest step further by *locating the cost inside the valuation route*:

- **Sparse top-structure** (`modPrimePower_eq_and_of_downshift_modP`): `p^e ∣ s ↔ ∀ i < e, p ∣ (s/p^i)` — `MOD_{p^e}`
  is an `e`-fold **AND of `MOD_p` tests on the down-shifted counts**.  The top is sparse (`e` conjuncts).
- **Each conjunct is low-degree** (`downshift_conjunct_decided_by_lowdegree_gate`): `p ∣ (s/p^i)` is decided by the
  degree-`(p-1)` Fermat gate at `s/p^i` — the modular arithmetic is cheap.
- **The carry barrier** (`downshift_breaks_additivity`): `s ↦ s/p` is *not additive*, so it destroys the linear form
  `∑ Xᵢ` that makes `MOD_p` cheap; after one down-shift the argument is no longer linear in the bits.

So the residual difficulty is *not* the modulus — it is a sparse representation of the **down-shift / carry** `s/p^i`
in the input bits.  This is a sharper statement of the open target, not the breakthrough: constructing such a
representation is still the `ACC⁰[composite]` lower bound.

### 7e. Route 1, carry structure — the carry boundary dissected (163)

`…ACC0CarrySparseTheory` dissects the down-shift itself:

- **Exact decomposition** (`downshift_add_carry_identity`): `⌊(a+b)/p⌋ = ⌊a/p⌋ + ⌊b/p⌋ + ⌊(a%p+b%p)/p⌋` — the
  non-additivity is *exactly* one carry term.
- **Single bit** (`carry_le_one`): `⌊(a%p+b%p)/p⌋ ≤ 1` — one carry bit per addition.
- **No-carry success fragment** (`downshift_additive_no_carry`): `a%p+b%p < p ⇒` additivity holds, so the down-shifted
  count stays a linear form and the sparse representation goes through.
- **Carry obstruction** (`carry_not_function_of_downshifts`): `(0,0)` and `(p-1,1)` share down-shifts but differ in
  carry — the carry needs the low residues, not just the down-shifts.

This is the **dynamic boundary** N-Frame predicts: refining `MOD_p → MOD_{p^e}` forces the observer from field residue
to carry-aware `p`-adic filtration, and the carry is the extra datum.  Structure theory of the carry, not a
representation — the general (carry-present) regime remains the open lower bound.

### 7f. Route 1, the count carry is symmetric — sum of threshold gates (164)

`…ACC0CountCarrySymmetric` uses the fact that in `ACC⁰` the argument is a single **count** `s = ∑ᵢ xᵢ`, not a general
`a+b`.  The whole tower `s, ⌊s/p⌋, ⌊s/p²⌋, …` are functions of that one `s`, so the §7e residue obstruction dissolves:

- **Symmetric** (`count_carry_symmetric`): equal-weight inputs give equal carry — `⌊s/p^i⌋` is a function of `s` alone.
- **Sum of thresholds** (`count_carry_eq_sum_thresholds`): `⌊s/p⌋ = ∑_{j} [s ≥ j·p]` — a `SYM` form, the top structure
  Beigel–Tarui wants.
- **Small range** (`count_carry_range_le`): `⌊s/p⌋ ≤ ⌊n/p⌋`.

So the count carry *has* the symmetric `SYM` top-structure — but the gain re-localises the open difficulty to the
**degree of a Majority-flavoured threshold `[s ≥ j·p]` on the count**, which (composed over the tower) is the open
`ACC⁰[composite]` representation.  Symmetric structure: present and proved; threshold degree: open.

---

## 8. The dynamic-boundary capstone — observer selection, formalised (165)

`…ACC0DynamicObserverSelection` turns the N-Frame dynamic-boundary slogan into a theorem: the boundary does not merely
shrink states, it *forces the observer to refine* exactly when the coarser observer loses the information to evaluate
the fragment.  An **observer** `O : ℕ → α` reads the count; `Sufficient O f := ∀ x y, O x = O y → (f x ↔ f y)`;
`Finer O₁ O₀` means `O₁` distinguishes at least as much.

**The refinement ladder, proved up to thresholds:**

- **`resObs_insufficient_for_modPow`** — the residue observer (mod `p`) is *not* sufficient for `MOD_{p^e}` (`e ≥ 2`):
  `0` and `p` share their residue but `MOD_{p^e}` separates them.  Refinement is *forced*.
- **`padicObs_sufficient_for_modPow`** — the `p`-adic carry observer (the down-shift tower) *is* sufficient (via the
  §7d down-shift decomposition).  Refinement *succeeds* one level up.
- **`padicObs_finer_than_resObs`** + **`observer_refines_modp_to_padic`** — the `p`-adic observer refines the residue
  observer, so `MOD_p → MOD_{p^e}` is a genuine forced refinement.
- **`carry_observer_eq_threshold_observer`** — the carry observer factors through a Hamming-threshold observer (§7f),
  the next rung.

**The closure socket (the ACC wall):** that repeated refinement *closes* at a quasipolynomial-size Beigel–Tarui
`SYM∘AND` observer — making BT the *fixed point* of dynamic refinement, not an external trick — is recorded as an
explicit socket.  `dynamic_boundary_to_acc0_sat_speedup` is the pure-glue cash-out (modus ponens, **no axioms**):
`DynamicClosesAtBT → BTHasQuasipolySparse → Speedup`, every premise an unproved socket.  Discharging it *is* the open
`ACC⁰[composite]` lower bound.  So the dynamic boundary has not failed — it provably selects the residue→`p`-adic→
threshold ladder; what remains is precisely the proof (or refutation) that this ladder stabilises at a quasipoly BT
observer.

### 8a. The final conditional chain — `dynamic closure ⇒ NEXP ⊄ ACC⁰` (166)

`…ACC0BTClosureFrontier` freezes the capstone and states the whole reduction as **one theorem ending at the codebase's
actual separation statement** `¬ NEXPHasACC0Circuits` (not an abstract `Speedup`):

```
  dynamicClosure_to_NEXP_not_ACC0 :  DynamicClosesAtBT
                                       → BTHasQuasipolySparse        (closure_to_quasipoly)
                                       → ACC0SatSpeedup              (quasipoly_to_speedup)
                                       → ¬ NEXPHasACC0Circuits       (williams + hierarchy, via routeB_to_NEXP_not_ACC0)
```

It is **proved as glue and depends on no axioms** — pure composition through the already-proved Route-B/Williams
reduction.  `observer_ladder_proved` re-exports the proved foundation (residue → `p`-adic refinement).  The chain is
valid and machine-checked; its two load-bearing premises (`DynamicClosesAtBT`, `closure_to_quasipoly`) are the unproved
sockets that together *are* the `ACC⁰[composite]` lower bound.  **Everything around the wall is now proved; the wall
itself — the quasipoly BT closure — is the single named socket.**  This is the terminal scaffolding of the programme.

### 8b. The wall is the Beigel–Tarui theorem — and it factors (167)

**Crucial framing.**  `DynamicClosesAtBT` is, classically, the **Beigel–Tarui / Yao theorem** (every `ACC⁰` function
has a quasipoly-size `SYM∘AND` representation), and `NEXP ⊄ ACC⁰` (Williams 2011) is *also* a proven theorem.  So the
wall in this development is the **size of the Lean formalisation**, not mathematical openness; "proving the closure"
formalises a known result and is *not* a new separation or `P ≠ NP`.

`…ACC0ThresholdBTClosure` factors the BT size bound and shows which factors are already done:

```
  quasipoly SYM∘AND  =  (SYM top: ≤ n+1 states)  ×  (AND-feature layer: ≤ (n+1)^D)   held by  (fan-in ≤ D under composition)
                          symmetric_observer_state_le    beigelTarui_monomial_count_le        FanInStaysPolylog  ← SOCKET
                          PROVED                          PROVED (repo)                        the BT depth reduction
```

- **`symmetric_observer_state_le`** (proved): the `SYM` top is *linear*-state (`≤ n+1`) — not the bottleneck.
- **`bounded_fanin_feature_count_le`** (proved, repo): the bounded-fan-in AND layer is quasipoly (`≤ (n+1)^D`).
- **`quasipoly_BT_observer_of_fanin_preservation`** (proved glue): fan-in `≤ D` ⇒ feature count `≤ (n+1)^D`.

So both *size factors* of the BT bound are proved; the wall is refined to the single concrete lemma `FanInStaysPolylog`
— the Beigel–Tarui mixed-radix depth reduction (fan-in stays polylog under `ACC⁰` composition), a known theorem whose
full formalisation over arbitrary-depth `ACC⁰` is the large remaining work.  We do not prove it.

### 8c. The depth induction — `FanInStaysPolylog` reduced to one per-layer merge (168)

`…ACC0FanInRecurrence` carries out the "induct over circuit depth" step.  With `fanInAtDepth b factor d := factor^d · b`:

- **`fanin_bounded_by_recurrence`** (proved): the per-layer merge `layerFanIn (d+1) ≤ factor · layerFanIn d` iterates
  to `layerFanIn d ≤ factor^d · b` (induction on depth).
- **`fanInAtDepth_le`** (proved): for `factor ≤ L`, `d ≤ D`, this is `≤ L^D · b` — polylog for *constant* depth `D` and
  polylog `L, b`.  Constant depth is what keeps it polylog.
- **`quasipoly_feature_count_of_layer_merge`** (proved, chains to §8b): the per-layer merge + constant depth ⇒ bottom
  AND-feature count `≤ (n+1)^{L^D·b}` (quasipoly).

So `FanInStaysPolylog` is now reduced to **a single per-layer merge** `hstep` — that composing a gate's children's
`SYM∘AND` forms multiplies the bottom fan-in by only a polylog factor.  That per-layer merge is the genuine
Beigel–Tarui mixed-radix step; it is a *theorem* (BT and Williams are proven classically), and its full Lean proof over
a concrete `ACC⁰` gate datatype is the substantial remaining formalisation.  The depth induction around it is proved.

---

## The four remaining routes (no small glue left)

The algebraic-observer route is now exhaustively mapped (§7).  What remains are four big, independent projects:

1. **Non-field low-degree theory** (Route 1) — a non-field observer (`ZMod p^e` / valuation / digits) admitting a
   quasipolynomial sparse/low-degree representation.  *This is the actual composite-`MOD` wall* (§7c): the most
   N-Frame-aligned path and equal in strength to the `ACC⁰[composite]` lower bound.
2. **Physical fast-SAT verifier** — turn the sparse feature read-off into an actual machine evaluating/counting in
   `poly(b)` steps with the budget closing (`…ACC0WilliamsFastSat` grounds the combinatorics; the uniform realization
   is separation-strength).
3. **Physical universal TM** (`hstep`) — the decode→lookup→rewrite→re-encode loop as `U`-transitions with explicit
   overhead `B` (all sub-machine contracts proved; the loop assembly remains).
4. **IKW / NW hard-function machinery** — no-easy-witnesses ⇒ hard function ⇒ derandomisation ⇒ `NEXP ⊄ ACC⁰`.

**Status, restated.** This remains a machine-checked *conditional anatomy*, not a proof.  The algebraic side is pushed
to its honest mathematical limit; the four routes above are the genuine open content, each a major project and (for
Routes 1 and the Williams realization) of separation strength.  Nothing here is `NEXP ⊄ ACC⁰`, and nothing is
`P ≠ NP`.
