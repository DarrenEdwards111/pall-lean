# Flexible-Boundary Projected SPDP (PAC / Amplituhedron `piPhi`) — Status Audit

*Honest audit of the "flexible boundary" godmove: a projection `Π_flexible` (`piPhi` / gauge / quotient)
applied to the Cook–Levin compiled polynomial that should (P-side) drop the rank to `poly(n)` on a
trivial/P-time object while (NP-side) preserving the identity-minor rank `≥ superpoly(n)`. Two read-only
audits of ~20 files + direct signature checks. Verdict: the two required properties are **not both proved
for any real projection** — NP-preservation holds only where the projection is trivial, P-side collapse is
socketed everywhere and provably false for the only concrete map, and the codebase itself certifies the
missing map must be non-flat and is unbuilt. No `sorry`, no live `axiom` in the gauge files; the gap is
carried entirely in undischarged hypotheses. Nothing here is `P ≠ NP`.*

---

## The target (what `Π_flexible` must simultaneously achieve)

1. **P-side low**: `rank(Π_flexible(compiledPoly for a trivial/P-time machine)) ≤ n^200`.
2. **NP witness preserved**: `rank(Π_flexible(compiledPoly SAT/search object)) ≥ superpoly(n)`.
3. **Passes the trivial-DTM test** (must be low on a bare machine, not just a hard one).
4. **Constructed and proved**, not assumed.

## The load-bearing fact everything runs into (axiom-free, verified)

`GodMoveReal.compiledPoly_rank_gt_npow200_at_large_n` — for **any** `DTM M` with `timeBound ≤ 4`,
`numStates ≤ n`, at `n ≥ 2^804`: `n^200 < mlBlockedSpdpRank … (compiledPoly …)`. No `DecidesSAT`, no
hardness hypothesis. Its lower bound `compiled_np_lower_bound_any_dtm` is built from `fobFamily`
(first-of-block κ-subsets of the compilation grid) → the rank floor `C(n/3, log₂n)` is a **compilation
artifact, identical for the trivial machine and the SAT machine.** This is the wall.

---

## What is already PROVED (the scaffold is real)

- **Rank-monotonicity infrastructure.** `IsRankMonotoneGauge`, `SATDeciderGaugeRankMonotonicity`,
  `piPhi_isRankMonotoneGauge` (`PaperFaithfulCompilation.lean:240`, delegating to
  `PiStarConcrete.piZero_isRankMonotoneGauge`): `mlBlockedSpdpRank B κ ℓ (gauge p) ≤ mlBlockedSpdpRank B κ ℓ p`.
  Genuine — but this is the **only** direction available: rank can **decrease**. There is no absolute
  `≤ poly(n)` anywhere.
- **`piPhi` is defined and characterised.** `piPhi σ := PiStarConcrete.piZero (keepU σ)` — keeps `U`
  variables, kills `V` (tableau) variables.
- **`canonicalPathAWitness`** (`PaperFaithfulCompilation.lean`): the projection property, rank-monotonicity,
  and "fixes coupled-sheet embeddings" (`piPhi_embed_eq`) are proved for it.
- **PAC pipeline** (`PAC.lean`): restriction / tag-constant / gadget-multiplication / composition ops.
  `applyPipeline_rank_monotone` (line 704) is **proved but is a rank UPPER BOUND WITH BLOW-UP**,
  `rank(applyPipeline π p) ≤ N^{factorSum}·rank_shifted(p)` — not a decrease and conditional on the input's
  shifted rank.
- **Honest negative results** (proved): `identitySATDeciderGauge_not_pSideBound_at_large_n`,
  `r72_identity_not_pSide`, `matrixGaugeToPolynomialProjectionPiPhi_not_pSideBound_at_large_n`,
  `cookLevinRichProjectionTarget_forces_nonflat_witness` — the codebase certifies the trivial/flat
  projection is insufficient and any real witness must be `≠ id` and `≠ piPhi`.

## Trivial-DTM test — **FAILED** by the only concrete projection

The single projection that actually lands on the real flat Cook–Levin space is
`satDeciderGaugeMapPiPhi`, and `satDeciderGaugeMapPiPhi_eq_id` **proves it equals `LinearMap.id`** (on the
flat split, every variable is a `U` variable, so `keepU` keeps everything). Therefore:

- `satDeciderGaugeMapPiPhi_pSideBound_iff_unprojected_bound`: for flat `piPhi` the projected P-side bound is
  **equivalent to the unprojected one** — the projection buys nothing.
- and the unprojected bound is `compiledPoly_rank_gt_npow200_at_large_n`'s **negation**, so the P-side bound
  is **proved FALSE at paper scale** for this map. The trivial machine still has rank `> n^200` after
  projection. Test failed.

## NP identity-minor preservation — PROVED but **vacuous**

`partitionedOutput_cookLevin_projectedCompilerIdentityMinorLowerBound` /
`concreteCookLevin_piPhi_…_via_fixed_embed` do prove `identity-minor survives piPhi` for the real `piPhi`,
**unconditionally** — but only because (a) on the real object `piPhi = id` (survives trivially), and (b) the
"preserved" bound is the machine-independent `any-DTM` bound. It is a sanity check, not a distinguishing
result; the authors flag this themselves (`ProjectedIdentityMinorFrontier` "sanity check" docstring;
`GodMoveReal` "Semantic Gap Analysis"). "Identity" is a rank lower bound via a Kronecker-delta minor
(`SourceIdentityMinorLowerBound`, `IdentityMinorReal.KroneckerDeltaSystem`), genuine on the source sheet —
but preservation is by-construction extraction, not clever survival.

## What is OPEN / socketed (the real content, undischarged)

Every theorem that concludes the P-side low bound carries the hard part as an **explicit hypothesis** that
is nowhere discharged for a concrete projection:

| Socket (hypothesis) | Where | Note |
|---|---|---|
| `hunprojected : rank(compiledPoly) ≤ n^200` | `SATDeciderGaugePSideBridge.lean:34` | **provably FALSE** at `n≥2^804` |
| `CookLevinProfileTemplateCollapseLemma` | `SATDeciderGaugeFinalTarget.lean:66` | template collapse, open |
| `SingletonQuotientSATGaugePSideObligation` | `NonflatSingletonQuotientCandidate.lean:144` | posed as open Prop |
| `SATDeciderSpecificGaugeSubgoalDischarge` | `R72AmplituhedronFrontier.lean:201+` | assumes the whole frontier |
| `RouteBSATWindowedIncPSideRankBound` (+incl) | `PathC/PiPlusBooleanProjectedFinalFrontier.lean:116` | PathC hits same wall |
| `exists_amplituhedron_gauge_for_sat_decider` | `GlobalGodMoveGauge.lean:420` | **demoted from `axiom` to hypothesis/Prop** |

`CookLevinRichProjectionTarget` (`∃ gauge, rankMonotone ∧ PSideBound ∧ NPPreservation`) is stated as a
**target, never proved unconditionally**. The genuinely non-flat candidates
(`singletonQuotientSATGauge`, `satDeciderGaugeKeepFirstProjection`) are proved idempotent/rank-monotone/
non-trivial but **assert no P-side package** — their P-side field is an open obligation, and even their
rank-monotonicity is conditional on further hypotheses (`…GeneratorLift`, `…RowCommutatorVanishes`).

## The sharp structural point — why this route cannot close as posed

A rank-monotone gauge only delivers `rank(gauge p) ≤ rank p`. The floor `rank(compiledPoly) > n^200` is
(i) already above the target and (ii) **machine-independent** (same `C(n/3, log₂n)` grid family for trivial
and SAT machines). So:

- **Monotonicity alone cannot** pull an already-`> n^200` rank down to `≤ n^200`; a genuinely
  **rank-reducing, non-flat** projection is required (this is exactly `forces_nonflat_witness`).
- Any projection that keys **only on the compilation grid** treats the trivial and SAT machines
  identically (same floor) — so it either leaves both high (fails P-side) or drops both low (kills the NP
  witness). This is the danger HAL named, now pinned: to drop the trivial machine's rank while keeping
  SAT's, `Π_flexible` must key on the machine's **function** — i.e. **decide which machine is hard**.

That is a super-polynomial separation of the projected rank by machine hardness — a super-polynomial
circuit lower bound. **It is the same far shore as the scale-ceiling result**
(`ComputationalDepthNFrameScaleCeiling.lean`): `Π_flexible` is not a bridge to `P ≠ NP`; the projection
whose existence would matter (`CookLevinRichProjectionTarget`, forced non-flat) *is* the theorem. The PAC/
amplituhedron machinery is honest scaffolding — real rank-monotonicity, a real characterisation of `piPhi`,
real negative results — around a socket whose discharge is P≠NP.

## Verdict

- **PAC proves:** rank-monotonicity ops, `piPhi`, and a blow-up pipeline upper bound; two `axiom`s
  (`gadget_spdp_subspace_factoring` (Lemma 40c) — the strict version flagged **falsifiable** with a
  counterexample, the `Inc` variant the workaround) that are about gadget-multiplication rank, **not** about
  `piPhi` lowering `compiledPoly` rank.
- **Amplituhedron/PaperFaithful proves:** `canonicalPathAWitness` (projection + monotone + fixes-embed), and
  the P-side only ever "via the input P-side hypothesis" (`gauge_rank_sandwich`,
  `pathA_hypothesis_contradiction`).
- **Passes trivial-DTM?** **No** — the only concrete projection is the identity; P-side bound proved false
  for it.
- **Preserves NP identity minors?** **Yes but vacuously** — because the projection is the identity there and
  the bound is machine-independent.
- **Open:** a non-flat, rank-reducing `Π_flexible` that collapses the trivial/P rank below `n^200` while
  keeping SAT rank super-polynomial. Socketed everywhere, discharged nowhere; equivalent to a
  super-polynomial circuit lower bound.

**The flexible-boundary godmove is the same missing object under a new name: a projection that separates a
machine-independent rank floor by machine hardness = P ≠ NP.** Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

*Files audited: `PAC.lean`, `PaperFaithfulCompilation.lean`, `GodMoveReal.lean`, and PathB
`SATDeciderGaugeMapPiPhi / …PSideBridge / …RankMonotoneCriterion / …Candidate / …FinalTarget /
…RealFrontier / …IdentityObstructions`, `NonflatSingletonQuotientCandidate`,
`SingletonQuotient{RankMonotonicity,GeneratorLiftDecomposition}`, `MatrixInducedProjectionAttempt`,
`R72AmplituhedronFrontier`, `ProjectedIdentityMinor{Concrete,PaperFaithful}`,
`ProjectedNPIdentityPreservationProgress`, `ComputationalDepthInstrumentedSheetAudit`,
`GlobalGodMoveGauge`. Companions: `ComputationalDepthNFrameScaleCeiling.lean`, `NFRAME_BARRIER_MAP.md`,
`COMPOSITE_MEASURE_ATTEMPT.md`.*
