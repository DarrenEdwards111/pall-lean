# Exact designated-sheet extraction and its remaining source bound

This continuation constructs an exact extraction of the **actual nonmultilinear
production designated sheet** from the normalized output of a faithful SAT
machine. It derives the source-specific SPDP rank comparison, preserves the
paper's log/log parameters, and extends the extraction to an idempotent linear
projection on one ambient polynomial space. The source object and the named
source-to-target rank bridge are now supplied by constructions and proofs.

The SAT-specific runtime-derived polynomial bound for that source remains
unproved. These results do not establish separation.

## Exact extraction of the production target

Write `m = n / 3` and let `L` be the actual encoded length of the pinned
positive-unit formula on `m` variables. The source is

```text
P = circuitTarget (circuitFor M L (T L)).
```

It is the Boolean-normalized output polynomial of the actual unrolled machine
on **all** `L`-bit inputs, before any formula bits are fixed. The correctness
hypothesis is the faithful operational `Decides M SATLang T`.

[GodMoveSATUnitExtraction.lean](GodMoveSATUnitExtraction.lean) packages the
previously verified Boolean face and coordinate restriction into one algebra
map. The map uses the fixed unit-query template and its distinct assignment
positions. Machine correctness derives its output `∏ᵢ Xᵢ`; no satisfying
assignment, coefficient advice, polynomial identity, or rank bridge is supplied
as an additional input.

[GodMoveQuadraticSheetLift.lean](GodMoveQuadraticSheetLift.lean) proves that the
production `Step4Compiler.Step252.cookLevinStrictFOBTarget` is exactly

```text
Q = ∏ᵢ (1 - Xᵢ + Xᵢ²).
```

This is the same target wrapped by `routeBPaperFaithfulTPhiTarget`, including
its square terms. The adjacent constraints and their transition-skeleton
multiples vanish under the actual first-of-block restriction, leaving precisely
these booleanity factors. Substituting `Xᵢ ↦ 1 - Xᵢ + Xᵢ²` in the extracted full
monomial therefore recovers `Q` exactly. The target is not Boolean-normalized
after this lift.

[GodMoveSATDesignatedExtraction.lean](GodMoveSATDesignatedExtraction.lean)
composes those two explicit algebra maps. Its definition depends only on the
sheet size and fixed template. The historical `TuringMachine.DTM` indexes the
production target; the operational SAT decider is a separate
`ComposableMachine`. No simulation or equivalence between those models is
assumed. The connection here consists of the proved target identity and the
faithful operational source identity.

## Why the rank comparison holds on this source

The quadratic substitution is **not** asserted to preserve rank on arbitrary
polynomials. The proof compares the particular full monomial and quadratic
product through their actual shifted-derivative spaces.

[GodMoveFullShiftProductSpace.lean](GodMoveFullShiftProductSpace.lean) proves that,
for discrete blocks, `k ≤ m`, and `k ≤ ell`, the full monomial's strict SPDP space
is exactly the span of squarefree monomials missing at most `k` variables.
The quadratic-product proof factors each projected derivative row into an
active part and the affine factors of its undifferentiated variables. The
fixed involution `Xᵢ ↦ 1 - Xᵢ` transports these rows into that full-monomial
space. This supplies a common linear map and actual row preimages.

Combining this with unit-query extraction proves

```text
rank(target partition, k, ell, Q)
  ≤ rank(discrete source partition, k, ell, P).
```

The derivative and shift parameters remain unchanged. The target may retain
its actual coupled partition; its admissible row space is contained in the
discrete-partition row space. For `n ≥ 2²⁰`, the proved inequality
`log₂ n ≤ n / 3` discharges the remaining size condition at
`k = ell = log₂ n`.

The new `operationalPaperSource` fills `Theorem207PaperSource`, and
`operationalPaperSource_rank_bridge` fills
`Theorem207PaperSourceToTargetRankBridge` for that source and the designated
target. **`Theorem207PaperSourcePSideUpperBound` remains unfilled.** The complete
`Theorem207Witness` and a global rank-monotone-gauge contract are not supplied.

## An actual same-ambient idempotent projection

[GodMoveIdempotentExtractionExtension.lean](GodMoveIdempotentExtractionExtension.lean)
extends any algebra extraction `E : Poly L →ₐ[ℚ] Poly m` to a linear projection
on `Poly (L+m)`. Source and output variables occupy separate coordinates. If
`r_source` and `r_output` set the opposite coordinates to zero, the projection is

```text
Π(p) = embed_output
         (E(r_source(p)) + r_output(p) - C(coeff 0 p)).
```

Subtracting the common constant term makes the map fix every output-supported
polynomial. The proof gives `Π² = Π` globally and
`Π(embed_source p) = embed_output(E(p))` exactly.

[GodMoveSATDesignatedProjection.lean](GodMoveSATDesignatedProjection.lean)
instantiates this extension with the constructed sheet extraction. It proves
exact designated-sheet recovery and nonincreasing SPDP rank on the embedded
actual SAT-machine source, using the **same ambient discrete partition and the
same `k, ell`** on both sides. Injective renaming preserves the source rank when
the separate output coordinates are added. Idempotence holds globally; the rank
inequality is source-specific. The projection's range is the full output
polynomial space, not a proved small-dimensional space.

`designated_sheet_rank_le_projection` explicitly transports the original
target's coupled-partition rank into the projected polynomial's enlarged
discrete ambient space. With the production canonical compiler partition and
`n ≥ 2⁸⁰⁴`, `designatedProjection_rank_gt_npow200` consequently proves

```text
n^200 < rank(log₂ n, log₂ n, Π(embed_source P)).
```

Thus the existing designated-sheet lower bound survives the actual idempotent
extraction at the same window. No new source upper bound is inferred from this
lower-bound transport.

At that window the proved inequalities fit together as

```text
n^200 < rank(Q) ≤ rank(Π(embed_source P)) ≤ rank(embed_source P) = rank(P).
```

Here `Q` keeps its production coupled partition, while the embedded objects
use the same enlarged discrete partition. This is a lower bound on the
source; obtaining an incompatible upper bound from SAT runtime is still the
unproved step.

## What remains in the SAT-specific source bound

[GodMoveSATSourceCanonicity.lean](GodMoveSATSourceCanonicity.lean) proves that every
correct decider's normalized output at a fixed input length equals the language
characteristic at that length. Different faithful SAT machines and clocks
therefore give the same normalized polynomial. This equality isolates what
normalization retains; it does not provide a runtime bound for its rank.

For the unit-query family with `s` assignment variables, the file derives the
actual codec bound `L_s ≤ 23(s+1)²`. The existing binomial source minor then
excludes every eventual rank bound `C*(L_s+1)^d`, for strict and inclusive
windows and any shift-budget function. This lower-bound statement uses
derivative order `log₂ s`; it does not silently replace it with `log₂ L_s`.

The extraction uses easy positive-unit queries and a product of booleanity
factors. These structures already have large SPDP minors. Recovering them does
not establish unavoidable SAT difficulty or a runtime lower bound. A
SAT-specific theorem deriving a polynomial source-rank bound under a
hypothetical polynomial-time SAT decider would still require a new argument.
The earlier easy-language machine counterexample excludes a general
runtime-only bound, not every theorem that uses SAT correctness essentially.

Circuit unrolling and compact product syntax also do not pay for expanding
Boolean normalization or prove its rank is small. The coordinate selection and
linear extension above have mathematical definitions and correctness proofs;
this continuation supplies no compiled polynomial-time implementation theorem
for applying them to an expanded normalized source.

## Verification

The full focused run on 2026-09-10 passed with Lean 4.28.0: **80 modules,
627 printed axiom checks, zero warnings**, and a matched 498-file source
closure. Every printed dependency is among `propext`, `Classical.choice`,
and `Quot.sound`. No new `sorry`, custom axiom, or `native_decide` is used.
This checks the complete focused God-Move suite and its required production
imports; it is not a build of every historical module in the repository.

From the worktree root:

```sh
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py \
  --dependency-checkout /home/darre/pall-lean \
  --log-dir /home/darre/godmove-audit-20260910/designated-projection-checks
```

The checker verifies every imported production source and the Lean/Lake
configuration against the dependency checkout before using its cache. It
then compiles the audit modules in dependency order and rejects nonstandard
axioms. The result record is
`/home/darre/godmove-audit-20260910/designated-projection-checks/results.json`.
Independent review also checked the exact target identity, partition and
parameter transport, idempotence, and the stated scope of the remaining gap.
