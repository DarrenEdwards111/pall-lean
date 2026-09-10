# Runtime rank and the designated God-Move sheet

This continuation tests the two remaining claims against actual production
objects. It proves that **a general polynomial runtime bound for normalized
SPDP rank is false**, and that **the current multilinear characteristic cannot
equal the designated strict coupled sheet**. It also transports an explicit
binomial lower bound into the actual normalized SAT-machine source.

The later [designated-sheet extraction](GodMoveDesignatedProjection.md)
supplies a quadratic lift that retains the nonmultilinear target and a
source-specific rank comparison. This does not invalidate the normalization
obstruction proved here; the lift does not normalize the target. The
SAT-runtime-derived source upper bound remains unproved.

These results do not prove P ≠ NP. The runtime counterexample is an easy
language, so it does not refute a theorem with an additional faithful
SAT-correctness premise. The designated-sheet result concerns the current
Boolean normalization and characteristic identification, not every possible
God-Move map or redesigned source. No production definition is changed.

## An actual linear-time machine violates the general rank bound

`GodMoveLinearTimeRankObstruction.lean` defines one fixed four-state machine
in the same `ComposableMachine` model as the faithful SAT connection. It
scans right until the first false bit and accepts exactly when that bit's
index is even. Tape cells past the input read false. The machine writes
nothing and halts on every input of length `L` within `L + 1` steps, including
empty and all-true inputs. The file proves its language belongs to `InP`.

Its normalized output uses the same actual unrolling and normalization as
the recent machine-face construction:

```
scannerSource L = circuitTarget (circuitFor scanner L (L + 1)).
```

Machine execution proves the exact polynomial identity

```
scannerSource L = 1 - X₀ + X₀X₁ - X₀X₁X₂ + … + (-1)^L ∏ᵢ Xᵢ.
```

`GodMoveTopCoefficientMinor.lean` proves a general fact: any multilinear
polynomial with a nonzero full squarefree coefficient has the complementary
derivative coefficient minor, scaled by that coefficient. Off-diagonal
entries would require a square in the source and hence vanish. Applying it
to the scanner's derived coefficient `(-1)^L` gives

```
choose L k ≤ rank(discreteBlocks L, k, ell, scannerSource L).
```

For every shift-budget function `ell : ℕ → ℕ`, the file then proves that no
eventual bound `C * (L + (L + 1) + 1)^d` holds at derivative order `log₂ L`.
This includes both zero shifts and the matched `log₂ L / log₂ L` window.
These machine-rank statements use the discrete partition; they do not
automatically establish the same counterexample for a different fixed paper
partition.
Thus arbitrary legal machine operations, halting, finite control, and even
linear runtime do not imply the requested polynomial bound for this
normalized invariant. This strengthens the earlier small-circuit example
to an actual uniform machine with a proved runtime and language semantics.

The counterexample has no SAT-correctness premise. A hypothetical proof using
additional consequences of correctness on every encoded SAT input would
require a separate argument; it cannot simply cite a general runtime bound
for normalized SPDP rank.

## Boolean normalization destroys the actual designated sheet

`GodMoveDesignatedSheetNormalization.lean` uses the production
`Step4Compiler.Step252.cookLevinStrictFOBTarget`. The definition
`routeBPaperFaithfulTPhiTarget` in
`PallLean/Paper93/Paper283/RouteBPaperFaithfulTPhiExtraction.lean`, lines 72–80,
wraps exactly this object. The proof does not substitute a generic surrogate
product for the target.

The strict coordinate map retains indices `3*i`. Every adjacent-pair
constraint and its transition-skeleton multiples vanish under this
restriction. The remaining booleanity constraints vanish on Boolean
assignments. Consequently the target polynomial `Q` evaluates to `1` at
every Boolean point, and the checked normalizer gives

```
normalize Q = 1.
```

The existing production identity minor applies to this same target and
canonical partition. At `n ≥ 2^804` the new theorem proves, at the **same
log/log parameters**,

```
n^200 < rank(Q),
rank(normalize Q) = 0.
```

Every verifier characteristic is multilinear. The audit proves no
multilinear polynomial of the target's arity can equal `Q` at this scale.
Therefore the recent Boolean-face extraction cannot reach this designated
sheet through the proposed characteristic equality. Agreement on Boolean
points is particularly insufficient here: all of the designated sheet's
large-rank structure is lost by normalization.

The target uses the historical `TuringMachine.DTM` compiler. The new
operational scanner and SAT connection use `ComposableMachine`. No theorem
silently identifies these machine models or replaces faithful SAT
correctness with the historical encoding-free `DecidesSAT` predicate.

## The actual normalized SAT source already contains a binomial minor

`GodMoveInjectiveRankTransport.lean` supplies exact strict rank equality under
injective variable renaming with its pullback partition, and the discrete
partition specialization. It also preserves the derivative coefficient
entries themselves and supplies inclusive lower-bound transport.

`GodMoveMachineSourceMinor.lean` combines this with the previously proved
Boolean-face extraction. For every actual machine satisfying
`Decides M SATLang T`, positive-unit queries give

```
choose n k ≤ rank(discreteBlocks L, k, ell,
                  machineSource M T (unitFormula n) n),
```

where `L` is the actual encoded template length. No rank-embedding premise
is assumed. The file derives arbitrary-power lower bounds and excludes an
eventual `C*n^d` rank bound on this source family. Here the logarithmic
derivative order is `log₂ n`, not silently `log₂ L`.

The unit formulas are easy. This proves high normalized source rank under
faithful SAT correctness, irrespective of its clock; it does not turn that
rank into a runtime lower bound or identify the verifier target with `Q`.

## Verification

All five new modules are included in the focused checker:

```sh
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py \
  --dependency-checkout /home/darre/pall-lean \
  --log-dir /home/darre/godmove-audit-20260910/runtime-sheet-checks
```

The checker matches the production-source closure and Lean/Lake configuration
against the dependency checkout, builds the imports, compiles the focused
modules, and checks the printed theorem axioms. The new proofs contain no
`sorry`, custom axiom, or `native_decide`.

The full run on 2026-09-10 passed with Lean 4.28.0: **73 modules, 581 printed
axiom checks, zero warnings**, with a matched 491-file source closure. The
five new modules contribute 40 of those checks. Every printed dependency is
among `propext`, `Classical.choice`, and `Quot.sound`. Machine-readable results
are in `/home/darre/godmove-audit-20260910/runtime-sheet-checks/results.json`.
