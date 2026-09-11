# Actual runtime, snapshot rank, and the remaining derivative gap

2026-09-11. Continuation of `5a5a816a`.

This continuation proves a quadratic runtime bound for a specific gauge in
the unchanged production N-Frame type. The gauge spans actual tape, head,
and control coordinate functions and fixes the actual SAT decision
polynomial. It does **not** prove the runtime bound on the full derivative
space required for separation. A concrete machine demonstrates that those
two spaces can have incompatible dimensions.

## The bound derived from the machine

Fix a machine `M`, encoded input length `L`, and clock `t`. Write `q` for
the number of its control states and `S = L+t+1`. The existing operational
semantics prove that the tape and head remain within this window through
time `t`; the new `snapshot_covers_configuration` theorem specializes that
fact to every length-`L` input.

For every time from zero through `t`, interpolate the actual Boolean
function of each of the following coordinates over all length-`L` inputs:

* `S` tape bits;
* `S` one-hot head indicators;
* `q` one-hot control-state indicators.

Let `W(M,L,t)` be their rational linear span. The finite family has
`(t+1)(2S+q)` members. Lean proves

```
dim W(M,L,t) ≤ (t+1)(2(L+t+1)+q) ≤ (q+2)(L+t+1)².
```

The bound permits all the legal machine operations, including writes,
rereading, state reuse, and halted self-loops. It makes no SAT correctness,
small interface, derivative closure, or rank-budget assumption. Runtime
bounds the memory window, and the number of coordinate functions bounds
the dimension of their span. It does not count distinct joint machine
configurations as if there were only polynomially many of them.

These are symbolic functions on the **entire input slice**. This is not
the dimension of the scalar values observed in a single execution. The
interpolation definitions are semantic; their expanded coefficients are
not constructed within a polynomial-time budget here.

## Exact capture in the production gauge

`GodMoveFiniteStateInterpolation` proves the finite-state identity

```
characteristic(accept ∘ state)
  = Σ_s bit(accept(s)) · characteristic(state = s).
```

Applied to the actual final machine state, this proves that the decision
polynomial belongs to `W(M,L,t)`. The state indicators also sum to the
constant polynomial one. Both memberships are derived from the real
state partition, rather than added as requirements on a proposed gauge.

`GodMoveRuntimeSnapshotGauge.snapshotGauge` applies the previously proved
linear-complement construction to this space. Its projection is idempotent,
its range is exactly `W(M,L,t)`, and its production rank is consequently
bounded by the expression above. It fixes every captured snapshot and
the normalized output of `ComposablePpolyDischarge.circuitFor M L t`.

If `Decides M SATLang T`, then at `t=T(L)` it fixes both the existing
`satDecisionTarget L` and the canonical `languageCharacteristic SATLang L`.
If the clock is polynomially bounded, its production rank is polynomially
bounded in the actual encoded length `L`.

The production action is also evaluated exactly. With the existing
permitted zero coordinate field and unit rank/barrier weights,

```
fullLagrangianFixed α 1 1 G snapshotGauge
  = rank + 1/(1+rank)
  ≤ (q+2)(L+t+1)² + 1.
```

No production definition or minimization domain is changed. Choosing the
linear complement uses classical choice; the theorem does not provide
an efficient basis finder or projection algorithm, assert variational
minimality, or assert that these zero geometric coordinates faithfully
encode the machine's geometry.

An earlier theorem already gave a quartic runtime bound for the gauge
spanning computed circuit wires. The quadratic estimate here is for the
new **snapshot gauge**, not an improved estimate on every intermediate
wire or on the existing designated-row projector.

## Why this does not finish the required connection

The designated hard minor concerns shifted partial derivatives of the
source. Fixing that source polynomial does not imply fixing its
derivatives. Nor does mapping the snapshot span through the designated
projector identify the resulting image with that projector's full range.

The existing four-state, read-only scanner makes this distinction concrete.
On 16 input bits at its proved clock of 17 steps, the snapshot bound is

```
dim W(scanner,16,17) ≤ 18(2·34+4) = 1296.
```

Its actual normalized decision polynomial has a strict unshifted
fourth-derivative space under discrete blocks of dimension at least
`choose(16,4) = 1820`. Thus that derivative space
cannot be contained in the snapshot span, even though the exact output
polynomial is contained there. `GodMoveSnapshotDerivativeObstruction`
checks this noncontainment in Lean using the existing scanner correctness
and complementary-column minor proofs.

This scanner decides an easy language, so this is not a counterexample to
a theorem that also uses SAT correctness. It rules out the universal
inference from legal machine steps and output preservation to derivative
containment in this particular space. A SAT-specific proof must supply
additional structure that puts the required independent rows in a common
runtime-bounded space, or provide another invariant with both valid bounds.
Neither that extraction nor separation is proved in this continuation.

The earlier circuit-gluing result has the same limitation: a logarithmic
interface would bound one response matrix, but this alone does not bound
the full family of differently labelled derivative rows used by SPDP.

## Validation

The new modules are included in `check_godmove_circuit.py`, which matches
imported production source and configuration against the dependency
checkout before rebuilding and checking theorem axioms.

Run from this checkout:

```bash
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py \
  --dependency-checkout /home/darre/pall-lean \
  --log-dir /home/darre/godmove-audit-20260911/snapshot-checks
```

The complete run passed on Lean 4.28.0: 113 audit modules, a 532-file source
closure, and 901 printed axiom checks. The focused modules emitted zero
warnings; their theorems use only `propext`, `Classical.choice`, and
`Quot.sound`. The four new modules account for 31 of those checks. The
production dependency build succeeded and replayed existing linter warnings.
The machine-readable result is
`/home/darre/godmove-audit-20260911/snapshot-checks/results.json`.
