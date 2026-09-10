# God-Move: actual machine face extraction and certificate cost

This continuation proves a concrete extraction with derived rank transport.
It does **not** prove P ≠ NP. The polynomial upper bound for the normalized
machine source, and its connection to the paper's hard coupled sheet, remain
unproved. No production invariant or machine-correctness definition is changed.

## Actual machine source and extracted target

Let `L` be the length of the symbolic encoding of `φ` with an assignment
pinned by unit clauses. The source in `GodMoveMachineFaceExtraction.lean` is

```
P = normalize (rawPoly (circuitFor M L (T L))).
```

This is the actual clocked machine's output polynomial on all `L`-bit input
words. It represents a shared circuit for that whole input family, not one
execution on the original unpinned formula. The underlying circuit already
has a derived quartic gate bound in `L + T L + 1`, with a machine-dependent
constant. That bound does not cover the expansion or SPDP rank of `P`.

`GodMovePinnedFaceLayout.lean` proves that each assignment bit occurs exactly
once in the template. Its injective map `variablePosition` embeds these bits
in the ambient `L` input coordinates. All other coordinates are constants.
This matters: the specialization is an ordinary constant restriction, with
no identification of distinct polynomial variables. The position map is
defined by choosing a proved unique syntactic occurrence, not by choosing a
satisfying assignment. These results do not establish an executable runtime
bound for constructing the position map.

The gauge `pinnedGauge φ n` retains those positions and fixes the other bits
to their template constants. It is the existing concrete `PiStarConcrete`
linear substitution, and is idempotent. The gauge depends on the formula
template alone; neither a SAT witness nor machine-output advice is supplied.

The unconditional `pinnedGauge_extracts_compactTarget` identifies its output
with the renamed normalized output of the specialized machine circuit.
`pinnedGauge_extracts_verifier` then uses the actual machine premise
`ComposableMachine.Decides M SeparationTarget.SATLang T` to derive

```
pinnedGauge φ n P = rename (variablePosition φ n) (verifierCharacteristic n φ).
```

This is an exact polynomial identity, not merely agreement on Boolean
points and not an assumed extraction field. The proof first derives the
Boolean evaluations from the circuit semantics, then uses multilinearity
and injective renaming to obtain polynomial equality.

## Rank transport at unchanged parameters

`GodMoveMultilinearRestriction.lean` proves that constant substitution cannot
increase the production strict blocked multilinear SPDP rank **when the
source is multilinear**, for arbitrary rational fixed constants. It also
proves the inclusive-window version. Both compare the same ambient space,
block partition, derivative parameter, and shift bound.

The proof derives substitution on monomials and constructs a preimage for
each target generator. Derivatives involving a dropped variable vanish.
For retained derivatives, the permitted shifts use only differentiated
variables; therefore dropped-variable exponents remain at most one, allowing
multilinear projection to commute with the restriction.

Applied to `P`, this gives the checked theorem
`verifier_rank_le_machineSource`, and its inclusive counterpart:

```
rank(B,k,ell,rename position verifierCharacteristic) ≤ rank(B,k,ell,P).
```

The left side stays in `Fin L`. Transporting a lower bound originally stated
in `Fin n` additionally requires the appropriate block compatibility; this
result does not silently assume that compatibility. It also does not turn
the verifier characteristic into the paper's hard coupled sheet.

The multilinearity premise is essential. Boolean normalization can increase
the chosen rank, as already checked in the focused suite. Applying the new
restriction theorem after normalization therefore leaves the source-rank
cost of normalization unresolved. Small circuits can also have large
characteristic rank. The circuit gate bound is insufficient to conclude the
God-Move P-side rank bound.

## Every local accumulator certificate pays for the extracted target

`GodMoveAnyCertificateRank.lean` addresses the local-equation alternative.
For arbitrary polynomial multipliers, suppose an actual certificate satisfies

```
w_m - Q = A * (w_0 - 1) + Σ_i C_i * (w_(i+1) - w_i * f_i).
```

Retain all variables of `Q` and set the accumulator wires to zero. Every
step equation vanishes, while the initial equation becomes `-1`. Consequently
the certificate itself derives `piZero A = Q`. This holds even if factors
and multipliers depend on accumulator wires; no suffix-product form of the
certificate is assumed.

The existing zero-substitution rank theorem and a proved support inclusion
then give

```
rank(B,k,ell,Q) ≤ rank(B,k,ell,A),
totalDegree(Q) ≤ totalDegree(A).
```

Thus every certificate of this form carries the target's rank and degree
in the initial-equation multiplier. Low-degree local generators alone do
not provide a cheap extraction. This is a certificate-rank/degree result;
neither quantity alone is an arithmetic-circuit or SAT-runtime lower bound.
It does not rule out every redesigned God-Move source.

## Verification

The five new Lean modules are included in `check_godmove_circuit.py`. Run:

```sh
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py \
  --dependency-checkout /home/darre/pall-lean \
  --log-dir /home/darre/godmove-audit-20260910/face-extraction-checks
```

The checker compares the imported production sources and configuration with
the dependency checkout, builds those imports, compiles the focused modules,
and records the printed theorem axioms. The new files introduce no axiom,
`sorry`, or `native_decide` proof.

The full focused run on 2026-09-10 passed with Lean 4.28.0: **68 modules,
541 printed axiom checks, zero warnings**, and a matched 486-file source
closure. Every printed dependency is among `propext`, `Classical.choice`,
and `Quot.sound`. The five new modules account for 32 of those axiom checks.
The machine-readable results are recorded in
`/home/darre/godmove-audit-20260910/face-extraction-checks/results.json`.
