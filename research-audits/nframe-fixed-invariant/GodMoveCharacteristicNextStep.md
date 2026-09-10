# Continuing the characteristic-target construction

**10 September continuation:** [the compact machine-circuit connection](GodMoveCircuitConnection.md)
now supplies a shared symbolic source with explicit size bounds and exact
normal-form semantics. It also proves circuit-level obstructions to the
generic rank bound and to normalization-rank monotonicity. The runtime-derived
bound on the target's rank and the required hard-family lower bound remain open.

The requested separation is still **unproved**. This continuation checks two
specific steps needed by the proposed new characteristic target: obtaining a
minor from free witness padding, and representing/extracting the target
efficiently. It also inspects computation-dependent source candidates. None
of the missing source upper bound or hard-minor bridge is assumed to be true
in order to announce a separation.

## Free witness padding cancels exactly

`GodMoveCharacteristicPadding.lean` proves, for every Boolean predicate `f`,

    chi((a,b) -> f(a)) = rename(chi(f)).

The added bit `b` is unused. The proof explicitly pairs the two assignments
to it in the interpolation sum; their factors add to

    X_b + (1-X_b) = 1.

Thus the polynomial does not depend on `b`, and its derivative with respect
to `b` is zero. The file also proves the corresponding statement for the
genuine signed-CNF `verifierCharacteristic`, assuming the new variable does
not occur in the formula (`VariablesBelow n phi`). No equality or derivative
vanishing is supplied as a hypothesis.

The one-bit identity can be applied repeatedly to free padding. It does not
erase a minor already supported on the core variables. It does show that
acceptance multiplicity alone does not create dependence on the unused bits,
and cannot supply a minor requiring nonzero derivatives in those bits.
There is no claim that every definition of shifted rank, under arbitrary
partitions and shift conventions, is invariant under adding variables.

This addresses the desktop paper's section 34.5, printed pages 176–178:
Lemma 188 accepts every choice of ignored slack bits, and Lemma 189 explicitly
makes padding variables absent from the clauses. Corollary 190 then discusses
distinct monomials and a minor of a **coupled tableau/selector polynomial**.
The new theorem does not refute every possible such coupled construction;
it prevents transferring that assertion to the canonical witness-assignment
characteristic merely because the two constructions have the same acceptance
predicate. A copied-bit/tableau target retaining extra variables would need
its own verified extraction and rank analysis.

## Exact characteristic evaluation contains counting information

`GodMoveCharacteristicCounting.lean` defines `satisfyingCount n phi` as the
cardinality of the finite set of satisfying `n`-bit assignments (extended by
false outside those variables). It proves the exact rational identity

    satisfyingCount(n,phi)
      = 2^n * verifierCharacteristic(n,phi)(1/2,...,1/2).

Each delta-basis polynomial evaluates to `2^(-n)` at that point, so the
identity follows directly from the interpolation sum. With `VariablesBelow`,
the count is positive exactly when the genuine signed CNF is satisfiable.
As a regression case, the empty formula has exactly `2^n` satisfying
assignments.

The same exact counting identity is proved for the actual pinned-query
`machineQueryPolynomial`, using the previously constructed faithful handshake
and actual machine correctness. A final generic corollary records the
necessary consequence for any representation whose extraction is exact; its
`hexact` premise is **not** a construction of that extraction.

This is an algebraic reduction, not a proved complexity-class separation.
In particular:

- It does not prove counting requires superpolynomial time.
- It does not prove that a hypothetical polynomial-time SAT decider is
  impossible, or that such a decider cannot participate in a different
  construction.
- An alleged uniform polynomial-time exact extractor followed by an exact
  polynomial-time evaluator would have to justify how it supplies these
  counts. Boolean-cube evaluation alone is not that evaluator.
- A short ordinary arithmetic circuit alone is not being asserted to have
  polynomial-time exact rational evaluation: constant encodings and
  intermediate bit sizes also require analysis.

There is a relevant independently established warning about treating
multilinearization as cost-free. Hrubeš proves, **assuming VP is not VNP**,
that polynomial-time Boolean functions, even monotone 2-CNFs, can have
multilinear representatives requiring superpolynomial arithmetic circuits.
This is a conditional algebraic-complexity result, not a proof of P versus NP.
[Primary source: ECCC TR15-067, *On hardness of multilinearization, and VNP
completeness in characteristics two*](https://eccc.weizmann.ac.il/report/2015/067/).
It is contextual literature, not an axiom used in either Lean file.

## Computation-dependent candidates inspected

No inspected candidate currently derives a polynomial bound on actual
`mlBlockedSpdpRank` from faithful `ComposableMachine.Decides M SATLang T`
and a polynomial clock.

| Candidate | What is available | What remains missing or fails |
| --- | --- | --- |
| Physical-write dynamic quantity | `physicalWriteSPDP_global_le_clock` bounds actual per-run write charges by the clock. | This is an additive event count, not the characteristic polynomial's SPDP rank; no same-target minor bridge is supplied. |
| Dynamic boundary preservation | `DynamicSPDPPreservationFromCorrectnessFor` describes a boundary decoder. | Its projection already assumes `polyBoundary`; `decode_correct_of_decides_dynamic` is also a field, not a derived operational theorem. |
| Balanced time-unrolled composition | `balancedPower_eval` faithfully composes machine transitions. | `bondDimension` remains the full state-space cardinality, with no polynomial bound obtained merely by balancing. |
| Singleton quotient | The quotient removes designated rows. | `not_SingletonQuotientResidualGeneratorRowsKilled` already refutes its proposed derivative-stability condition for the current compiler. |

These findings come from source inspection, not a fresh rebuild of all four
historical routes. Their files are respectively
`ComputationalDepthComposableMachineDynamicSPDPEventCap.lean`,
`ComputationalDepthPvsNPDynamicPreservationFromCorrectness.lean`,
`ComputationalDepthTimeUnrolledTensorNetwork.lean`, and
`SingletonQuotientResidualRows.lean`, under
`PallLean/Paper93/DeepMath/PathB/`.

An actual continuation still needs a computation-dependent source, a
runtime-derived bound for its specified invariant, and an extraction retaining
the designated lower-bound minor at matched parameters. These files do not
provide that missing combination or mark it complete.

## Verification

Both new standalone files compile without warnings; their 15 printed theorem
checks use only subsets of `propext`, `Classical.choice`, and `Quot.sound`.
No proof placeholder or custom axiom was added. They were checked with Lean
4.28.0 using the cached dependencies from `/home/darre/pall-lean`.
Relevant imported source files
match this worktree. No production compiler, invariant, or theorem hypothesis
was changed. See the [handshake reproduction commands](GodMoveHandshake.md#lean-checks)
for the dependency setup, then run from the checkout root:

```sh
handshake_audit_dir="$PWD/research-audits/nframe-fixed-invariant"
lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean --root="$1" "$1/GodMoveCharacteristicCounting.lean"' _ "$handshake_audit_dir"
lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean --root="$1" "$1/GodMoveCharacteristicPadding.lean"' _ "$handshake_audit_dir"
```
