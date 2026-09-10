# Revision audit: conditional discovery and separation

The revision in `4efa4fff` makes the proposed conditional strategy logically
consistent, but it does not defeat the unrestricted-selector-to-SAT reduction
or establish separation. Its samples are obtained using a **supplied correct
SAT machine**. Assuming such a machine for a proof by contradiction is valid.
An independent lower bound is still needed to reach a contradiction.

This audit checks the actual revised definitions, adds a formal connection to
the earlier selector-to-SAT reduction, and tests whether the correctness
assumption can be removed. No production definition is changed.

## What the revision proves

The key correctness theorem has this logical form:

```text
For every M,T:
  if Decides M SATLang T,
  then for every circuit c,
    machineSamples M T c separates the complete wire space of c.
```

The construction remains applicable to arbitrary supplied circuits. The
change is its dependence on a correct SAT machine, rather than a restriction
to a special class of circuits. Its actual requests use that machine on
encoded relation circuits, including varying query lengths. Correctness on
just one input slice is not its hypothesis; `Decides` supplies correctness on
every input word within the stated clock.

The old implication survives. `GodMoveSampledSAT.sampledSATWord_eq_SATLang`
still turns any universally separating selector into a correct SAT program.
An efficient implementation of that selector with efficiently readable
assignments would therefore provide an efficient SAT algorithm. The earlier
formal reduction proves language correctness and size bounds; it does not
include a complete Turing-machine runtime proof.

`GodMoveDiscoveryQuantifierAudit.revised_sampledSATWord_correct` instantiates
that old reduction with the new selector. The stronger semantic round-trip
theorem proves, under the same supplied correctness hypothesis,

```text
sampledSATWord (revisedSelector M T) x
  = decideOut M x (T x.length).
```

Thus the route is now SAT machine → separating samples → SAT answers. There
is no contradiction in this composition, and it does not produce a SAT
machine independently of the input machine. Equality of answers says nothing
about an improvement in runtime.

## The assumptions survive the added guarantees

The audit packages the revision's proved separation, exact basis size,
request-count, and adaptive coefficient-precision guarantees in
`DiscoveryGuarantees M T`. These follow from `Decides M SATLang T`.

It then defines `RevisedPolynomialCandidate` to explicitly contain a machine,
a polynomially bounded clock, SAT correctness, and those guarantees. Lean
proves:

```text
RevisedPolynomialCandidate ↔ SeparationTarget.InP SATLang.
```

This is an audit of redundant derived properties, not a new complexity-class
equivalence for a runtime-bounded discovery implementation. The package
already includes the hypothesized polynomial-clock SAT decider. Adding
guarantees satisfied by every such hypothetical decider does not exclude any
of them. The package contains no full host-runtime assertion.

The correctness assumption is essential. In
`GodMoveDiscoveryAssumptionCheck`, a concrete finite-control machine halts
immediately and rejects every word. With the zero polynomial clock it obeys
the existing request-count and adaptive precision bounds, but discovery
returns no samples. For the one-gate constant-true circuit on zero inputs,
that empty list fails `SeparatesWires`.

This is a kernel-checked counterexample to dropping the SAT-correctness
premise. It is not a counterexample to the conditional construction. Small
clocks, queries, coefficients, and outputs do not imply semantic correctness.

## What a valid separation argument would require

Suppose, for contradiction, that SAT is in P. Unpack the hypothetical
globally correct machine `M` and polynomial clock `T`. Using that same machine
to obtain samples is legitimate inside the assumption. A contradiction would
then have to follow from a separately proved property that this candidate
cannot satisfy.

For the current computed-wire rank, write

```text
R(M,T,L) = wireRank (circuitFor M L (T L)).
```

The existing `unrolled_wireRank_polynomial` already proves that `R(M,T,·)`
is polynomially bounded whenever `T` is. Discovery does not amplify this
quantity: its basis size equals the wire rank exactly. The new
`discoveredBasis_polyBounded_iff` proves that polynomial boundedness of the
discovered basis-size family is equivalent to polynomial boundedness of the
original rank family.

A sufficient missing lower bound for this route is:

```lean
∀ (M : Machine) (T : ℕ → ℕ),
  Decides M SATLang T →
  ¬ PolyBounded (fun L => wireRank (circuitFor M L (T L)))
```

`UnavoidableWireLower` names precisely that proposition. It is a definition,
not a theorem asserting it. `separation_of_unavoidableWireLower` proves that
**if** this lower bound is supplied, the existing runtime-to-rank upper bound
implies the repository's faithful target `SeparationTarget.SAT_not_in_P`.
The audit does not prove the lower-bound premise or claim it is equivalent
to the separation target.

The existing lower and upper bounds remain compatible:

```text
L - 22 ≤ R(M,T,L) ≤ circuitConstant M * (L + T L + 1)^4.
```

The lower bound is linear. Capturing the SAT output polynomial in the wire
span does not force superpolynomial dimension, and the proposed universal
derivative-span containment already has a formal counterexample. The exact
production gauge rank can transport a valid wire-rank bound, but preserving
all wires is an additional restriction; the unrestricted production-minimizer
obstruction is unchanged.

Completing discovery's full host-runtime theorem would address the requested
efficient construction. It is **not needed for the conditional rank-based
separation implication above**: the runtime-to-rank upper bound is already
proved. The decisive remaining mathematical result for that implication is
the independent universal superpolynomial lower bound.

The revision therefore supports a coherent conditional proof strategy. The
original selector-to-SAT implication continues to hold, and no separation
follows merely from the revised construction or its polynomial size bounds.

## Verification

On 2026-09-10, all **63 focused modules** passed, with **509 printed axiom
checks**, zero warnings, and only `propext`, `Classical.choice`, and
`Quot.sound`. The source-matched check covered a 481-file import closure.

The two added modules check the logical scope directly, using kernel proofs
instead of executable examples alone. Independent review checked that the
candidate equivalence retains its SAT-decider hypothesis and that the final
separation implication retains its explicit lower-bound hypothesis.

Reproduce the focused audit with Lean 4.28.0:

```sh
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py \
  --dependency-checkout /home/darre/pall-lean \
  --log-dir /home/darre/godmove-audit-20260910/revision-objection-checks
```

Omit `--dependency-checkout` when using the checkout's own dependencies.
