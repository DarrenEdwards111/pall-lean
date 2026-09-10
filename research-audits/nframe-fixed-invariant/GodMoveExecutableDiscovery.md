# Executable discovery of separating samples and basis wires

The subsequent [adaptive continuation](GodMoveAdaptiveDiscovery.md) replaces
the outer exhaustive scan with boundedly many predicate-existence oracle
calls. It keeps the oracle's implementation cost explicit and proves a
separate obstruction for algorithms restricted to scalar output queries.

This work replaces the supplied sample-selector hypothesis with an executable algorithm. It scans actual circuit-wire values, retains assignments only when they add a new rational direction, and proves that those assignments separate the entire computed-wire polynomial space. A second scan of the transposed sample matrix selects actual wire indices whose normalized polynomials are an exact basis. Their number equals `wireRank c`, giving an executable exact rank calculation as well.

The first scan uses all `2^n` Boolean assignments. This completes an exhaustive discovery construction; **efficient general discovery and a superpolynomial SAT lower bound remain unproved**. The finite output can be small even though finding it inspects an exponential input table.

The current construction keeps the distinction between numeric data and polynomial semantics. It runs the original Boolean circuit at each supplied assignment, reads the emitted wire values, and converts those Boolean values to rationals. It does not expand normalized polynomial coefficients to evaluate these rows. A separate theorem identifies each numeric entry with evaluation of its normalized wire polynomial.

The source establishes the following components:

- `GodMoveBooleanWireTable.lean` defines executable `allAssignments`, `wireRow`, and `wireTable`. The assignment enumeration is complete and has no duplicates. Both the assignment list and the labeled wire table have exactly `2^n` entries. `wireRow_eq_normalized_eval` identifies the operational wire values with the existing polynomial semantics.
- `GodMoveRationalRowBasis.lean` defines exact rational orthogonal projection, residuals, insertion, and a complete labeled row scan. The residual zero test is equivalent to old-span membership. `selectRows` retains original entries; its returned rows are independent and span exactly all supplied rows. Their count equals the input row-space dimension and is at most the row width. The internal nonzero orthogonal residuals justify the arithmetic divisions. No square roots or floating-point arithmetic enter these operations.
- `GodMoveRowSpanSeparation.lean` proves that spanning all Boolean wire rows implies `SeparatesWires` for the selected assignments. The proof represents each wire-space polynomial by wire coefficients, transports vanishing across the numeric row span, and then uses multilinearity to turn vanishing on the entire Boolean cube into polynomial equality. The semantic separation property is therefore a consequence of row-span coverage, rather than an additional premise imposed on the row-selection algorithm.
- `GodMoveSampleRefinement.lean` proves an independent bound for counterexample-guided discovery. Its residual subspace contains exactly the computed-wire polynomials that vanish on the samples selected so far. A supplied nonvanishing polynomial/assignment pair strictly decreases the residual dimension. Zero residual dimension is equivalent to separation, and every nonseparating state has a Boolean counterexample. A successful refinement trace has length at most `wireRank c`, hence at most the circuit's gate count. Finding the next counterexample, or certifying that none exists, is explicitly outside this iteration bound.

`GodMoveExhaustiveDiscovery.lean` connects the scanner to the Boolean table. `discoverSamples_separates` derives global polynomial separation from this specific executable scan. It returns at most `c.length` assignments. The resulting `exhaustiveSATWord` equals the repository's `SATLang` on every encoded word, with no selector or separation hypothesis supplied by its caller. For a formula whose faithful encoding has length `L`, at most `L` samples are retained, occupying at most `3*L*(L+1)^2` assignment bits under the existing witness-arity convention. These bounds concern the returned data, not the exhaustive search table or working storage.

`GodMoveSampledWireBasis.lean` proves the second semantic bridge. On separating samples, numeric column spanning lifts to equality with `wireSpace`; numeric independence lifts to independence of the actual wire polynomials. `GodMoveExhaustiveWireBasis.lean` then applies the same executable selector to all wire columns. `discoverBasis_spans`, `discoverBasis_linearIndependent`, and `discoveredRank_eq_wireRank` certify the selected basis and its exact dimension. The basis has at most as many entries as the selected sample list, which itself has at most one entry per gate. It consists of valid wire indices, so selection does not expand polynomial coefficients.

The exhaustive table remains the dominant unresolved efficiency issue. Its length is exactly `2^n`, and no theorem reduces the number of assignments inspected to a polynomial. The rational row algorithm has no proved bound on coefficient bit lengths or full execution time. In addition, vectors are represented as coordinate functions, so the definitions alone do not establish memoization or a cost bound for repeated coordinate evaluation. “Executable” here means that the finite numeric definitions can be evaluated; it does not mean that their runtime has been proved polynomial, or even that a particular overall exponential upper bound has been formalized.

The refinement result identifies a different route for future work: only linearly many successful discoveries are needed if counterexamples can be obtained. It does not supply that search operation. A SAT-assisted implementation could search for a Boolean assignment violating a candidate rational relation between wires, but neither a polynomial-time SAT oracle nor the full oracle algorithm and its bit-cost analysis is supplied by this result. The bound on successful refinements cannot be substituted for a bound on time spent searching for them.

The earlier `GodMoveSamplingBarrier`, `GodMoveSampledSAT`, and `GodMoveRankIncrementSAT` results remain relevant to any proposed efficiency improvement. A selector that separates every supplied circuit's full computed-wire space also finds a satisfying assignment for a direct CNF verifier whenever one exists. Exact rank values likewise decide SAT through the two-control, four-gate rank comparison. Thus a uniform polynomial-time discovery procedure for unrestricted circuits, with polynomial-size output and ordinary evaluation costs accounted for, would give a polynomial-time SAT procedure. Such a result cannot coexist with a superpolynomial SAT runtime lower bound in the same computational model. The repository's current correctness reductions do not themselves include the composed machine/runtime proof needed to state this as a formal complexity-class theorem.

A construction specialized to the computation of a hypothetical correct polynomial-time SAT decider has a different logical role. It can be one component of a contradiction argument without supplying unrestricted efficient discovery for arbitrary circuits. That approach still needs a faithful construction with proved cost properties and an unavoidable lower bound on the same quantity. These new discovery modules supply neither such a superpolynomial SAT lower bound nor a proof of `P ≠ NP`.

The existing sampled gauge can be evaluated from supplied basis-wire references and rational weights. The new code discovers separating samples and independent basis wires exhaustively. It does not construct the certified inverse weights or a complete `WireCertificate`, and it does not prove bounded-cost gauge evolution. The current production definitions and the restrictions needed for their wire-preserving interpretation are unchanged. The previous obstruction to growing rank for unrestricted production minimizers continues to apply.

Verification on 2026-09-10 used Lean 4.28.0 and the focused checker:

```sh
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py \
  --dependency-checkout /home/darre/pall-lean \
  --log-dir /home/darre/godmove-audit-20260910/discovery-checks
```

All **40 modules** passed, with **332 printed axiom checks**, zero focused
warnings, and only `propext`, `Classical.choice`, and `Quot.sound`. The runner
checked the 454-file source closure and byte-matched imported production
sources and dependency configuration before using the existing Lake cache.
No production source was changed. On a checkout with its own dependencies,
omit `--dependency-checkout` to use that checkout's Lake environment.

The checked examples include an empty circuit, a two-input AND circuit, and
duplicate wires. Six guarded `#eval` comparisons also verify the selected
sample lists, the selected basis indices, and zero/constant-one ranks. These
are executable regression checks, separate from the general kernel-checked
theorems; they introduce no theorem axioms. The AND circuit retains samples
`01`, `10`, `11` and all three wires, whereas duplicate input wires retain
one sample and only the first wire. The zero and constant-one circuits have
computed ranks zero and one respectively.
