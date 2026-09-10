# Adaptive discovery and the scalar-query barrier

This work adds a concrete adaptive alternative to the exhaustive sample scan. Given a correct Boolean predicate-existence oracle, it discovers separating samples and independent basis wires using at most `(s + 1) * (n + 1)` oracle calls for an `s`-gate circuit on `n` Boolean inputs. The oracle is an explicit input whose implementation cost remains unresolved. **Polynomial-time discovery without that oracle and a superpolynomial SAT runtime lower bound are not proved.**

The work also proves an unconditional exponential query bound in a different, restricted model: a deterministic decision tree receiving only scalar Boolean output values must make at least `2^n` queries on its all-zero-answer path to decide whether the unknown function is ever true. That model withholds circuit syntax and internal wire values. Its bound does not apply to the circuit-aware adaptive algorithm, which instead uses an existential oracle over a numeric full-wire-row predicate.

The numeric and semantic counterexamples are now connected by a derived equality. In `GodMoveNumericCounterexample.lean`, take the exact rational residual of a supplied assignment's wire row against the current row span. Use its coordinates as coefficients of the existing normalized wire polynomials. The resulting polynomial lies in `wireSpace`, vanishes on every current sample, and evaluates at the supplied assignment to the residual's squared rational norm. Thus a nonzero residual gives a semantic counterexample, with concrete coefficients supplied by the numeric calculation. `accepts_iff_counterexample` proves the converse as well, provided the maintained numeric basis spans precisely the current sample rows. This checks a proposed assignment; it does not find that assignment.

`GodMoveCubeWitnessSearch.lean` implements the next step with an explicit `CubeOracle`. Its correctness contract says whether a supplied Boolean predicate has any accepting assignment. After one existence query, `findWitnessWithCount` fixes successive coordinates, choosing the false branch whenever its restriction still has a witness. It returns an actual accepting assignment when one exists, and returns `none` exactly when none exists. A negative initial answer costs one recorded oracle call; a positive answer costs exactly `n + 1`. Predicate restriction does not construct an exhaustive assignment table.

This is a predicate-existence oracle, not a supplied SAT implementation. Its arguments are Boolean predicate functions. The module does not implement the oracle, compile every predicate into a SAT instance, or bound predicate encoding and evaluation costs. The call-count theorem cannot be read as a machine runtime theorem.

`GodMoveAdaptiveDiscovery.lean` supplies the complete adaptive control flow. Its `outside` predicate runs the original circuit at an assignment and tests whether the resulting rational row adds a new direction. Each returned witness adds an independent direction to the maintained row basis. Starting with `s + 1` rounds of fuel suffices either to receive a negative existence answer or exhaust the possible independent directions. The following results concern this particular executable driver:

- `adaptiveSamples_separates` proves that the returned assignments separate the full computed-wire polynomial space under `OracleCorrect`.
- `adaptiveSamples_length_le` bounds the retained assignments by `s`.
- `adaptiveSearch_queries_le` bounds the recorded predicate-existence calls by `(s + 1) * (n + 1)`.
- `adaptiveBasis_spans`, `adaptiveBasis_linearIndependent`, and `adaptiveBasis_length_eq_wireRank` certify the actual wire indices selected by the subsequent numeric column scan.
- `adaptiveSATWord_eq_SATLang` proves equality with the repository's SAT language when the oracle satisfies its explicit correctness contract.

`GodMoveAdaptiveRefinement.lean` connects the actual driver to the earlier semantic residual-dimension theorem. Every emitted assignment is a counterexample to the samples preceding it. The returned sample count is therefore at most `wireRank c`; independence of the selected wire columns supplies the reverse inequality. The driver returns exactly `wireRank c` samples and the same number of basis wires. It also satisfies the sharper query bound `(wireRank c + 1) * (n + 1)`.

The new driver turns the iteration idea into an executable construction relative to an oracle. Neither the iteration bound nor the oracle-call bound assigns a cost to solving each existential query. Rational coefficient bit lengths, memoization of coordinate functions, and full operational runtime remain outside these bounds. These modules also do not construct the certified inverse weights required for a complete sampled gauge certificate.

`GodMoveBlackBoxQueryBarrier.lean` formalizes the separate value-query obstruction using a finite adaptive `QueryTree`. At each node the tree asks for the unknown function's value at one assignment and follows the corresponding Boolean branch. `zeroPath` records the points queried when all responses are false. If an assignment `a` is missing from that path, the singleton function that is true only at `a` follows exactly the same path and produces the same answer as the identically false function. Correctness on those two targets is therefore impossible without querying `a`.

`two_pow_le_zeroPath_length` and `two_pow_le_depth` prove the resulting `2^n` lower bounds. The stronger `two_pow_le_zeroPath_length_of_unit_tests` only requires correctness on zero and on the singleton functions realized by direct verifiers of `assignmentUnits a`. Those formulas have exactly `n` unit clauses, and `unit_verifier_length_le` bounds their verifier circuits by `5*n + 1` gates. The functions have small circuit descriptions, but those descriptions are deliberately unavailable in the query-tree model. A circuit-aware algorithm could read the prescribing unit clauses directly. This theorem is consequently a lower bound for exact scalar-value oracle testing, not SAT computation, full-wire-row query access, or production N-Frame gauge construction.

The existing SAT reductions still constrain the unresolved efficiency claim. Uniform polynomial-time discovery of samples separating every circuit's complete wire space, with polynomial output size and all ordinary evaluation costs included, would yield a polynomial-time SAT procedure by applying it to direct CNF verifier circuits. Such unrestricted discovery cannot coexist with a superpolynomial SAT runtime lower bound in the same model. A construction specialized to a hypothetical correct polynomial-time SAT decider has a different logical role, but would still need its own proved cost connection and an unavoidable lower bound on the same invariant. This work supplies neither that missing lower bound nor a proof of `P ≠ NP`.

Verification on 2026-09-10 used Lean 4.28.0:

```sh
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py \
  --dependency-checkout /home/darre/pall-lean \
  --log-dir /home/darre/godmove-audit-20260910/adaptive-checks
```

All **46 focused modules** passed, with **376 printed axiom checks**, zero
warnings, and only `propext`, `Classical.choice`, and `Quot.sound`. The checker
matched the 460-file source closure, including byte comparisons of imported
production sources and dependency configuration before using the Lake cache.
No production source changed. On a checkout with its own dependencies, omit
`--dependency-checkout`.

`GodMoveAdaptiveDiscoveryExamples.lean` supplies a concrete exhaustive oracle
and proves its correctness. Six guarded executable checks inspect actual
sample lists, basis indices, and the adaptive search's query counter. They
cover empty circuits, two-input AND, duplicate wires, a contradiction with a
constant, invalid wire references with reuse, and a zero-input constant-one
circuit. The AND case returns three samples, three basis wires, and ten
existential queries; duplicate wires return one sample, one basis wire, and
three queries. The oracle still enumerates internally. Its work is excluded
from the displayed query counter, and these tests do not establish efficiency.
