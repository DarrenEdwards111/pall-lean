# Cached construction and exact SAT-call clock accounting

The new construction removes nested residual-function recomputation from
discovery and column selection, and proves a polynomial bound on the sum of
the actual SAT-call clocks. The complete construction's bit-runtime bound and
the SAT-specific derivative-rank bound remain unproved. Separation is not
established.

## The executable construction changed

The original `RowBasis.grow` retains a residual as a function. Evaluating a
later component can call earlier residual functions repeatedly, and the old
selection scan calculates acceptance again after insertion. Small query
counts and short rational values do not by themselves bound this evaluation
work. This is a source-level recomputation issue; no lower bound on Lean's
backend execution is inferred from it.

The new `GodMoveCachedProjectionConstruction.construct` uses the following
materialized stages:

1. `GodMoveCachedDiscoveryBasis` stores each orthogonal row and its squared
   norm. An insertion calculates its component vector, residual vector and
   squared norm once. A zero-norm comparison chooses whether to append.
2. `GodMoveCachedResidualMatrix` stores all residual relation coefficients
   before queries. It first materializes the scaled orthogonal rows, then
   calculates each matrix entry with the counted dot-product loop.
3. `GodMoveCachedRowFinder` reads the stored matrix when calculating precision
   budgets and constructing each rational query. The original adaptive
   witness search still supplies actual assignments.
4. `GodMoveCachedMachineDiscovery` caches the new Boolean wire row and inserts
   it once per successful round. It charges residual-matrix construction even
   on the final unsuccessful round.
5. `GodMoveCachedSelection` materializes all supplied samples' wire values
   and transposes them into stored columns. Its scan selects the same original
   wire indices as before, using the returned basis count to detect acceptance.
6. The existing cached inverse builds the weights. The wrapper stores the
   resulting dimension with the descriptor, so obtaining its array type does
   not invoke discovery again.

`construct_value` proves equality with the previous descriptor, including its
sample data, wire indices, computed weights and query count. The numerical
changes therefore preserve the existing computed-wire projection exactly.
The range is still the wire span; no derivative closure is introduced.

Circuit traces are cached within each phase. Discovery insertion, column-table
construction and inverse sample-table construction still use separate passes
over the samples.

## Proved operation counts

Let `s` be circuit gate count, `r` the discovered sample count, and `k` the
current orthogonal basis count. The existing correctness theorems give
`k ≤ s` and `r ≤ s`. The counters instrument the executed rational operations.

| Stage | Proved rational-operation bound |
| --- | --- |
| One basis insertion | Exactly `k*(4*s+1)+3*s`, at most `8*(s+1)^2` |
| One residual matrix | Exactly `k*s+s^2*(2*k+1)`, at most `4*(s+1)^3` |
| All discovery basis and residual work | At most `16*(s+1)^4` |
| Original-column selection | At most `8*s*(r+1)^2` |
| Inverse weights | At most `8*r^3` |
| Combined counted construction stages | At most `32*(s+1)^4` |

The final bound is `construct_basis_operations_le`. It excludes coefficient
clearing, query-circuit compilation, SAT execution, Boolean circuit evaluation,
comparisons, allocation, indexing and the internal integer work of rational
primitives. It is not a total runtime theorem.

## Every actual SAT call is accounted for

`GodMoveDiscoveryClockTrace` instruments the original witness descent,
coordinate scan and adaptive discovery. It records each emitted Boolean input
word, including prefix-specialized queries and early termination. Its erasure
theorems recover the original samples and exact query count. Under
`Decides M SATLang T`, every recorded word has a machine configuration halted
by its corresponding supplied clock.

`GodMoveDiscoveryClockBudget` derives a size bound for every recorded word
from the actual sampled-state precision invariant. For

`T(m) ≤ C*(m+1)^d`,

it proves

`sum_{w in emittedWords} T(w.length)
  ≤ (C*500000000^d)*(n+s+1)^(16*d+3)`,

where `n` is input arity. This is the sum evaluated at the particular words
actually emitted, not a maximum-clock hypothesis. The constant is a
conservative consequence of the explicit query encoding bounds.

`GodMoveCachedDiscoveryTrace` then instruments the stored residual matrix and
cached insertion directly. It proves equality of the entire ordered query log
with the original trace by following each adaptive branch. Equal outputs and
call counts alone would not justify that claim. `searchClock_le_polynomial`
transfers the bound to the cached algorithm's own query log.

This bounds the SAT-machine clock component. The host work constructing and
interpreting those calls remains separate.

## What still prevents the requested conclusion

A complete bit-runtime theorem must account for coefficient clearing and
serialization, Boolean query construction and execution, data handling and
rational/integer primitives. It must also link precision bounds to every new
discovery and selection intermediate. The earlier theorem for all intermediate
values in the inverse kernel does not automatically cover these other loops.

The SAT rank investigation found no valid replacement for the missing joint
derivative-span argument. Deterministic simulation and circuit gluing bound
particular wire, snapshot or interface spaces. They do not put all labelled
derivative rows into those spaces. Even the easy product `∏ᵢ Xᵢ` has response
rank one across each fixed variable cut and order-`k` derivative rank
`choose(s,k)`. Efficient access to each row therefore does not bound their
joint rank.

SAT self-reduction does not directly repair this: Boolean OR arithmetizes as
`p+q-p*q`, introducing product spans, and conditioning a formula variable is
different from differentiating arbitrary bits of its encoded input. The
remaining SAT-restricted upper bound must use additional consequences of
global SAT correctness and uniformly polynomial computation. Its existing
equivalence with `SAT_not_in_P` is not a proof of either proposition.

## Validation

The complete focused audit passed under Lean 4.28.0:

- 133 audit modules;
- 1,057 printed axiom checks;
- 552 files in the checked source closure;
- zero focused warnings;
- only `propext`, `Classical.choice` and `Quot.sound` in the axiom reports.

Every source predates its final log. The new Lean files contain no `sorry`,
`admit`, custom axioms or `native_decide`.

Reproduction:

```sh
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py \
  --dependency-checkout /home/darre/pall-lean \
  --log-dir /home/darre/godmove-audit-20260911/cached-discovery-clock-checks
```

The local result record is
`/home/darre/godmove-audit-20260911/cached-discovery-clock-checks/results.json`.
