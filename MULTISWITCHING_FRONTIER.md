# Multi-switching frontier (2026-08-21)

This ledger records only the current machine-checked state of the common-tree route.  It is a
restricted-circuit counting project, not a proof of `P ≠ NP`.

## Verified reconstruction progress

Affected Lean modules:

- `ComputationalDepthMultiSwitchingCommonTree.lean`
- `ComputationalDepthMultiSwitchingWitnessLabel.lean`
- `ComputationalDepthMultiSwitchingCommonShallow.lean`
- `ComputationalDepthMultiSwitchingCompactLabelCounterexample.lean`
- `ComputationalDepthMultiSwitchingResidualFuelCounterexample.lean`
- `ComputationalDepthMultiSwitchingFuelSafeTerminal.lean`

The normalized common path now has an explicit endpoint

```text
pathEndpoint σ t x = fixOn σ (pathVars σ t x) x.
```

`freeOn_pathEndpoint` proves that re-freeing exactly `pathVars` recovers the root.  Hence endpoint
equality plus equality of `pathVars` is injective (`pathEndpoint_inj_of_pathVars_eq`).

For canonical DNF families, the globally fresh tagged witness stream decodes to exactly
`pathVars`, and its length is exactly the normalized shared transcript length
(`freshTaggedWitSeq_length_eq_trace_readOnce`).  The corrected literal-position and `(gate,term)`
codes therefore reconstruct the complete fresh stream and discharge endpoint injectivity.

The densest completed count is `canonicalCommonBadPath_count`.  A smaller sparse encoder is also
complete:

```text
SparseCommonBadPathLabel cardinality
  = ((d+1) * 2^d) * (w+1)^d * (G*m+1)^d.

|Bad| ≤ |Short| * ((d+1) * 2^d) * (w+1)^d * (G*m+1)^d.
```

The second inequality is `sparseCanonicalCommonBadPath_count`; it has no reconstruction or
injectivity hypothesis.  Its only combinatorial input is that every bad root's normalized endpoint
belongs to `Short` (plus the explicit width, term-count, extension, and depth bounds).

The full-path encoder is not the correct object for a bad path whose normalized trace can be longer
than the target depth `d`.  The new prefix endpoint API treats the first `d` fresh common queries:

- `prefixVars_card_eq_of_le_trace` proves that a trace of length at least `d` selects exactly `d`
  distinct variables;
- `prefixVars_subset_freeVars` and `stars_prefixEndpoint` prove that fixing them from a `K`-star root
  lands in the exact `K-d` shell;
- `freeOn_prefixEndpoint` and `prefixEndpoint_inj_of_prefixVars_eq` recover the root from the prefix
  endpoint and its selected variable set.

`commonShallowBad_card_le_of_prefix_encoder` packages these facts with the sparse label cardinality.
Its only encoder-specific premise is equality of the first-`d` prefix-variable sets under label
equality.  In particular, it does not assume that the entire bad path has length exactly `d`.

The prefix-order seam has now been bypassed without assuming an unproved ordering equivalence.
`freshTaggedPrefixVars` selects the variables decoded by the first `d` globally fresh tagged
witnesses.  For every normalized trace of length at least `d`, Lean proves that this set:

- has cardinality exactly `d` (`freshTaggedPrefixVars_card_eq_of_le_trace`);
- is contained in the root's live variables;
- produces an exact `K-d` endpoint and recovers the root when re-freed.

The optional position and `(gate,term)` streams reconstruct those first `d` tagged entries even
when the full path is longer (`freshTaggedWitSeq_take_eq_of_sparseCodes`).  Consequently
`sparseCanonicalCommonLongPath_count` and
`commonShallowBad_card_le_of_sparse_prefix` are concrete injective counts: there is no residual
label-reconstruction or prefix-variable-equality premise.

The semantic failure event now has a concrete witness extraction.  The canonical
`prefixEndpoints` tree preserves the root restriction and is a valid `CommonShallowAt` certificate
whenever all reached residual gates are shallow (`commonShallowAt_of_prefix_residual`).  Therefore a
failure supplies an extending assignment and a gate that is still too deep at its reached prefix
restriction (`exists_deep_prefix_residual_of_not_commonShallowAt`).  `commonShallowBadAssignment`
chooses these witnesses uniformly, and `commonShallowBad_card_le_of_semantic_sparse_prefix` reduces
the count to the single question of whether this chosen execution has at least `d` fresh queries.

All printed axiom sets for these capstones are subsets of
`{propext, Classical.choice, Quot.sound}`.  There is no `sorry`, `admit`, custom axiom, or
`native_decide` in the affected modules.

## Falsification retained

`ComputationalDepthMultiSwitchingCompactLabelCounterexample.lean` proves, by kernel reduction, that
endpoint + bit transcript + gate-run counts + raw per-term multiplicities do **not** determine the
queried variable set.  The one-term DNF `¬x₀ ∧ ¬x₁` gives two distinct roots with identical old
boundary data and endpoint but different `pathVars`.  This refutes the position-free compact-label
route; the literal-position stream is necessary for the present canonical reconstruction.

`ComputationalDepthMultiSwitchingResidualFuelCounterexample.lean` falsifies the tempting next
inference “a deep rebuilt residual after a budget-`d` prefix implies a length-`d` common trace.”  For
the DNF `x₀ ∧ x₁` with fuel one and budget two, the family tree asks only `x₀` before its recursive
fuel reaches zero, but rebuilding the residual with the original fuel asks `x₁` and has positive
depth.  Thus the current same-fuel residual semantics can stop early for fuel exhaustion, not only
because the gate is semantically resolved.

The ample-fuel repair is now verified for the full sequential family in
`ComputationalDepthMultiSwitchingFuelSafeTerminal.lean`.  `canonicalEnd` follows the exact canonical
binary execution and equals its normalized `CommonTree.pathEndpoint`.  If `stars σ ≤ fuel`, Lean
proves that the reached state is semantically terminal, so rebuilding the gate with *any* fuel has
depth zero.  Lean also proves that every member gate's normalized path-variable set is contained in
the full family set, hence the family endpoint extends every member endpoint, and that semantic
terminality is monotone under restriction extension.  The capstone
`canonicalFamily_deep_prefix_implies_long_trace` therefore proves that a positive-depth member
residual after a budget-`d` family prefix forces a normalized common trace of length at least `d`.
On the exact `K` shell, `commonShallowBadAssignment_long_of_le_fuel` discharges the former semantic
long-path premise from `K ≤ fuel`; consequently
`commonShallowBad_card_le_of_ample_fuel_sparse_prefix` gives the concrete sparse bad-event count
without an assumed encoder-side long-path hypothesis.  The retained counterexample violates
precisely the new hypothesis (`stars root = 2` but `fuel = 1`).

## Exact remaining frontier

The current sparse count is an honest finite counting theorem, but it is not yet the quantitative
multi-switching lemma:

1. The factor `(G*m+1)^d` pays for a gate/term identity at every fresh query.  A sharp
   multi-switching encoder must amortize this to run/block information (roughly one family choice per
   residual-depth block), rather than one arbitrary key per query.
2. The shorter-shell count now yields a positive proportional shell contraction, but not yet with
   trunk parameters strong enough for iteration.  The exact shell identity
   `card_stars_eq`, namely `C(n,K) * 2^(n-K)`, is now proved, and
   `commonShallowShellContraction_of_sparse_balance` reduces positive contraction to one explicit
   natural-number binomial/power inequality only in the genuinely nontrivial regime
   `trunkDepth K < K`.  `commonShallowBad_card_eq_zero_of_le_trunk` proves that the bad event is empty
   for `K ≤ trunkDepth K` under ample fuel.  The balance is now discharged by
   `sparsePrefix_balance_of_density` whenever
   `(16*(w+1)*(G*m+1))*K + K ≤ n+1` and the saving exponent fits inside the trunk.
   `commonShallowShellContraction_densityAdaptive` consequently gives a verified uniform saving of
   `2^floor(K/2)`: it uses trunk depth `K/2` in the sparse regime and the full depth `K` otherwise.
   The dense-shell full-depth branch is deliberately recorded as quantitatively trivial, not a
   useful shallow-trunk iteration theorem.
3. Only after these steps can the restriction iteration be tested against the required `AC⁰` depth
   reduction parameters.  No unrestricted P-time/SAT consequence follows from the present result.

The next defensible route is therefore a block/run sparse encoder with a proved decoding theorem,
aimed at reducing the `G*m` density penalty enough to replace the adaptive full-depth branch by a
uniformly shallow trunk.  If the proposed block data collide, the collision must be retained as
another concrete counterexample rather than hidden behind an injectivity premise.
