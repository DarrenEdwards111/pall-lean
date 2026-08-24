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

The key word is now compressed further.  `freshTaggedWitSeq_keys_pairwise` shows that the global
fresh key stream is lexicographically block-monotone.  Therefore the first `d` keys are uniquely
determined by their `(gate,term)` multiplicities; `freshPrefixKeys_eq_of_termCounts_eq` and
`freshTaggedWitSeq_take_eq_of_prefixCounts` prove this reconstruction.  The selected-prefix
endpoint already stores the fixed values, so no branch transcript is needed.  The resulting label
has exact cardinality

```text
(w+1)^d * ((d+1)^m)^G,
```

and `commonShallowBad_card_le_of_ample_fuel_prefix_counts` proves the corresponding ample-fuel
bad-shell bound.  This is a parameter trade rather than a uniform domination of the earlier sparse
label: it removes the per-query key alphabet and transcript, but retains a dense `G*m` count table.
`commonShallowBad_card_le_of_ample_fuel_hybrid_prefix` takes the minimum of the old and new exact
factors, so the exposed capstone is uniformly no weaker than either encoder separately.

The dense count table has now also been replaced by an exact realized-prefix multiset.  The first
`d` finite keys form `Sym (Fin G × Fin m) d`; equality of these multisets gives a permutation, and
block monotonicity upgrades that permutation to equality of the ordered key prefixes.  The optional
`Sym` code is total even on short non-bad paths and has exact stars-and-bars factor

```text
choose(G*m + d - 1, d) + 1.
```

Thus `commonShallowBad_card_le_of_ample_fuel_prefix_sym` proves the label bound
`(w+1)^d * (choose(G*m+d-1,d)+1)`, while
`commonShallowBad_card_le_of_ample_fuel_realized_hybrid` exposes the minimum of all three verified
encoders.

The first shell-balance audit of this exact factor is now complete.  A `d`-multiset over an
`A`-letter alphabet is a quotient of the `A^d` words, and for `d>0` the optional total code obeys

```text
choose(A+d-1,d)+1 ≤ (A+1)^d.
```

After including the lower-shell `2^d` and a requested saving `2^e` with `e≤d`, the complete
realized-prefix factor is at most

```text
(4*(w+1)*(G*m+1))^d.
```

Consequently `commonShallowBad_scaled_le_of_realized_density` proves the one-shell contraction
whenever `d>0`, `d≤K≤n`, `K≤fuel`, `e≤d`, and
`(4*(w+1)*(G*m+1))*K+K≤n+1`.  This improves the corresponding verified sparse-label density base
from `16*(w+1)*(G*m+1)` to `4*(w+1)*(G*m+1)`; it does not remove its linear dependence on `G*m`.

Testing that dependence against the repository's concrete growing-family scale changes the
assessment.  `commonShallowBad_scaled_le_linearGap_realized` instantiates

```text
n = 1000*(G*m)*r,  K = 20*r,  d = 10*r,  w = 2
```

and proves a `2^(10*r)` one-shell saving for every positive `G,m,r` (with `20*r ≤ fuel`).  The
linear `G*m` label cost is absorbed by the same linear `G*m` growth in `n`; the trunk remains exactly
half the shell independently of `G`.  Thus the factorial saving is not the next blocker for this
specific linear-gap regime, although it may matter at smaller ambient-density constants.

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

1. Both the per-query `(G*m+1)^d` word and dense `(d+1)^(G*m)` count table now have a
   realized-prefix alternative with exact factor `choose(G*m+d-1,d)+1`.  The quotient-of-words audit
   proves that it fits shell balance with density base `4*(w+1)*(G*m+1)`, a factor-four improvement
   over the prior sparse route.  The concrete linear-gap substitution shows that its `G*m`
   dependence is not itself an obstruction when `n=1000*(G*m)*r`: a half-shell trunk gives a
   `2^(10*r)` saving uniformly in positive `G,m`.  A factorial refinement is therefore deferred
   unless a later iteration requires a substantially smaller ambient-density constant.
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

The intended growing-`G` test now succeeds without exposing the factorial: at the verified
linear-gap scale the realized-prefix count supports a uniform half-shell trunk.  The next
defensible route is to compose this one-shell common-shallow contraction with the actual layered
depth-reduction round and check whether its residual-depth and fuel interfaces iterate at those
parameters.

The first interface audit is now formalized.  `stars_le_of_restrictionExtends` proves that a leaf
restriction cannot have more live variables than its root, and
`CommonShallowAt.leaf_stars_le_fuel` packages the consequence that `stars σ ≤ fuel` remains true at
every common-trunk leaf.  Thus the ample-fuel hypothesis is stable under the leaf transition and is
not an iteration blocker.

The residual-depth bridge is now formalized in
`ComputationalDepthMultiSwitchingLayeredBridge.lean`.  `CoversLayeredBottoms gates C` isolates the
necessary compatibility condition: the common family enumerates both `cs` and `negDNF cs` for every
bottom gate of the current layered circuit.  At each reached trunk leaf,
`CommonShallowAt.leaf_shallows` converts the residual `depth ≤ s` bounds into the existing
root-local `Shallows fuel leaf (s+1) C` interface.  The capstone
`CommonShallowAt.leaf_collapseRound_altO` then pays the trunk depth separately, preserves the leaf
fuel bound, proves subcube equivalence, gives output `BottomWidth (s+1)`, and reduces
`AltO (k+3)` to `AltO (k+2)`.  Thus no new collapse transformation is needed.

The finite indexing and first structural recurrence are now formalized in the same bridge file.
`layeredBottomFamilyList C` is the syntactic list `bottomGates C ++ map negDNF (bottomGates C)`, and
`layeredBottomFamily C` indexes it by `Fin`.  The proved length equation is exact:
`G = 2 * (bottomGates C).length`; `layeredBottomFamily_covers` discharges the former abstract
coverage premise.  Circuit-level bottom width and clause-count bounds transfer to the indexed
family without loss.  The specialized
`layered_commonShallowBad_scaled_le_of_realized_density` consequently exposes the shell density
charge with this exact `G`, rather than an unrelated family parameter.

The reached-leaf recurrence is also explicit.  If the current circuit has at most `M` bottom gates
and the common switching residual depth is `s`,
`CommonShallowAt.leaf_collapseRound_family_bounds` proves that the collapsed circuit still has at
most `M` bottom gates and has bottom clause count at most `M * 2^(s+1)`.  Therefore the next exact
two-polarity switching family has `G_next ≤ 2*M`, while its available uniform term bound is
`m_next = M*2^(s+1)`.  In the realized-prefix density base the product can thus be charged as large
as `G_next*m_next ≤ 2*M^2*2^(s+1)`: gate-family count itself is stable, but the syntactic
gate-key/term-key product has a quadratic `M` charge and an exponential residual-depth charge.

The duplicate-clause interface gap is now closed.  The reusable normalization proof has been moved
to `ComputationalDepthMultiSwitchingNormalize.lean`: order-preserving `eraseDups` preserves
membership, first-active-term selection, and the complete `canonicalDT` at every fuel and
restriction.  In the layered bridge, `normalizedLayeredBottomFamily C` erases duplicates inside
both polarities while retaining the same `Fin (2 * bottomGateCount)` index type.  Its gates are
unconditionally `Nodup`; circuit width and clause-count bounds transfer without loss.

`CoversLayeredBottoms` now records equality of canonical trees rather than syntactic clause-list
equality.  This is the exact invariant consumed by `leaf_shallows`, and it lets the normalized
family drive the unchanged `collapseRound` on the original circuit.  The proved equivalence
`commonShallowAt_normalizedLayeredBottomFamily_iff` shows that normalization changes neither the
common trunk nor any residual-depth event.  Finally,
`normalizedLayered_commonShallowBad_scaled_le_of_realized_density` specializes the realized-prefix
shell contraction to the normalized circuit family with no extra duplicate-clause hypothesis.
Thus `BottomClean` need not be strengthened, and normalization does not worsen the audited
recurrence: `G_next ≤ 2*M`, `m_next ≤ M*2^(s+1)`, and hence
`G_next*m_next ≤ 2*M^2*2^(s+1)` remain the available bounds.

The round-dependent survivor audit is now instantiated.  Write

`A = 2*M^2*2^(s+1)` and `B = 100*(s+2)*(A+1)`.

At level `j`, `layeredRoundLive` supplies
`N_j = 2000*(s+2)*(A+1)*(r*B^j)` live variables and `layeredRoundShell` retains
`K_j = 20*(r*B^j)`.  `layeredRoundShell_succ_eq_live` proves the exact localization interface
`K_(j+1) = N_j`, so these are genuinely consecutive subcubes rather than independent shell
estimates.  `layeredRound_density` proves that every key product `G*m ≤ A` satisfies the required
density premise at every level.  The circuit capstone
`normalizedLayered_commonShallowBad_scaled_le_schedule` then gives a half-shell trunk and
`2^(10*r*B^j)` contraction at each normalized round, with no duplicate-clause assumption.

This succeeds for every prescribed finite number of rounds when `M` and `s` are external
parameters, but the audit also exposes a decisive limitation: the starting live budget grows
geometrically with a base containing `M^2`.  The proved counter-bound
`not_layeredRound_worstCase_density_of_live_le_gateBound` says that if the ambient live dimension
`N` is already at most the gate bound `M`, then the worst-case-cap density premise is false for
every nonempty survivor shell.  Thus this recurrence does not self-close for the standard regime
where `M` grows linearly or faster with `N`; increasing the constant `2000` or retaining only a
larger constant cannot repair that self-reference.  The counter-bound applies to the present
power-base density theorem; it does not rule out a new argument that retains the exact factorial.

The precise next frontier is to reduce the quadratic syntactic key charge before another schedule
attempt: exploit sharing or realized active bottom gates so the encoder pays substantially less
than `(2*M)*(M*2^(s+1))`, or prove a matching obstruction for any encoder that records independent
gate and term indices.  In parallel, an exact-factorial density theorem is the remaining defensible
way to test whether quotient savings can overcome the `M^2` self-reference without changing the
encoder.
Any proposed run-data collision must be retained as another concrete counterexample rather than
hidden behind an injectivity premise.  No unrestricted P-time/SAT consequence follows from this
audit.

### Exact-factorial arithmetic gate and depth-one obstruction

The quotient saving can now be tested without passing through the power-base density theorem.
`commonShallowBad_scaled_le_of_realized_balance` accepts the exact shell inequality containing
`choose(G*m+d-1,d)+1` and transfers it directly to the scaled bad-set bound.  Thus future schedule
tests no longer need to discard the factorial before reaching the semantic common-shallow event.

The first exact test is negative.  `not_realizedPrefix_exact_balance_one_of_live_le_keys` proves
that at `K=d=1` with one bit of requested saving, the unrelaxed stars-and-bars inequality itself
forces `4*(w+1)*(A+1) ≤ n`, where `A` is the realized key alphabet.  Consequently it is false as
soon as `0<n≤A`.  This obstruction occurs before `prefixSymCode_le_pow` and therefore cannot be
blamed on the quotient-to-word relaxation.  It rules out using the factorial alone to obtain a
uniform all-shell contraction in the self-referential key regime.

The scheduled proportional-depth test is now negative in the same self-referential regime.
`not_realizedPrefix_exact_balance_half_of_live_le_keys` treats every positive `r` with
`K = 2*r`, `d = r`, saving exponent `r`, and nonempty shell `2*r ≤ n`.  It proves that the exact
balance is impossible whenever `n ≤ A`.  Equivalently, the exact balance itself has the necessary
ambient condition `A < n`.

This conclusion uses the two binomial factors directly.  Monotonicity gives
`choose(A+r-1,r) ≥ choose(n,r)` when `n ≤ A`, and `Nat.choose_mul` gives
`choose(n,2r) ≤ choose(n,r)^2`; meanwhile the shell shift and requested saving contribute the
strict factor `2^(2*r)`.  Thus the contradiction occurs before `prefixSymCode_le_pow`, for every
nonempty proportional half-shell rather than only at depth one.

For the audited circuit recurrence `A = 2*M^2*2^(s+1)`, the exact factorial therefore cannot
overcome the `M²` self-reference when the live dimension is at most that key charge.  The precise
next frontier is structural: reduce the encoder alphabet below the ambient live dimension by
charging only realized active gates/terms or by sharing term indices, then reconnect that smaller
alphabet to the normalized layered-family count.  Any attempted sharing encoder must retain and
resolve concrete run-data collisions.  No P-versus-NP conclusion follows from this audit.

### Ragged-family encoder and total-clause recurrence

The rectangular key charge has now been removed at the encoder level.  `ActualFamilyKey gates` is
the dependent sum `Σ g : Fin G, Fin (gates g).length`, so its cardinality is exactly
`Σ_g |gates g|`.  The proved ragged-family multiset code retains the gate coordinate and genuine
term position, hence it preserves the existing block-monotone reconstruction and does not assume
away the compact-label collision.  `prefixActualSymCanonicalCommonLongPath_count` and
`commonShallowBad_card_le_of_ample_fuel_prefix_actual_sym` replace
`choose(G*m+d-1,d)+1` by

`choose((Σ_g |gates g|)+d-1,d)+1`.

The circuit recurrence supplies a matching structural bound.  The new `bottomClauseCount` is the
sum of all bottom-gate clause-list lengths.  `mergePass_bottomClauseCount` proves exact conservation
through every merge, including the uniform sibling flattening cases, and
`collapseRound_bottomClauseCount_le` proves

`bottomClauseCount(collapseRound) ≤ M * 2^s`

from at most `M` input bottom gates and residual shallow depth `s`.  For the normalized
two-polarity family, `layeredBottomFamily_total_length` is exactly twice the unnormalized total and
`normalizedLayeredBottomFamily_total_length_le` can only decrease it.  Consequently
`CommonShallowAt.leaf_collapseRound_actualAlphabet_bound` gives the next encoder alphabet bound

`A_next ≤ 2 * M * 2^(s+1)`.

This removes one full factor of `M` from the previously audited
`2*M^2*2^(s+1)` recurrence without relying on duplicate gates or shared clauses.  It does not by
itself prove a shell contraction: the existing exact-balance and density capstones still take the
rectangular parameter `G*m`.

The precise next frontier is to lift the exact-balance/scaled-bad-set theorem to the ragged alphabet
parameter `A = Σ_g |gates g|`, specialize it to the normalized layered family, and rerun the
half-shell self-reference audit with the new linear cap `2*M*2^(s+1)`.  If the ambient live
dimension can still be at most this cap, the already proved necessary condition `A < n` remains
the exact obstruction; otherwise this is the first defensible route to a composable schedule.
The concrete compact-label collision remains in force.  No P-versus-NP conclusion follows.

### Ragged half-shell recurrence audit

The exact alphabet is now connected through the arithmetic and circuit interfaces.
`realizedPrefix_balance_of_actual_density` states the stars-and-bars balance directly for an
arbitrary alphabet cardinality `A`, and `commonShallowBad_scaled_le_of_actual_balance` plus
`commonShallowBad_scaled_le_of_actual_density` transfer the exact ragged-family count to the scaled
bad-set bound.  No uniform per-gate term bound occurs in these statements.

`normalizedLayered_commonShallowBad_scaled_le_of_actual_density` specializes the result to the
normalized two-polarity family.  The new schedule uses

`layeredRoundActualKeyCap M s = 2*M*2^(s+1)`

and `normalizedLayered_commonShallowBad_scaled_le_actual_schedule` proves a half-shell contraction
at every level whenever the current normalized alphabet is below this cap.
`layeredRoundActualShell_succ_eq_live` proves consecutive levels compose exactly, and
`CommonShallowAt.leaf_collapseRound_actualAlphabet_bound` now concludes directly with the same cap,
so the structural output of one round matches the counting input of the next.

The linear improvement is real but does not remove the worst-case self-reference obstruction.
`not_layeredRoundActual_worstCase_density_of_live_le_gateBound` proves that for every nonempty
survivor shell the density premise is false whenever the ambient live dimension `N` is at most the
bottom-gate bound `M`.  Thus the quadratic `M²` charge was not the only blocker: even the exact
ragged alphabet can be at least the live dimension in the unrestricted worst case.

The precise next frontier is structural control of `M` (or of the actual total clause occurrences)
relative to the survivor dimension across the input circuit class.  A useful next test is to derive
the strongest size-sensitive invariant available from the surrounding ACC0 assumptions and check
whether it keeps `2*M*2^(s+1) = o(N)` throughout all prescribed depth-reduction rounds.  Without
such an invariant, another alphabet-only refinement cannot make the present density schedule
self-closing.  The compact-label collision remains preserved, and no P-versus-NP conclusion follows.

### Polynomial-size cap audit

The surrounding layered iteration does not currently derive its bottom-gate cap from an ACC0
syntax-size hypothesis: it takes `(bottomGates C).length ≤ M` as an external invariant.  The strongest
generic class-level information suggested by "polynomial size" is therefore a cap of the form
`M = N^c`, not a sublinear estimate on the actual bottom layer.

Two arithmetic consequences are now explicit in the layered bridge.
`layeredRoundActual_gateBound_lt_live_of_density` proves that every nonempty shell satisfying the
linear-cap density premise must have `M < N`.  Its specialization
`not_layeredRoundActual_worstCase_density_of_polynomial_gateCap` proves that a positive-degree
polynomial cap `M = N^c`, `c > 0`, makes the premise false for every `N > 0` and `K > 0`, since
`N ≤ N^c`.  Thus a polynomial-size upper bound alone cannot uniformly instantiate the ragged
schedule, even though individual circuits within that class may have much smaller actual bottom
layers.

The precise next frontier is a structural sparsification or active-occurrence theorem that applies
to every circuit in scope and yields an actual roundwise cap strictly below the live dimension
(quantitatively, enough to absorb the additional `2^(s+1)` and density constants).  Before such a
theorem exists, wiring the generic ACC0 tree-size bound into `M` only reproduces the proved
self-reference obstruction.  No P-versus-NP conclusion follows from this audit.

### Active-occurrence invariant audit

The recurrence can now be stated without an external bottom-gate cap.  Raw
`bottomClauseCount` is not sufficient for this purpose: the layered syntax permits empty `dnf []`
and `cnf []` bottom gates, and `NonEmptyGates` only constrains internal child lists.  The new
`bottomSlotCount` therefore sums `max 1 |cs|` over bottom gates, charging actual clause occurrences
while retaining one necessary slot for each empty constant gate.

`bottomGates_length_le_bottomSlotCount` and `bottomClauseCount_le_bottomSlotCount` prove that this
single measure controls both syntactic gates and raw occurrences.  Consequently
`collapseRound_bottomClauseCount_le_bottomSlotCount` replaces the external premise
`bottomGates.length ≤ M` by the circuit's own slot count, and
`CommonShallowAt.leaf_collapseRound_slotAlphabet_bound` proves the exact next normalized alphabet
bound

`A_next ≤ 2 * bottomSlotCount(C) * 2^(s+1)`.

This is the strongest currently verified active-occurrence recurrence that treats constant gates
soundly.  It removes the API-level external invariant, but not the quantitative obstruction:
`layeredRoundActual_bottomSlotCount_lt_live_of_density` proves that the existing density schedule
still requires `bottomSlotCount(C) < N` on every nonempty round.  A generic positive-degree
polynomial syntax-size bound does not imply this sublinear condition.

The precise next frontier is therefore a semantic sparsification theorem that reduces
`bottomSlotCount` below the live dimension while preserving the restricted circuit, or a new
counting argument whose density premise tolerates linear-or-larger slot count.  Purely replacing
the external gate cap by exact syntactic occurrences is now proved insufficient.  Empty-gate
counterexamples remain explicitly charged, and no P-versus-NP conclusion follows.

### Exact slot-margin audit

The qualitative requirement `bottomSlotCount(C) < N` understated the gap demanded by the present
density premise.  Expanding `layeredRoundActualKeyCap M s = 2*M*2^(s+1)` and using only `K ≥ 1`,
`layeredRoundActual_gateBound_margin_of_density` proves the necessary margin

`8 * (s+2) * M * 2^(s+1) + 4*(s+2) ≤ N`.

Its circuit-owned specialization `layeredRoundActual_bottomSlotCount_margin_of_density` removes the
external cap and gives

`8 * (s+2) * bottomSlotCount(C) * 2^(s+1) + 4*(s+2) ≤ N`.

Thus merely reducing active occurrences to some unspecified sublinear value is not a sufficient
round interface.  A semantic sparsification theorem intended for this schedule must preserve the
restricted circuit while reaching this residual-width-adjusted bound at every round.  Conversely,
a counting replacement must explicitly recover enough of the factor `8*(s+2)*2^(s+1)` if it is to
tolerate denser circuits.  The precise next frontier is to test whether restriction simplification
can establish this exact margin for the survivor circuits; if not, the counting argument rather
than syntactic accounting must change.  No P-versus-NP conclusion follows.

### Restriction/collapse slot-recurrence audit

The invariant consumed by the next round is now tracked through the actual restriction/collapse
pipeline.  `bottomSlotCount_le_bottomGates_length_add_bottomClauseCount` proves

`bottomSlotCount(C) ≤ bottomGates(C).length + bottomClauseCount(C)`.

Combining this with the proved post-collapse gate-count and total-clause bounds gives
`collapseRound_bottomSlotCount_le`: for a structurally nonempty layered circuit shallow to depth
`t`,

`bottomSlotCount(collapseRound F ρ C) ≤ bottomSlotCount(C) * (2^t + 1)`.

`CommonShallowAt.leaf_collapseRound_bottomSlotCount_bound` transports this exact recurrence through
the common trunk.  Since the layered bridge pays `t = s+1`, the roundwise bound available from the
current semantics is

`M_next ≤ M_current * (2^(s+1) + 1)`.

This answers the immediate test negatively at the level of verified guarantees: restriction,
canonical-tree compilation, and sibling merge preserve circuit semantics, but their present
structural analysis supplies a multiplicative expansion bound, not the residual-width-adjusted
contraction required by the next density margin.  This does not prove that every individual leaf
expands—constant propagation or semantic duplicate removal may shrink particular circuits—but no
such uniform shrinkage is currently established.

The precise next frontier is to define circuit-level constant propagation and semantic duplicate
elimination after `collapseRound`, prove `EquivOn` and the layered invariants, and determine whether
their *actual* slot count contracts by the needed factor on every survivor leaf.  If a preserved
counterexample blocks that uniform contraction, the encoder/counting density must change rather
than relying on the existing restriction simplification.  No P-versus-NP conclusion follows.

### Semantic slot-contraction barrier

The proposed uniform-cleanup route is now blocked by a proved minimal counterexample, independently
of the implementation details of constant propagation.  `bottomGates_nil_eval_eq` and
`bottomSlotCount_zero_eval_eq` show that every layered circuit with zero bottom slots computes a
constant function.  Therefore `equivOn_singleLiteral_bottomSlotCount_pos` proves that every circuit
equivalent, on the fully live subcube, to the one-term DNF containing one positive literal has
positive slot count.

The capstone `singleLiteral_no_equivOn_bottomSlotCount_lt` packages the exact obstruction: the source
circuit has slot count one, and no `EquivOn` replacement has strictly smaller slot count.  Thus even
an ideal semantic duplicate eliminator and constant propagator cannot supply a uniform strict
contraction theorem for every survivor circuit.  This does not exclude useful cleanup on larger or
partially resolved circuits, but it rules out using per-circuit strict slot contraction as the
roundwise invariant required by the current density schedule.

The precise next frontier is to replace that invariant by an aggregate or excess-slot potential
that permits irreducible one-slot components, and test whether restriction gives enough expected or
shellwise decrease to absorb the factor `8*(s+2)*2^(s+1)`.  If no such amortized decrease is
available, the encoder/counting density itself must change.  No P-versus-NP conclusion follows.

### Semantic excess-potential baseline obstruction

The proposed excess route now has a cleanup-independent formal model.
`semanticBottomSlotCount ρ C` is the minimum bottom-slot count among every layered circuit
`EquivOn ρ` to `C`; `exists_equivOn_bottomSlotCount_eq_semantic` proves that this natural-number
minimum is attained, while `semanticBottomSlotCount_le` and
`le_semanticBottomSlotCount_of_forall` provide its upper- and lower-bound interfaces.  Thus the
potential already grants ideal constant propagation and semantic deduplication rather than
measuring a particular syntax cleanup.

Define `semanticSlotExcess ρ C = semanticBottomSlotCount ρ C - 1` and sum this over survivor
components.  The exact literal calculation is negative for using this potential alone:
`semanticBottomSlotCount_singleLiteral` proves that a live literal has semantic count exactly one,
so `aggregateSemanticSlotExcess_replicate_singleLiteral` gives zero excess for arbitrarily many
such components.  At the same time `sum_bottomSlotCount_replicate_singleLiteral` proves that their
raw encoder slot mass is exactly the number of components.  This is not an artifact of a weak
cleanup algorithm: the semantic minimization ranges over all equivalent layered circuits.

Consequently an aggregate excess term by itself cannot pay even the encoder's irreducible baseline
alphabet.  Any viable amortized invariant must separately charge the number (or probability mass)
of nonconstant survivor components, for example a baseline-plus-excess potential, and must then
prove restriction-driven decay of that combined quantity strong enough to absorb
`8*(s+2)*2^(s+1)`.  The precise next frontier is to define that combined shellwise potential and
connect its baseline component count to the common-trunk leaf distribution; if the baseline mass
does not contract, the encoder/counting density must change.  No P-versus-NP conclusion follows.

### Baseline-plus-excess trunk audit

The proposed combined potential is now defined and its exact content is formalized.
`semanticSlotBaseline ρ C = min 1 (semanticBottomSlotCount ρ C)` charges one precisely for a
semantically nonconstant component, and `semanticSlotBaseline_add_excess` proves pointwise that

`semanticSlotBaseline ρ C + semanticSlotExcess ρ C = semanticBottomSlotCount ρ C`.

Consequently `aggregateSemanticBaselineExcess_eq` identifies the aggregate combined potential
exactly with the sum of semantic minimum slot counts.  Baseline plus excess is therefore a useful
decomposition, but not a numerically smaller invariant.  The general monotonicity theorem
`semanticBottomSlotCount_anti_of_extends` proves that restriction can only decrease this ideal
potential.

The decrease is not automatic at a common-trunk leaf.  The live-literal obstruction has been
strengthened from the fully live cube to every restriction leaving its coordinate free:
`semanticBottomSlotCount_singleLiteral_of_free` gives semantic minimum exactly one whenever
`ρ i = none`.  At the actual canonical prefix interface,
`prefixEndpoint_replicate_singleLiteral_baseline_mass_of_not_mem` proves that if `i` is absent from
the followed prefix query path, then arbitrarily many replicated `i`-literal components retain
their full combined mass `q` at that leaf.

Thus baseline contraction must be paid for by querying an essential coordinate; merely passing to
a finer survivor restriction supplies only nonincrease.  The replicated example also exposes why
raw component count is too coarse: one query of a shared coordinate may discharge all `q` copies,
whereas omitting it discharges none.  The next defensible invariant must account for diversity of
essential live support, not only the number of syntactic or semantic components.

The precise next frontier is to define a distinct-essential-coordinate baseline, prove the sharp
`q - trunkDepth` survivor lower bound for `q` independent live literals along canonical prefix
leaves, and compare that pathwise bound with the required factor `8*(s+2)*2^(s+1)`.  If even
support-aware baseline mass cannot contract at that rate, the encoder/counting density must change.
No P-versus-NP conclusion follows.

### Distinct-essential-support contraction obstruction

The support-aware baseline and the proposed comparison are now formalized.
`distinctEssentialCoordinateBaseline ρ support` counts the distinct designated coordinates in
`support` that remain live under `ρ`; replicated components sharing a coordinate therefore incur
only one charge.  `independentLiveLiteralFamily` realizes this baseline by one positive-literal
component for each currently live support coordinate, and
`aggregateSemanticBaselineExcess_independentLiveLiteralFamily` proves that its aggregate semantic
baseline-plus-excess mass is exactly the distinct-support baseline.  The fixed-coordinate companion
theorem `semanticBottomSlotCount_singleLiteral_of_fixed` confirms that a queried literal has
semantic slot minimum zero, while a free literal has minimum one.

At a canonical prefix endpoint, `distinctEssentialCoordinateBaseline_prefixEndpoint` gives the
exact identity

`baseline(endpoint, support) = |support \ prefixVars|`

whenever the designated support was initially live.  Since `prefixVars` has cardinality at most the
trunk budget, `distinctEssentialCoordinateBaseline_prefixEndpoint_ge_sub` proves the sharp
pathwise lower bound

`|support| - trunkDepth ≤ baseline(endpoint, support)`.

The comparison with the required switching factor is negative in a broad regime.
`distinctEssentialCoordinateBaseline_no_switchingFactor_contraction` states the exact obstruction:
factor contraction is impossible whenever

`|support| < 8*(s+2)*2^(s+1) * (|support| - trunkDepth)`.

In particular,
`distinctEssentialCoordinateBaseline_no_switchingFactor_contraction_of_twice_budget_lt` proves
that it is impossible on every canonical prefix leaf whenever `2*trunkDepth < |support|`.  Thus
even after quotienting replicated components by shared coordinates, a shallow trunk removes only
an additive number of independent baseline charges, whereas the present iteration asks for a
large multiplicative reduction.  This preserves the replicated-coordinate example as a useful
case where support-aware accounting helps, while showing that independent support remains a
genuine obstruction.

The precise next frontier is to extract a circuit-owned essential-support set for arbitrary
survivor families and determine whether the encoder's irreducible alphabet can be bounded by this
distinct-support term plus semantic excess.  If that bridge includes independent-literal families,
the verified obstruction rules out the current uniform multiplicative schedule and the
encoder/counting density or trunk schedule must change.  No P-versus-NP conclusion follows.

### Support-plus-excess alphabet bridge fails before support extraction

The proposed alphabet comparison is false even if the support charge is enlarged to include every
ambient coordinate.  `semanticSlotExcess_singleClause` first proves that an arbitrary one-clause
DNF has semantic excess zero under every restriction: its original one-slot representation already
bounds the semantic minimum by one.

`permutedThreeLiteralGates` is then a concrete family of six singleton gates, one for each ordering
of the same three positive literals.  `permutedThreeLiteralGates_clean` verifies both encoder-side
cleanliness conditions: every gate list is duplicate-free and every clause has distinct literal
variables.  Pointwise `eraseDups` therefore leaves the family unchanged.  The exact realized key
mass is six, while `permutedThreeLiteralSurvivors_semanticExcess` proves aggregate semantic excess
zero.  Since the entire ambient support `univ : Finset (Fin 3)` has cardinality three,
`permutedThreeLiteral_no_alphabet_le_support_add_semanticExcess` proves the strict counterexample

`3 + 0 < 6`.

Thus extracting a sharper circuit-owned essential set cannot establish the requested raw-alphabet
upper bound: it would only reduce the support side.  The failure comes from semantic replicas
across indexed gates (here merely literal-order permutations), which pointwise clause deduplication
does not identify.  This counterexample is compatible with `BottomClean` and is retained as a
normalization requirement, not dismissed as malformed syntax.

The precise next frontier is to test a stronger, coverage-preserving quotient: canonicalize literal
order inside clauses and deduplicate semantically identical canonical trees across the whole indexed
family, then determine whether the quotient alphabet is controlled by distinct live support plus
semantic excess.  Independently, the already proved independent-literal obstruction means that even
a successful quotient bound would still require changing the uniform multiplicative counting
density or paying a trunk depth comparable to independent support.  No P-versus-NP conclusion
follows.

### Literal-order quotient fails the current coverage interfaces

The proposed whole-family quotient cannot be inserted into the existing layered bridge merely by
sorting literals and weakening the notion of coverage.  `orderedThreeLiteral_dnfEval_eq` proves
that the singleton clauses `x₀ ∧ x₁ ∧ x₂` and `x₁ ∧ x₀ ∧ x₂` compute the same Boolean
function.  Nevertheless `orderedThreeLiteral_canonicalDT_ne` proves that their canonical trees are
already unequal at fuel one on the fully live cube: they query different root variables.
`orderedThreeLiteral_no_common_exactTree_representative` packages the interface consequence: no
single gate can retain exact-tree coverage of both orders.  Thus deduplication by conjunction
semantics is incompatible with the present `CoversLayeredBottoms` contract.

Depth-only coverage is also insufficient in general.  The two-clause gates

`[(x₀ ∧ x₁), x₀]` and `[(x₁ ∧ x₀), x₀]`

are semantically equal by `depthSensitive_dnfEval_eq`, but
`depthSensitive_canonicalDT_depth_ne` proves that at fuel two on the live cube their canonical
depths differ (one versus two).  Querying `x₀` first immediately resolves the absorbed clause;
querying `x₁` first can leave the singleton `x₀` active.  Hence arbitrary literal sorting
does not even preserve the shallowness premise consumed by the collapse round.

An exact-canonical-tree quotient remains sound but leaves the six literal permutations distinct,
so it cannot repair the existing `3 + 0 < 6` alphabet counterexample.  A semantic quotient would
instead require redefining the canonical walk itself to consume a globally normalized DNF and then
re-establishing the switching encoder/decoder and collapse interfaces for that new walk.

The precise next frontier is to choose between two genuinely different routes: formalize a
normal-form canonical walk (including absorption of redundant clauses, as the depth-sensitive
example requires) and audit whether its witness encoding remains injective, or abandon the raw
gate-key alphabet density and build a semantic counting code that does not require tree-preserving
representatives.  Either route must still confront the independent-support additive-contraction
obstruction.  No P-versus-NP conclusion follows.

### Semantic gate keys cannot reconstruct the fresh variable from position

The semantic-counting route already needs more information than a semantic quotient of the
existing `(gate,term)` key.  The realized-prefix decoder combines a literal-position stream with
the raw key to recover each selected fresh coordinate.  In the reordered singleton examples, both
first witnesses have literal position zero, but this position denotes `x₀` in
`orderedThreeLiteralGate012` and `x₁` in `orderedThreeLiteralGate102`.

`orderedThreeLiteral_no_semanticKey_position_decoder` formalizes the resulting impossibility for
an arbitrary target type and arbitrary key map: if the key identifies every pair of semantically
equal DNFs, no decoder from `(key, literal position)` can recover the correct first coordinate for
both examples.  This is independent of exact-tree coverage.  It shows that a semantic prefix code
must separately retain the queried coordinate, or retain enough ordered syntax to determine it;
simply replacing `ActualFamilyKey` by a semantic gate class destroys the root-code injectivity
argument.

The precise next frontier is to test the smallest viable augmented code: record the selected fresh
coordinate together with a semantic component/key class, then derive its exact finite cardinality
and compare its unavoidable support factor with the proved independent-support additive
contraction obstruction.  If the coordinate alphabet reintroduces an `n`-scale base, the current
uniform multiplicative density cannot close and the trunk schedule or counting injection must
change.  The normal-form canonical-walk route remains logically available but still requires new
encoder/decoder and collapse proofs.  No P-versus-NP conclusion follows.

### Direct coordinate augmentation fails the proportional shell balance

The smallest total repair of the semantic-key decoder has now been counted exactly.
`CoordinateSemanticPrefixLabel n d S` stores one optional queried coordinate in each of the `d`
prefix slots and an optional symmetric multiset of `d` abstract semantic keys from an alphabet of
size `S`.  `card_coordinateSemanticPrefixLabel` proves its cardinality is

`(n+1)^d * (choose(S+d-1,d)+1)`.

The coordinate cost is already fatal for the current half-shell schedule, independently of the
quality of semantic quotienting.  `not_coordinateSemantic_exact_balance_half` proves that for
`r > 0` and `2*r ≤ n`, the exact balance at `K = 2*r`, `d = r`, with saving exponent `r` is
impossible for every `S`, including `S = 0`.  The proof does not relax stars and bars to a word
bound: the coordinate word alone dominates the exact symmetric code over all `n` coordinates, to
which the earlier proportional-depth obstruction applies.

Thus attaching queried coordinates to independently coded semantic keys cannot replace the raw
ordered key in the existing injection.  Together with the independent-support result, this shows
that the obstruction is structural: a coordinate-by-coordinate prefix label pays an ambient-scale
alphabet while a shallow trunk removes only additively many independent charges.

The precise next frontier is to abandon per-query coordinate words and test whether a set-valued
support code can be coupled to the endpoint (so its cost is binomial rather than `n^d`) while still
recovering the ordered canonical prefix.  If endpoint plus an unordered queried-coordinate set
cannot recover order, preserve that counterexample and redirect to a different trunk schedule or
a genuinely new counting injection.  The normal-form canonical-walk route remains available but
requires rebuilding its encoder/decoder and collapse interfaces.  No P-versus-NP conclusion
follows.

### Unordered coordinate sets close injectivity but fail half-shell balance

The endpoint coupling is stronger than the previous frontier question suggested: reconstructing
the ordered canonical prefix is unnecessary.  `CoordinateSetPrefixLabel n d` is the subtype of
`d`-element finsets of `Fin n`, and `card_coordinateSetPrefixLabel` proves its exact cardinality is

`choose(n,d)`.

On every path of length at least `d`, `canonicalCoordinateSetPrefixLabel` records exactly
`freshTaggedPrefixVars`.  Equality of this unordered set and equality of the corresponding prefix
endpoint recover the root by re-freeing the selected coordinates.  The theorem
`coordinateSetCanonicalCommonLongPath_count` therefore gives the family-independent bound

`|Bad| ≤ |Short| * choose(n,d)`

without semantic keys, gate keys, literal positions, or ordered-prefix reconstruction.  This is a
strict improvement over both the coordinate word and the stars-and-bars key labels.

The sharper code nevertheless does not meet the current proportional schedule.
`not_coordinateSet_exact_balance_half` proves that for `r > 0` and `2r ≤ n`, the exact balance at
`K = 2r`, `d = r`, including the requested saving `2^r`, is impossible.  The endpoint shell and
the label each contribute `choose(n,r)`, while `choose(n,2r) ≤ choose(n,r)^2`; the remaining power
of two makes the proposed left side strictly larger.

Thus the coordinate-set route succeeds completely as an injection but preserves a quantitative
counterexample to the uniform half-shell schedule.  The precise next frontier is to change the
counting measure or trunk schedule so that selected coordinates are charged conditionally against
the root support (rather than multiplying an ambient `choose(n,d)` label by the entire endpoint
shell), and test that conditional/fiberwise count first on the independent-literal family.  If no
such cancellation is available, the counting injection must change more fundamentally.  The
normal-form canonical-walk route remains available but is no longer needed merely to obtain an
injective prefix code.  No P-versus-NP conclusion follows.

### Full endpoint-compatible fibers do not cancel the shell

The first conditional/fiberwise audit is now exact.  At a root with `K` live coordinates and a
prefix selecting `d ≤ K`, the endpoint has `K-d` live coordinates.  Relative to that endpoint the
selected set must lie among its `n-(K-d)` fixed coordinates, so the full compatible label fiber has
size `choose(n-(K-d),d)`, rather than the ambient `choose(n,d)`.

This smaller fiber does not yield a smaller total counting space.  The theorem
`endpointFiber_coordinateSet_exact_count` proves, for `d ≤ K ≤ n`,

`choose(n,K-d) * 2^(n-(K-d)) * choose(n-(K-d),d)`

`= choose(n,K) * 2^(n-K) * choose(K,d) * 2^d`.

Thus the endpoint-shell growth exactly compensates for the fiber restriction and leaves an
additional factor `choose(K,d) * 2^d` over the root shell.  The companion theorem
`endpointFiber_coordinateSet_strictly_larger` proves that this compatible-pair space is already
strictly larger than the root shell whenever `d>0`, even before imposing any requested saving.

This closes the naive fiberwise route that enumerates every endpoint-compatible selected set.  It
does not rule out a sharper conditional count of the actually realized canonical image: for a
fixed gate family, canonical query order may occupy only a small subset of each compatible fiber.
The precise next frontier is therefore to characterize that realized image on the preserved
independent-literal family.  Either prove that its per-endpoint multiplicity still has an
unavoidable `choose(K,d)`-scale obstruction, or extract a genuine multiplicity reduction and test
it against the half-shell saving.  No P-versus-NP conclusion follows.

### The realized independent-literal fiber is already nontrivial

The first actual-image test rules out the strongest possible conditional cancellation.  The
family `independentTwoLiteralGates` consists of the two singleton gates `x₀` and `x₁`.  Starting
from either root obtained by freeing exactly one coordinate of the all-false assignment, its
fuel-one canonical prefix selects that live coordinate and returns to the same fully fixed
endpoint.  `independentTwoRoot0_realized_label` and
`independentTwoRoot1_realized_label` compute the two distinct realized singleton labels.

`independentTwo_realized_endpoint_fiber_card` packages the exact result: the common endpoint has
two distinct realized roots, exactly `choose(2,1)`, so this smallest independent family fills its
entire compatible coordinate-set fiber.  Consequently no universal multiplicity-one or
family-independent constant-fiber refinement can justify the desired shell cancellation.

This finite counterexample does not yet establish an asymptotic `choose(K,d)` lower bound.  The
precise next frontier is to parameterize the construction: use all `n` independent singleton
gates and roots obtained by freeing a `d`-set from one fixed total assignment, then prove that all
`choose(n,d)` such roots return to the common endpoint when the canonical prefix has budget `d`.
If canonical gate order prevents full realization for `d>1`, compute the exact surviving subfamily
and compare its growth with the half-shell saving.  No P-versus-NP conclusion follows.

### The first multi-query independent fiber is also full

The `n = 3, d = 2` audit now tests the first case not covered by the one-query example.
`independentThreeLiteralGates` contains the three singleton gates `x₀`, `x₁`, and `x₂`.
The three roots free respectively `{0,1}`, `{0,2}`, and `{1,2}` from one all-false endpoint.

`independentThree_realized_labels` computes that the two-query canonical prefixes realize all
three corresponding coordinate labels.  `independentThree_realized_endpoint_fiber_card` proves
that all three roots return to the same all-false endpoint and that their realized fiber has exact
size `choose(3,2) = 3`.  Thus canonical gate order does not force multiplicity one, or otherwise
collapse the full compatible fiber, merely because `d > 1`.

This remains a finite case, so the asymptotic lower bound is not yet proved.  The precise next
frontier is to add the generic singleton-family trace lemma: for a root free exactly on a finset
`S`, show that the fresh tagged stream lists exactly the members of `S` in gate order.  It should
then yield, for every `d ≤ n`, all `choose(n,d)` roots over the fixed all-false endpoint.  If that
generic trace proof exposes an unexpected boundary condition, preserve it and state the exact
surviving range.  No P-versus-NP conclusion follows.

### The generic independent-literal fiber is full

The finite pattern now extends to every dimension.  `independentLiteralGates n` contains the
positive singleton gate `x_i` at every coordinate, while `independentRoot S` frees exactly the
finset `S` from the common all-false assignment.  The gate-local trace theorem
`independentLiteral_queryVars` proves that gate `i` contributes `[i]` exactly when `i ∈ S`.
After common refinement and read-once normalization, `independentLiteral_pathVars` therefore
identifies the exact queried-coordinate set with `S`.

`independentLiteral_freshTaggedPrefixVars` transfers that exact set through the actual fresh tagged
witness stream.  Its proof also establishes that the stream length is exactly `|S|`, so taking a
budget of `|S|` loses no member.  `independentLiteral_freshTaggedPrefixEndpoint` then shows that
every such root returns to the same all-false endpoint.

Finally, `independentRealizedRoots n d` is the injective image of all `d`-subsets of `Fin n`, and
`independentLiteral_realized_endpoint_fiber_card` proves its exact cardinality is `choose(n,d)` and
that every member reaches that common endpoint with budget `d`.  This holds for all natural `n,d`;
when `d > n` both sides are empty/zero.  Thus the actually realized canonical image has the full
asymptotic compatible-fiber multiplicity on the independent singleton family.  Canonical gate
order supplies no universal multiplicity reduction at the fully fixed endpoint.

The precise next frontier is the partially free endpoint relevant to proportional schedules:
start with a root having `K>d` live singleton coordinates, prove that the fresh prefix selects the
first `d` live coordinates in `Fin` gate order, and count the roots over each residual
`(K-d)`-live endpoint.  This will determine whether gate order creates a genuine conditional
cancellation at `K=2d`, even though the `K=d` endpoint fiber is maximally large.  No P-versus-NP
conclusion follows.

### The partially free singleton endpoint already has multiplicity

The list-level audit now exposes the order that the previous set theorem forgot.
`independentLiteral_runWitSeq` proves that singleton gate `a` contributes exactly the canonical
key `(0,0)` when `a` is live, and nothing otherwise.  Consequently
`independentLiteral_taggedRawVars` proves that decoding the raw tagged stream gives precisely the
live coordinates in `Fin` gate order.  The globally fresh trace has exact length `|S|`, and
`independentLiteral_prefixEndpoint_stars` proves that every budget-`d` prefix with `d ≤ |S|`
lands in the exact `(|S|-d)`-live shell.

The generic ordered-prefix interface is now exact as well.  `independentLiveOrder_nodup` proves
that the gate-ordered live list has no repetitions.  Combining stable freshness's sublist,
decoded-set, and no-duplicate invariants, `independentLiteral_freshTaggedVars` proves that fresh
filtering leaves the decoded singleton stream unchanged as a list, not merely as a set.
Consequently `independentLiteral_freshTaggedPrefixVars_eq_take` identifies every budgeted label
with the first `d` members of `independentLiveOrder S`, and
`independentLiteral_freshTaggedPrefixEndpoint_eq_sdiff` identifies the reached restriction exactly
with the independent root on the residual set
`S \ ((independentLiveOrder S).take d).toFinset`.

The first proportional partially free case already rules out universal conditional
multiplicity one.  At `n=3`, `K=2`, and `d=1`, the distinct roots freeing `{0,2}` and `{1,2}` both
reach the same endpoint that retains only coordinate `2`; this is proved by
`independentThree_partial_endpoint_fiber_two`.  Thus gate order can reduce a fiber relative to the
fully fixed endpoint, but it does not collapse every `K=2d` endpoint fiber to one.

The precise next frontier is now the generic ordered fiber count itself.  For nonempty residual
`E`, characterize the roots reaching `independentRoot E` as `E ∪ D`, where `D` is a `d`-set below
`min(E)`; handle the empty-residual endpoint separately.  Prove the resulting exact binomial
cardinality, maximize it at `K=2d`, and compare that maximum directly with the required `2^d`
shell saving.  No P-versus-NP conclusion follows.

### A generic ordered binomial subfiber is realized exactly

The first half of the ordered-fiber count is now generic.  `independentLiveOrder_pairwise` and
`independentLiveOrder_eq_sort` identify the singleton-family query order with the increasing sort
of the live finset.  If every coordinate in `D` is below every coordinate in a residual set `E`,
`independentLiveOrder_union_of_lt` therefore splits the trace exactly as the order of `D` followed
by the order of `E`.  `independentLiteral_prefixEndpoint_union_of_lt` uses `|D| = d` to prove that
the budget-`d` prefix consumes precisely `D` and reaches `independentRoot E`.

`independentStrictBelow E` is the set of coordinates below every member of `E`, and
`independentOrderedFiber E d` takes the roots `independentRoot (D ∪ E)` over all `d`-subsets of
that initial region.  `independentOrderedFiber_card_and_endpoint` proves both that every such root
reaches the common endpoint `independentRoot E` and that the roots are distinct, giving the exact
realized subfiber size

`choose((independentStrictBelow E).card, d)`.

For nonempty `E`, the base is the initial segment below `min(E)`; for `E = ∅`, the definition
uniformly recovers the full `choose(n,d)` common all-false fiber.  This is an actual canonical-image
lower bound, not a count of all endpoint-compatible labels.  It does not yet prove that these are
all `K`-live roots reaching `E`, nor does it maximize the binomial over `|E| = K-d`.

The precise next frontier is to prove the converse characterization under the shell condition
`|S| = K`: if the budget-`d` prefix from `independentRoot S` reaches `independentRoot E`, then
`S = E ∪ D` for a unique `d`-set `D ⊆ independentStrictBelow E` (with the empty endpoint treated
by the already verified full-prefix theorem).  Then rewrite the base as `min(E)`, maximize it for
`K = 2d`, and compare the resulting maximum directly with the required `2^d` saving.  No
P-versus-NP conclusion follows.

### The ordered endpoint converse is exact and uniform

The missing converse no longer needs a separate empty-endpoint case.
`independentLiteral_prefixEndpoint_converse` takes the actual first `d` members of the increasing
live order and proves that, whenever the prefix reaches `independentRoot E`, this consumed set has
cardinality exactly `d`, lies in `independentStrictBelow E`, and reconstructs the source as
`S = D ∪ E`.  The proof uses the already exact residual-set identity and the cross term of
pairwise ordering on `take d ++ drop d`; it does not infer the order merely from cardinalities.

`independentLiteral_prefixEndpoint_iff_existsUnique` combines that converse with the realized
union theorem.  Under `d ≤ |S|`, reaching `independentRoot E` is now equivalent to the existence
of a unique `d`-set `D ⊆ independentStrictBelow E` satisfying `S = D ∪ E`.  This includes
`E = ∅`, because the strict-below condition is then vacuous and the source itself is the unique
consumed set.

Thus the generic canonical trace has been completely characterized pointwise.  The existing
`independentOrderedFiber_card_and_endpoint` is no longer only a lower-bound construction in
principle; the new converse supplies the missing exhaustion direction, although the explicit
finite shell-fiber equality/cardinality corollary has not yet been packaged.

The precise next frontier is to define that fixed-`K` endpoint fiber and prove it equals
`independentOrderedFiber E d` when `|E| = K-d`; then identify
`(independentStrictBelow E).card` with the value of `min(E)` for nonempty `E`, maximize the exact
binomial at `K = 2d`, and compare it with the required `2^d` saving.  No P-versus-NP conclusion
follows.

### The fixed-shell ordered endpoint fiber is exact

`independentFixedShellEndpointFiber K d E` now packages the actual roots obtained from `K`-element
free-coordinate sets whose budget-`d` canonical prefix reaches `independentRoot E`.  Under the
necessary shell conditions `d ≤ K` and `|E| = K-d`,
`independentFixedShellEndpointFiber_eq_ordered` proves this fiber is exactly
`independentOrderedFiber E d`, not merely that the latter embeds into it.  The forward inclusion
uses the unique consumed-set converse; the reverse inclusion uses strict-below disjointness and the
identity `d + (K-d) = K` to return every ordered union to the source shell.

Consequently `independentFixedShellEndpointFiber_card` gives the exact endpoint multiplicity

`choose((independentStrictBelow E).card, d)`.

This closes the finite-set packaging gap and confirms that there are no additional `K`-live roots
hidden outside the realized ordered construction.  The precise next frontier is arithmetic:
identify `(independentStrictBelow E).card` with the numeric value of the least member of nonempty
`E`, then maximize this exact binomial over endpoints with `|E| = d` at `K = 2d` and compare the
maximum directly with the required `2^d` saving.  No P-versus-NP conclusion follows.

### The ordered-fiber base is the least residual coordinate

The remaining filtered-finset cardinality is now explicit.  For nonempty `E`,
`independentStrictBelow_eq_Iio_min'` proves

`independentStrictBelow E = Iio (min(E))`,

and `Fin.card_Iio` therefore gives cardinality equal to the numeric value of `min(E)`.
`independentFixedShellEndpointFiber_card_eq_choose_min'` combines this with the exact fixed-shell
fiber theorem, yielding endpoint multiplicity

`choose(min(E), d)`.

Thus the trace and finite-set layers have been eliminated from the remaining question.  The
precise next frontier is to maximize `choose(min(E), d)` subject to `E ⊆ Fin n` and `|E| = d`.
The expected extremal endpoint is the final `d` coordinates, with `min(E) = n-d`; after proving
that exact maximum, compare `choose(n-d,d)` directly with the required `2^d` shell saving.  No
P-versus-NP conclusion follows.

### The fixed-shell ordered fiber has an attained exact maximum

The extremal arithmetic is now proved.  `min'_val_le_card_complement` embeds every nonempty
`d`-set `E` into the final interval beginning at `min(E)` and uses its cardinality to show

`min(E) ≤ n-d`.

Binomial monotonicity and the exact fiber formula therefore bound every residual `d`-endpoint in
the `K = 2d` shell by `choose(n-d,d)`.  The final `d` coordinates attain the bound:
`exists_card_min'_val_eq_card_complement` constructs that endpoint with least member `n-d`, and
`exists_independentFixedShellEndpointFiber_card_eq_choose_card_complement` proves its fiber has
cardinality exactly `choose(n-d,d)`.  Thus this is an exact maximum, not only an upper estimate.

The precise next frontier is the requested-saving comparison.  Insert the attained maximum into
the shell balance and determine exactly which `n,d` regimes can absorb the factor
`choose(n-d,d) * 2^d`; in particular, test the proportional `K = 2d` schedule rather than bounding
the binomial by a word count.  No P-versus-NP conclusion follows.

### The attained ordered-fiber maximum rules out the proportional balance

`independentOrderedFiberMaximum_exact_shell_count` inserts the exact maximum into the complete
residual-shell count.  For every nonempty proportional shell (`2d ≤ n`), it proves

`choose(n,d) * 2^(n-d) * choose(n-d,d) * 2^d`

`= choose(n,2d) * 2^(n-2d) * choose(2d,d) * 2^(2d)`.

Thus the proposed left side is not merely too large in a particular density regime: for every
`d > 0` it exceeds the original `2d`-shell by the strict factor
`choose(2d,d) * 2^(2d)`.  The theorem
`not_independentOrderedFiberMaximum_exact_balance_half` formalizes that no ambient `n` with
`2d ≤ n` can absorb the attained worst-case fiber together with the requested `2^d` saving.
Increasing `n`, retaining the factorial in stars-and-bars, or tuning the previous density constant
cannot repair this proportional maximum-fiber argument.

The precise next frontier is to avoid multiplying the entire residual shell by the worst endpoint
fiber.  The next useful target is an aggregate incidence bound coupling bad endpoints to their
actual ordered fibers (or a proof that the independent-singleton family saturates that incidence
on a relevant bad event).  Without such correlation, the exact maximum-fiber route is closed.  No
P-versus-NP conclusion follows.

### Aggregate ordered incidence is exactly conserved

The first aggregate audit is now exact.  `independentFixedShellCoordinateFiber` exposes the
coordinate-set fiber before the injective `independentRoot` encoding, and
`independentFixedShellEndpointFiber_card_eq_coordinateFiber` proves that passing to restrictions
does not change any fiber cardinality.

`independentFixedShellEndpointFiber_aggregate_exact` then partitions all `2d`-element live sets by
their actual budget-`d` canonical residual endpoint and proves, for every `n,d`,

`sum_{|E|=d} |independentFixedShellEndpointFiber (2d) d E| = choose(n,2d)`.

The theorem needs no feasibility hypothesis: if `2d > n`, both sides vanish.  Thus on the
independent singleton family the canonical endpoint map conserves aggregate incidence exactly.
The previously attained maximum `choose(n-d,d)` is real but highly localized; multiplying it by
every residual endpoint is pure overcount, not a property of the realized canonical image.

This removes the unrestricted aggregate incidence itself as an obstruction and identifies the
missing correlation precisely.  The next frontier is to restrict the partition to
`commonShallowBad` roots using the canonical bad-assignment prefix, and determine whether the bad
event concentrates on the large ordered fibers or instead admits an endpoint-local weighted bound.
That requires relating the arbitrary bad-assignment fixed values to the independent-root model (or
building the corresponding general restriction-valued fiber partition); the unweighted exact
partition alone supplies no positive saving.  No P-versus-NP conclusion follows.

### Canonical bad roots now have an exact endpoint partition

The general restriction-valued partition has now been built.  `commonShallowBadEndpointFiber`
restricts the actual `commonShallowBad` event to roots whose chosen fresh-prefix endpoint is a
specified residual restriction.  `commonShallowBadEndpointFiber_aggregate_exact` proves that any
extending assignment with a genuinely length-`d` trace satisfies

`sum_{stars τ = K-d} |bad roots with endpoint τ| = |commonShallowBad|`.

This identity tracks fixed values as well as live coordinates, so it does not assume that an
arbitrary semantic bad witness has the independent-root form.  On ample-fuel shells,
`commonShallowBadAssignment_endpointFiber_aggregate_exact` discharges both hypotheses using the
canonical bad assignment itself.  Thus the independent-family aggregate audit has been lifted to
the actual semantic exceptional event without a worst-fiber multiplication.

The identity alone gives no contraction: all bad mass could still concentrate on endpoints with
expensive prefix-label multiplicity.  The precise next frontier is to define an endpoint-local
realized-prefix label image and prove a weighted inequality for the sum of its actual cardinalities
over residual endpoints.  Comparing that weighted image with the independent ordered fibers will
then decide whether bad roots can saturate the large fibers or whether aggregate correlation yields
the missing saving.  No P-versus-NP conclusion follows.

### Endpoint-local realized labels give an exact weighted accounting

`commonShallowBadEndpointLabelImage` now records, separately at each residual restriction, the
exact ragged-alphabet prefix labels actually realized by semantic bad roots in that endpoint
fiber.  It is an image of the bad fiber, not the full ambient `PrefixActualSymLabel` type, so it
retains the correlation between badness, endpoint, prefix positions, and actual family keys.

`commonShallowBadEndpointLabelImage_card` proves that on extending witnesses with a genuinely
length-`d` trace, this image has exactly the cardinality of its endpoint fiber.  The proof uses
the endpoint together with equality of realized labels to reconstruct the selected variables and
hence the original root.  Summing the result over the residual `(K-d)` shell gives the stronger
identity

`sum_{stars τ = K-d} |actual bad-prefix labels realized at τ| = |commonShallowBad|`.

The ample-fuel specialization
`commonShallowBadAssignment_endpointLabelImage_aggregate_exact` discharges the extension and
length premises for the canonical semantic bad assignment.  Thus the proposed endpoint-local
weighted inequality is exact: no information is lost in passing from bad roots to their realized
labels within fixed endpoints, and no worst-fiber multiplier is present.

This is an accounting interface, not yet a contraction.  The precise next frontier is to bound
this weighted realized image using a property stronger than injective encoding—either show that
semantic residual depth excludes enough endpoint/label pairs, or construct an independent-style
bad family demonstrating saturation.  An ambient label-cardinality bound alone simply recovers
the already audited product bound.  No P-versus-NP conclusion follows.

### Independent singleton badness saturates the zero-residual endpoint incidence

The first semantic saturation test is now formal rather than heuristic.  Two generic common-tree
lemmas show that a followed path contains at most the tree depth many queried coordinates, and
that flipping a coordinate absent from that path reaches the same leaf.  Using the two assignments
that differ only at such a missed live coordinate, `independentRoot_not_commonShallowAt_zero`
proves that no depth-`d` common trunk can make all `K>d` independent singleton gates residual-depth
zero.  The proof applies to the existential `CommonShallowAt` definition, not only to its canonical
prefix witness.

Consequently every root in every realized ordered endpoint fiber belongs to the actual semantic
bad event at threshold zero.  `independentBadEndpointFibers_aggregate_exact` packages the
proportional case `K=2d`: for `d>0`, every explicit endpoint fiber is contained in
`commonShallowBad (independentLiteralGates n) 1 (2d) d 0`, while their aggregate cardinality remains
exactly `choose(n,2d)`.  Thus semantic badness can saturate the full realized endpoint incidence;
there is no threshold-uniform theorem saying that residual depth alone excludes a positive
fraction of endpoint/label pairs.

This counterexample is deliberately limited to residual threshold zero.  Singleton gates become
shallow at threshold one, so it does not refute a saving that exploits the positive residual depth
used by an actual layered round.  The precise next frontier is to test that relevant regime with
disjoint ordered conjunction blocks of residual depth `s+1`: either prove an analogous saturated
bad-fiber construction for positive `s`, or isolate a quantitative exclusion that genuinely uses
`s>0` and the circuit-owned block structure.  No P-versus-NP conclusion follows.

### Positive residual depth already has a semantic bad root

The first disjoint-block test is now formal.  `independentPairGates` consists of the two disjoint
ordered conjunctions on coordinate pairs `{0,1}` and `{2,3}`.  Whenever both coordinates of one
pair remain free, `independentPairGates_depth_two` computes its fuel-two canonical depth exactly as
two.

`independentPairs_not_commonShallowAt_one` proves that no depth-one common trunk on the fully live
four-variable cube makes both gates residual-depth at most one.  Along the all-false branch the
trunk queries at most one coordinate.  At least one whole pair is therefore absent from the path;
flipping each absent coordinate separately proves that the reached leaf cannot fix it, so the
corresponding residual gate still has depth two.  Consequently
`allFreeFour_mem_commonShallowBad_one` places the fully live root in the actual semantic bad event
with parameters `fuel=2`, `K=4`, trunk depth `1`, and residual depth `1`.

Thus the zero-threshold phenomenon is not an artefact of constant singleton gates: positive
residual depth and genuine width-two block structure can still defeat a shallow common trunk.  The
result is intentionally local—it proves one bad root, not full-shell or realized-fiber saturation.
The precise next frontier is to parameterize the construction by `s` and the number of disjoint
`(s+1)`-blocks, then couple it to a fixed-shell endpoint partition.  That will decide whether the
positive-depth bad event aggregates at full shell scale or loses enough mass to permit the desired
round contraction.  No P-versus-NP conclusion follows.

### The positive-depth obstruction now has a parameterized semantic core

`supportedGates_not_commonShallowAt_allFree` isolates the two ingredients used by every
disjoint-block construction at arbitrary parameters.  For a gate family with support sets, assume
that every coordinate set of size at most the proposed trunk depth misses one complete support,
and that a gate whose support is wholly free has canonical depth strictly above the proposed
residual depth.  The theorem proves that no common trunk of that depth can shallow the family on
the fully live cube.  Its fixed-shell corollary
`allFree_mem_commonShallowBad_of_supportedGates` places that root in the actual semantic bad event
with `K=n`.

The proof is insensitive to how a trunk is chosen.  It follows the all-false branch, flips each
unqueried support coordinate separately, and uses extension at both assignments to prove that the
reached leaf leaves the missed block free.  Thus the earlier four-variable argument was not a
finite-case accident: once the block-packing and single-gate depth premises are supplied, the
obstruction already holds uniformly for arbitrary `fuel`, trunk depth, and positive residual
depth.

This is still not full-shell saturation.  The exact next frontier is to instantiate the two
premises for a canonical family of disjoint ordered `(s+1)`-literal conjunctions on arbitrary live
coordinate sets, then count which `K`-shell roots retain more intact blocks than a depth-`d` trunk
can hit.  Coupling that count to the existing endpoint partition will decide whether the bad event
has full-shell-scale mass or an aggregate saving.  No P-versus-NP conclusion follows.

### Pairwise-disjoint blocks now discharge the trunk-packing premise

The abstract support condition is now reduced to its exact finite combinatorial content.
`exists_disjoint_support_of_pairwiseDisjoint` proves that if `G` supports are pairwise disjoint,
then every coordinate set of cardinality below `G` misses one complete support.  Its proof chooses
one allegedly hit coordinate per support and obtains an injection `Fin G → path`; hence it does not
charge the block width or the ambient number of coordinates.

`pairwiseDisjoint_support_miss` specializes this to every path of size at most the trunk depth when
`trunkDepth < G`.  The capstone
`allFree_mem_commonShallowBad_of_pairwiseDisjoint` composes that packing theorem with the existing
semantic core: any pairwise-disjoint gate family containing more blocks than the trunk depth has a
bad fully live root as soon as a wholly free block has canonical depth above the residual target.

Thus the block-count side of the parameterized construction is complete and exact: the critical
threshold is the number of blocks, not their total support size.  The precise next frontier is now
the remaining gate-specific premise: define an arbitrary ordered conjunction block and prove that,
with sufficient fuel and all of its distinct coordinates free, its canonical tree has depth equal
to the block length.  After that, lift the fully live obstruction to `K`-shell roots by counting
restrictions retaining more than `trunkDepth` intact blocks and couple those roots to the endpoint
partition.  No P-versus-NP conclusion follows.

### Arbitrary ordered conjunction blocks close the semantic obstruction

`orderedConjunctionBlock` packages any coordinate list as one ordered positive conjunction.
`orderedConjunctionBlock_depth` proves that if the coordinates are duplicate-free and remain free,
then fuel equal to the list length gives canonical depth exactly that length, regardless of all
coordinates outside the block.  The proof follows the satisfying branch, carrying the already-true
prefix and still-free suffix as an invariant; the falsifying sibling is controlled by the general
fuel upper bound.

The capstone `allFree_mem_commonShallowBad_of_orderedConjunctionBlocks` composes this computation
with pairwise-disjoint support packing.  For `G` pairwise-disjoint duplicate-free blocks of common
width `w`, every trunk of depth below `G` leaves a whole block untouched, and the fully live root is
semantically bad for every residual target below `w`.  Thus both abstract premises of the
parameterized fully-live obstruction are now discharged by a concrete gate family.

The precise next frontier is no longer gate semantics.  Count fixed-`K` restrictions that retain
more than `trunkDepth` complete blocks, first for equal disjoint blocks, and determine their exact
distribution across the existing canonical endpoint partition.  That count will decide whether
positive-residual badness has full-shell-scale mass or enough aggregate decay for the layered round.
No P-versus-NP conclusion follows.

### The many-intact-block shell event now embeds in semantic badness

`intactSupportBlocks support σ` is the exact set of indexed blocks whose entire support remains
free at an arbitrary restriction `σ`.  The packing lemma
`exists_intact_support_disjoint_of_pairwiseDisjoint` proves that, for pairwise-disjoint supports,
any queried coordinate set smaller than this intact-block set misses one of those intact blocks
completely.

The semantic argument has also been lifted off the fully live cube.
`supportedGates_not_commonShallowAt_of_intact_miss` starts from an arbitrary root restriction,
follows one extending assignment, and toggles an unqueried coordinate of the missed intact block.
Agreement of both assignments with the same trunk leaf forces that coordinate to remain free.
Consequently `pairwiseDisjoint_supportedGates_not_commonShallowAt_of_intact` rules out every common
trunk whose depth is below the number of intact deep blocks.

The concrete capstone
`mem_commonShallowBad_of_orderedConjunctionBlocks_of_many_intact` now states the desired shell
inclusion: every `K`-star restriction retaining more than `trunkDepth` pairwise-disjoint,
duplicate-free width-`w` conjunction blocks is in the actual semantic bad event for every residual
target below `w`.  Thus no further semantic bridge is needed for these roots.

The precise next frontier is an exact cardinality formula (or sharp lower bound) for this explicit
many-intact-block event on the `K`-shell, followed by its distribution across the existing
canonical prefix-endpoint fibers.  For equal disjoint blocks this is a finite hypergeometric
occupancy count; formalizing that count will determine whether the obstruction has shell-scale
mass in the intended parameter regime.  No P-versus-NP conclusion follows.

### Fixed-value multiplicity is now factored out exactly

`manyIntactShell support K d` is the explicit restriction event with exactly `K` live coordinates
and more than `d` wholly live support blocks.  `manyIntactFreeSets support K d` is its underlying
occupancy event on `K`-element coordinate sets.  The exact factorization
`manyIntactShell_card` proves

```text
|manyIntactShell support K d|
  = |manyIntactFreeSets support K d| * 2^(n-K).
```

The proof partitions restrictions by their exact free-variable set and applies the established
fiber count.  It therefore loses neither fixed-coordinate assignments nor correlations between
block occupancy and the chosen live set.

For the pairwise-disjoint ordered conjunction construction,
`manyIntactShell_subset_commonShallowBad_of_orderedConjunctionBlocks` embeds this entire event in
semantic badness, and `manyIntactFreeSets_mul_pow_le_commonShallowBad_card` records the resulting
cardinality lower bound.  Consequently the restriction-valued counting problem has been reduced
exactly to a finite-set occupancy count: the Boolean values on the `n-K` fixed coordinates are a
uniform multiplicative factor and cannot create an endpoint saving.

The precise next frontier is to evaluate `manyIntactFreeSets` for `G` equal pairwise-disjoint
width-`w` blocks (and an optional outside-coordinate reservoir).  This is the remaining
hypergeometric coefficient: count `K`-subsets containing more than `d` complete blocks, with
partial occupancy of the other blocks handled without double counting.  Then distribute those
free sets, or their induced restrictions, across the canonical prefix-endpoint fibers.  No
P-versus-NP conclusion follows.

### Occupancy profiles remove the partial-block double-counting ambiguity

`freeSetOccupancyCode support S` now records the actual intersection of `S` with every support
block together with `S` outside the union of all supports.  `freeSetOccupancyCode_reconstruct` and
`freeSetOccupancyCode_injective` prove that this record is lossless.  Injectivity does not require
disjoint blocks; consequently it cannot hide a choice of a preferred intact block or count a free
set more than once when several blocks are complete.

For pairwise-disjoint supports, `freeSetOccupancyCode_card` proves the exact additive shell
constraint

```text
|S| = sum_g |S ∩ support(g)| + |S \ union_g support(g)|.
```

Finally, `mem_manyIntactFreeSets_iff_occupancy` rewrites the obstruction event as the lossless
profiles satisfying total size `K` and having more than `d` components equal to their full
supports.  Partial occupancies and outside coordinates therefore have explicit, disjoint slots;
the remaining enumeration is a genuine product-of-binomial-coefficients calculation rather than
an inclusion-exclusion problem.

The precise next frontier is to define the finite set of admissible occupancy-size vectors
`a : Fin G → Fin (w+1)` and outside size `r`, prove that each fiber has cardinality
`(product_g choose w (a g)) * choose (n-G*w) r`, and sum exactly over
`sum_g a(g)+r=K` with more than `d` entries equal to `w`.  Only after that coefficient is proved
should it be distributed across canonical prefix-endpoint fibers.  No P-versus-NP conclusion
follows.

### Every occupancy-size fiber now has the exact hypergeometric weight

`occupancySizeFiber support a r` is the finite set of free-coordinate sets whose intersection
with block `g` has cardinality `a(g)` and whose outside component has cardinality `r`.
`occupancySlotChoices support a r` independently selects those block subsets and the outside
subset.  The reconstruction theorem `freeSetOccupancyCode_reconstructChoice` proves that, for
pairwise-disjoint supports, these independent choices are in bijection with the size fiber.  This
is stronger than an upper or lower bound and explicitly rules out overlap between two profiles.

Consequently `occupancySizeFiber_card` proves the general exact formula

```text
|fiber(a,r)|
  = (product_g choose |support(g)| (a(g)))
      * choose |outside| r.
```

For `G` pairwise-disjoint blocks of common width `w`,
`supportUnion_card_of_pairwiseDisjoint_uniform` computes the occupied reservoir as `G*w`, and
`occupancySizeFiber_card_uniform` specializes the formula to

```text
|fiber(a,r)| = (product_g choose w (a(g))) * choose (n-G*w) r.
```

Thus the individual summand advertised by the occupancy audit is now formal, including partial
blocks and all outside coordinates.  The precise next frontier is to define the finite admissible
index set with `a(g) ≤ w`, `sum_g a(g)+r=K`, and more than `d` entries equal to `w`; prove that its
size fibers form an exact disjoint partition of `manyIntactFreeSets`; and rewrite the event's
cardinality as the resulting finite sum.  After that, evaluate the coefficient in the intended
parameter regime before distributing it across canonical prefix-endpoint fibers.  No
P-versus-NP conclusion follows.

### The admissible profiles now form an exact finite partition

`occupancySizeIndex support S` packages every block-intersection cardinality and the outside
cardinality into a finite `(Fin G → Fin (n+1)) × Fin (n+1)` index.  The ambient `n+1` bound keeps
the construction uniform for ragged block families.  `admissibleOccupancyIndices support K d`
filters these indices by the three exact constraints: every coordinate is at most its block size,
the block and outside occupancies sum to `K`, and more than `d` block coordinates are full.

For pairwise-disjoint supports, `occupancySizeIndex_mem_admissible_iff` proves that a set's index
is admissible exactly when the set lies in `manyIntactFreeSets`.  Moreover,
`manyIntactFreeSets_filter_sizeIndex_eq` identifies each admissible fiber with the previously
counted `occupancySizeFiber`.  Applying finite fiberwise counting therefore gives the exact ragged
formula

```text
|manyIntactFreeSets support K d|
  = sum_(a,r admissible)
      (product_g choose |support(g)| a(g)) * choose |outside| r.
```

This closes the disjoint-partition obligation: partial blocks and outside coordinates occur in
one and only one summand, and the full-block threshold is enforced inside the finite index set.
For equal width `w`, the already-proved union-cardinality lemma rewrites every summand to
`(product_g choose w a(g)) * choose (n-G*w) r`.

The precise next frontier is to evaluate or sharply bound this exact coefficient in the intended
`K,d,G,w,n` schedule and compare its shell density against the canonical prefix-endpoint fiber
capacity.  Only then should the coefficient be distributed across those endpoint fibers.  No
P-versus-NP conclusion follows.

### The exact support-volume cutoff makes the intended many-intact event empty

The first evaluation of the exact coefficient is decisive for the currently verified schedule.
`manyIntactFreeSets_eq_empty_of_uniform_volume` proves that pairwise-disjoint uniform width-`w`
blocks have no `K`-element free set containing more than `d` intact blocks whenever

```text
K < (d+1)*w.
```

The proof unions the intact supports, uses pairwise disjointness to compute their exact volume,
and embeds that union into the free set.  Thus the cutoff is structural rather than an artifact of
bounding the occupancy sum.

Specializing to the half-shell parameters used by the existing contraction theorem,

```text
K = 20*r,  d = 10*r,  w = 2,
```

`manyIntactFreeSets_eq_empty_width_two_half_shell` gives an empty event: the required `10*r+1`
intact blocks consume `20*r+2` live coordinates.  Its restriction-valued shell lift is therefore
empty as well.  Consequently this particular disjoint-width-two construction supplies no bad
mass to compare with canonical endpoint capacity at the intended schedule; distributing its exact
coefficient across endpoints would be vacuous.

The precise next frontier is to audit the boundary event at exactly `d` intact width-two blocks.
A depth-`d` trunk can in principle touch all of them, so any obstruction must prove a query-cost
stronger than one coordinate per block (or use blocks whose residual hardness survives one trunk
query).  If no such stronger semantic construction exists, the positive-residual obstruction
route does not challenge the current half-shell schedule.  No P-versus-NP conclusion follows.

### The smallest exact-boundary instance is common-shallow

The semantic audit now confirms that the one-query-per-block upper bound is attained, not merely
suggested by the volume calculation.  For the existing `independentPairGates` family, the fully
live four-variable root has exactly two intact width-two blocks.  The earlier theorem
`independentPairs_not_commonShallowAt_one` is retained: no depth-one common trunk can make both
gates residual-depth one.

The new explicit `independentPairBoundaryTrunk` queries coordinate `0` from the first block and
coordinate `2` from the second.  Its four leaves store the corresponding restrictions.
`independentPairs_commonShallowAt_two` proves that this depth-two trunk leaves both canonical gate
trees with depth at most one on every extending assignment.  Consequently
`allFreeFour_not_mem_commonShallowBad_two` proves that the same root is not semantically bad at
trunk depth two.

Thus merely changing the intact-block threshold from `d+1` to exactly `d` cannot extend this
ordered-conjunction obstruction, even in its smallest nontrivial case: the strict threshold in
the support-missing argument is sharp.  A viable boundary obstruction must use a gate requiring
at least two trunk queries before its residual canonical depth drops to the target, and its shell
volume must still fit the half-shell schedule.

The precise next frontier is to test the smallest such residual-hard block (width at least three
for target residual depth one) against the volume budget `K = 2*d`.  In particular, determine
whether any mix of larger blocks and partially live supports can force total query cost above `d`
without already exceeding `K`; if not, close the disjoint-block obstruction route at this
schedule.  No P-versus-NP conclusion follows.

### Width three survives the exact half-shell boundary

The smallest larger-block test goes the opposite way from the width-two boundary.  The new
`independentTripleGates` consists of two disjoint ordered conjunctions on coordinates
`{0,1,2}` and `{3,4,5}`.  All six coordinates are live, so this is exactly the proportional
boundary

```text
K = 6,  d = 3,  K = 2*d,
```

with target residual depth one.

`independentTripleGates_depth_gt_one` proves the local residual-hardness statement needed for
the audit: provided no block coordinate is fixed false, any two free coordinates in a triple
force its canonical tree to have depth greater than one.  The proof covers all three possible
free pairs in each block and retains the existing ordered canonical semantics.

`independentTriples_not_commonShallowAt_three` follows the all-true branch of an arbitrary common
trunk.  A depth-three trunk queries at most three distinct coordinates on that branch.  Since the
two triple supports are disjoint, one support contains at most one queried coordinate and hence
retains at least two free coordinates.  Every queried value on this branch is true, so the local
depth lemma applies and contradicts residual depth one.  Finally,
`allFreeSix_mem_commonShallowBad_three` places the fully live root in the actual fixed-six-star
semantic bad event.

Thus larger blocks can force query cost above `d` without exceeding `K = 2d`: here the support
volume is six while the required all-true-path cost is four.  This refutes closure of the
disjoint-block obstruction route based only on the width-two volume argument.  It does not yet
refute the switching contraction: one explicit bad restriction supplies no quantitative lower
bound on a large shell.

The precise next frontier is to generalize the path argument to a weighted deficit condition
`sum_g max(0, live_g - residualDepth) > d`, then count the corresponding partially-live
width-three shell event at the intended scalable parameters `K = 20*r`, `d = 10*r`.  The key
question is whether that event has enough mass, after fixed-value multiplicity, to challenge the
verified upper bound rather than merely being nonempty.  No P-versus-NP conclusion follows.

### The weighted path inequality is proved, with the necessary truth-compatibility correction

`liveSupport support σ g` records the root-live coordinates of block `g`, and
`residualQueryDeficit` is the proposed weight

```text
max(0, |liveSupport(g)| - residualDepth).
```

For pairwise-disjoint supports,
`exists_liveSupport_sdiff_card_gt_of_sum_deficit` proves the exact weighted pigeonhole statement:
if the sum of these deficits exceeds the number of distinct path queries, some block retains more
than `residualDepth` root-live coordinates outside the path.  The proof partitions each block's
live coordinates into queried and unqueried parts and uses disjointness to show that the sum of all
queried parts is at most the path cardinality.  This strictly generalizes the previous whole-block
packing argument and does not assume uniform widths.

The audit also exposed a necessary correction before this combinatorics can be used semantically.
A positive conjunction with a root-fixed false literal is already constant, even if several other
coordinates remain live.  Therefore the unqualified live deficit can overcount hardness.
`supportTrueCompatible` expresses that no support coordinate is root-fixed false, and
`compatibleResidualQueryDeficit` assigns zero weight to incompatible blocks.  The sound capstone
`exists_compatible_liveSupport_sdiff_card_gt_of_sum_deficit` proves that excess *compatible*
deficit yields a compatible block with too many live unqueried coordinates.  Thus fixed Boolean
values cannot be factored out uniformly for the partially-live event, unlike the earlier
whole-intact event; they enter the occupancy weight itself.

The precise next frontier is to prove the corresponding partial-live canonical-depth lemma for an
ordered positive conjunction (truth-compatible root plus `q` remaining live coordinates gives
canonical depth `q` with sufficient fuel), lift the compatible weighted event into
`commonShallowBad`, and then count it at `K = 20*r`, `d = 10*r`, width three.  The count must weight
each non-live coordinate inside a contributing triple by the single allowed fixed value `true`,
rather than by the ambient two-value multiplicity.  No P-versus-NP conclusion follows.

### The compatible weighted event now has a semantic badness interface

`compatibleDeficitShell` is the explicit fixed-star shell event in which the sum of
truth-compatible residual query deficits exceeds the common-trunk budget.  In contrast with the
earlier intact-block event, its membership deliberately retains fixed Boolean values: a partially
live positive block contributes only when every fixed coordinate in its support is true.

`supportedGates_not_commonShallowAt_of_compatible_sum_deficit` lifts the weighted pigeonhole
theorem through an arbitrary common trunk.  It follows the root-compatible all-true assignment,
bounds the number of distinct path queries by trunk depth, and obtains a compatible block with too
many live unqueried coordinates.  The standard toggle argument proves that those coordinates
remain free at the reached leaf, while leaf agreement proves that no coordinate of the selected
support is false there.

The set-level capstone `compatibleDeficitShell_subset_commonShallowBad` therefore embeds the entire
weighted shell event into actual semantic badness, under one explicit gate-local premise:

```text
no support coordinate is false
and residualDepth < number of free support coordinates
implies residualDepth < canonical depth.
```

This completes the generic semantic lift without assuming that canonical depth depends only on a
free-coordinate set; that dependence remains to be proved for the ordered conjunction family.
It also prevents the upcoming count from silently restoring the invalid two-value multiplicity on
fixed internal coordinates.

The precise next frontier is to discharge the local premise for duplicate-free ordered positive
conjunctions with sufficient fuel, then specialize the subset theorem to uniform disjoint
width-three blocks.  After that, count `compatibleDeficitShell` at `K = 20*r`, `d = 10*r`, keeping
one allowed value for every fixed coordinate inside each contributing triple and two values only
outside the constrained compatible supports.  No P-versus-NP conclusion follows.

### The ordered-conjunction depth premise is discharged semantically

`orderedConjunctionBlock_freeSupport_card_le_depth` proves the required partial-live statement.
If no coordinate appearing in an ordered positive conjunction is fixed false and
`stars rho <= fuel`, then

```text
|(xs.toFinset) ∩ freeVars rho| <= depth(canonicalDT [AND xs] fuel rho).
```

The proof follows the all-true extension of `rho`.  If a free support coordinate were absent from
that decision-tree path, flipping only that coordinate would preserve the tree output by off-path
invariance but change the conjunction from true to false.  Correctness of `canonicalDT` under the
fuel premise gives the contradiction.  This argument counts distinct support coordinates, so the
result is stronger than the anticipated duplicate-free lemma: neither `xs.Nodup` nor a particular
placement of fixed-true coordinates is required.

`compatibleDeficitShell_subset_commonShallowBad_of_orderedConjunctionBlocks` then instantiates the
generic weighted semantic lift for every pairwise-disjoint family of ordered positive
conjunctions.  It uses ambient fuel `n`, which is sufficient for every restriction because
`stars rho <= n`.  Consequently the specialization has no remaining local canonical-depth
premise and already includes uniform disjoint width-three families as a special case.

The precise next frontier is now purely quantitative: compute or sharply lower-bound the cardinality
of `compatibleDeficitShell` for uniform disjoint triples at `K = 20*r`, trunk depth `d = 10*r`,
and residual depth one.  The count must distinguish the four local triple states: three live
coordinates contribute deficit two, two live plus one fixed-true contributes deficit one, and all
other states contribute zero; only coordinates outside contributing compatible triples retain
unrestricted two-value multiplicity.  Compare that weighted occupancy count against the verified
common-shallow upper bound before attempting endpoint-fiber distribution.  No P-versus-NP
conclusion follows.

### The exact intact-triple occupancy sum is a verified weighted-shell lower bound

The first quantitative bridge reuses the exact stars-and-bars infrastructure instead of rebuilding
the full weighted count at once.  `compatibleResidualQueryDeficit_eq_two_of_intact_triple` proves
that a completely live width-three support contributes exactly two units at residual depth one.
Consequently `manyIntactShell_subset_compatibleDeficitShell_triples` proves the scalable inclusion

```text
manyIntactShell support (20*r) (5*r)
  ⊆ compatibleDeficitShell support (20*r) (10*r) 1.
```

Indeed, more than `5*r` intact triples contribute more than `10*r` total deficit.  This subevent
does not impose any Boolean-value penalty inside its selected blocks because all their coordinates
are free.  Other blocks may be arbitrary, and any additional compatible partial triples only
increase the deficit.

`compatibleDeficitShell_triples_occupancy_lower_bound` composes this inclusion with the earlier
exact disjoint-support enumeration and fixed-value factor.  It gives the explicit lower bound

```text
(sum over admissible occupancies with > 5*r intact triples
   product_g choose(3,a_g) * choose(outside,r_out)) * 2^(n-20*r)
  ≤ |compatibleDeficitShell support (20*r) (10*r) 1|.
```

Finally, `manyIntactShell_card_le_commonShallowBad_of_orderedTriples` pushes the same counted
subevent through the ordered-conjunction semantic interface into the actual common-shallow bad
set.  Thus the lower-bound route is no longer missing either a semantic premise or a
restriction-multiplicity factor.

This does not yet decide the balance.  The intact-only subevent omits the potentially important
local state with two live coordinates and one fixed-true coordinate, which contributes one unit.
For one triple the exact bivariate state enumerator (star marker `z`, deficit marker `y`) is

```text
8 + 12*z + 3*z^2 + 3*z^2*y + z^3*y^2.
```

The precise next frontier is to formalize the coefficient identity obtained from the `G`th power
of this polynomial and the outside factor `(2+z)^(n-3G)`, summing coefficients of `z^(20*r)` whose
`y`-degree exceeds `10*r`.  Then compare that full weighted mass—and, separately, the now-verified
intact-only lower bound—against the common-shallow upper bound in the intended growing-`G` schedule.
Only if the aggregate balance is adverse should endpoint-fiber concentration be audited next.
No P-versus-NP conclusion follows.

### The full width-three generating function now has a verified local coefficient table

The weighted-shell count has been factored at its smallest nontrivial unit.  For an abstract
width-three restriction `rho : Fin 3 → Option Bool`, `tripleLocalStars` records the number of live
coordinates and `tripleLocalDeficit` records the truth-compatible residual query deficit at
residual depth one.  `tripleLocalFiber s d` is their joint fiber.

Five kernel-checked cardinality theorems prove

```text
|(stars, deficit) = (0,0)| = 8
|(stars, deficit) = (1,0)| = 12
|(stars, deficit) = (2,0)| = 3
|(stars, deficit) = (2,1)| = 3
|(stars, deficit) = (3,2)| = 1.
```

`tripleLocalFibers_exhaustive` proves that the union of these five fibers is the entire
27-element local restriction space.  Thus the local bivariate enumerator is fully verified,
including the absence of an omitted state:

```text
8 + 12*z + 3*z^2 + 3*z^2*y + z^3*y^2.
```

The proofs use ordinary `decide`, so reduction is checked by the Lean kernel; `native_decide` is
not used.  The precise next frontier is to transport each ambient restriction on a three-element
support to `Fin 3 → Option Bool`, prove that pairwise-disjoint support transport and the outside
coordinates form a bijective product decomposition, and derive the coefficient identity for

```text
(8 + 12*z + 3*z^2 + 3*z^2*y + z^3*y^2)^G * (2+z)^(n-3G).
```

After selecting `z^(20*r)` terms with `y`-degree greater than `10*r`, compare the resulting exact
mass and the intact-only lower bound against the verified common-shallow upper bound.  No
P-versus-NP conclusion follows.

### Ambient restrictions now factor exactly into abstract triple states and outside states

The local coefficient table is now connected to the ambient restriction space by a genuine
finite equivalence.  `restrictionProductCode` records the restriction on each support subtype and
on the complement of the support union.  `restrictionProductCode_injective` proves that these
pieces determine the ambient restriction without any disjointness assumption.

For pairwise-disjoint three-element supports,
`restrictionProductCode_bijective_triples` proves surjectivity as well.  Its cardinal audit uses

```text
|supportUnion| = 3*G
3^n = (product over G blocks of 3^3) * 3^(n-3*G).
```

Thus independently chosen block states never hide a consistency constraint.  Each support subtype
is then reindexed by a chosen equivalence with `Fin 3`, yielding
`ambientRestrictionTripleProductEquiv`:

```text
Restriction n
  ≃ (Fin G → (Fin 3 → Option Bool))
      × ({outside coordinates} → Option Bool).
```

This closes the product-decomposition part of the generating-function frontier.  The precise next
step is to prove that, under this equivalence, ambient `stars` is the sum of the `tripleLocalStars`
values plus the outside star count, while the compatible deficit is the sum of the
`tripleLocalDeficit` values.  That weight-preservation theorem will justify coefficient extraction
from

```text
(8 + 12*z + 3*z^2 + 3*z^2*y + z^3*y^2)^G * (2+z)^(n-3G).
```

Only after that identity is kernel-checked should the `z^(20*r)`, `y`-degree `> 10*r` mass be
compared with the common-shallow upper bound.  No P-versus-NP conclusion follows.

### The ambient product equivalence preserves both generating-function weights

The exact product decomposition now carries the intended statistics without distortion.
`ambientTripleState` restricts an ambient assignment to one support subtype and transports it
along the chosen equivalence with `Fin 3`.  The reindexing proof
`tripleLocalStars_arrowCongr` shows that the arbitrary numbering does not affect the local live
count.  `ambientTripleState_stars` and `ambientTripleState_deficit` then identify the two local
weights with the ambient block's root-live cardinality and truth-compatible residual query
deficit at residual depth one.

For pairwise-disjoint triples, `ambient_stars_eq_triple_sum_add_outside` proves

```text
stars sigma
  = sum_g tripleLocalStars(local_g sigma)
      + number of live outside coordinates,
```

and `compatible_deficit_eq_triple_sum` proves

```text
sum_g compatibleResidualQueryDeficit(sigma,g,1)
  = sum_g tripleLocalDeficit(local_g sigma).
```

Finally, `ambientRestrictionTripleProductEquiv_apply` identifies these local and outside states
with the literal output of `ambientRestrictionTripleProductEquiv`, and
`ambientRestrictionTripleProductEquiv_preserves_weights` packages both identities directly on
that output.  Thus the bijection is now weight-preserving in both the `z` and `y` gradings; there
is no hidden consistency or reindexing penalty between ambient restrictions and the proposed
product enumerator.

The precise next frontier is the finite coefficient theorem: define a bivariate coefficient
enumerator for the product state space and prove, using the five checked local fibers and the
outside `2+z` factor, that its `(K,D)` fiber is the coefficient of

```text
(8 + 12*z + 3*z^2 + 3*z^2*y + z^3*y^2)^G * (2+z)^(n-3*G).
```

The first quantitative extraction should specialize to `K = 20*r` and sum `D > 10*r`, before
comparing that exact mass with the existing common-shallow upper bound.  No P-versus-NP
conclusion follows.

### Exact bivariate fibers now pass through the ambient product equivalence

The coefficient interface is now explicit on both sides of the product decomposition.
`compatibleDeficitFiber support K D` is the ambient set of restrictions with exactly `K` live
coordinates and exactly `D` units of truth-compatible residual deficit.  The corresponding
`tripleProductWeightFiber support K D` imposes the same two totals directly on the independent
triple states and the outside-coordinate state.

`compatibleDeficitFiber_card_eq_tripleProductWeightFiber_card` proves, for pairwise-disjoint
three-element supports,

```text
|compatibleDeficitFiber support K D|
  = |tripleProductWeightFiber support K D|.
```

The proof restricts `ambientRestrictionTripleProductEquiv` to the exact `(K,D)` fibers and proves
membership, injectivity, and surjectivity using the previously established two weight identities.
Thus the coefficient to be computed on the product space is now kernel-checked to be the exact
ambient restriction count, not merely a lower bound or an unproved generating-function proxy.

The precise next frontier is algebraic factorization of the product-space enumerator: define the
finite bivariate polynomial whose `(K,D)` coefficient is
`|tripleProductWeightFiber support K D|`, prove that independent `Fin G` coordinates multiply the
verified local factor

```text
8 + 12*z + 3*z^2 + 3*z^2*y + z^3*y^2,
```

and prove that the outside subtype contributes `(2+z)^(n-3*G)`.  Then specialize to `K = 20*r`,
sum coefficients with `D > 10*r`, and compare the resulting exact mass with the existing
common-shallow upper bound.  No P-versus-NP conclusion follows.

### The exact bivariate product enumerator now factors algebraically

The product count is now represented in `MvPolynomial (Fin 2) ℕ`, with coordinate `0` recording
the live count `z` and coordinate `1` recording the compatible deficit `y`.
`tripleLocalEnumerator_eq` derives the one-block polynomial from the five previously checked local
fibers, rather than installing the displayed formula as a definition:

```text
8 + 12*z + 3*z^2 + 3*z^2*y + z^3*y^2.
```

`outsideStateEnumerator_eq` proves that any finite outside reservoir contributes one `2+z` factor
per coordinate.  Finally, `tripleProductEnumerator_factorization` uses finite distributivity over
function spaces to prove the exact identity

```text
(8 + 12*z + 3*z^2 + 3*z^2*y + z^3*y^2)^G * (2+z)^(n-3*G).
```

The outside coordinates are canonically reindexed by `Fin (n-3*G)` in the polynomial definition;
the earlier disjoint-triple cardinal audit proves that this is exactly the cardinality of the
ambient outside subtype.  Thus the algebraic factor itself no longer depends on arbitrary support
labels.

The precise next frontier is coefficient extraction: prove that the coefficient of `z^K y^D` in
`tripleProductEnumerator G (n-3*G)` is the cardinality of
`tripleProductWeightFiber support K D`, using multiplication of weight monomials and an outside
subtype/`Fin (n-3*G)` reindexing.  Then specialize to `K = 20*r`, sum over `D > 10*r`, and compare
the exact mass with the existing common-shallow upper bound.  No P-versus-NP conclusion follows.

### Exact coefficient extraction now reaches ambient restriction fibers

The canonical algebraic enumerator now has a proved coefficient interpretation.
`tripleProductEnumerator_coeff` collapses each product of local weight monomials to one monomial
whose exponents are the total live count and total compatible deficit, then shows that extracting
`z^K y^D` counts exactly `tripleProductIndexWeightFiber G outsideCount K D`.

For disjoint three-element supports,
`tripleProductWeightFiber_card_eq_indexWeightFiber_card` explicitly reindexes the ambient outside
subtype by the order equivalence

```text
{i // i is outside all supports} ≃ Fin (n - 3*G).
```

The proof transports outside assignments in both directions and separately proves invariance of
the number of live outside coordinates.  Consequently,
`tripleProductEnumerator_coeff_eq_weightFiber_card` establishes

```text
[z^K y^D] tripleProductEnumerator G (n - 3*G)
  = |tripleProductWeightFiber support K D|,
```

and `tripleProductEnumerator_coeff_eq_compatibleDeficitFiber_card` composes this with the earlier
ambient product equivalence to obtain the exact ambient restriction count directly.

The precise next frontier is finite deficit-tail extraction: at `K = 20*r`, prove that the
cardinality of the union of exact fibers with `D > 10*r` is the corresponding finite sum of
coefficients of the factored polynomial.  Then compare that exact tail mass with the verified
common-shallow upper bound.  No P-versus-NP conclusion follows.

### The finite coefficient tail now meets the verified switching upper bound

The deficit grading has now been audited through its endpoint.  `tripleLocalDeficit_le_two` proves
that one width-three block contributes at most two units, and
`compatible_deficit_sum_le_two_mul` transports this to ambient restrictions.  Hence the semantic
tail is supported exactly on the finite degree set

```text
trunkDepth < D ≤ 2*G.
```

`compatibleDeficitShell_card_eq_sum_fibers` partitions the shell by its unique deficit degree.
Composing this with exact coefficient extraction gives
`compatibleDeficitShell_card_eq_coefficient_tail`, and its requested specialization proves

```text
|compatibleDeficitShell support (20*r) (10*r) 1|
  = sum_{10*r < D ≤ 2*G}
      [z^(20*r) y^D] tripleProductEnumerator G (n-3*G).
```

The comparison is no longer merely proposed.  For pairwise-disjoint, duplicate-free ordered
triples in the already verified linear-gap ambient scale `n = 1000*(3*G)*r`,
`orderedTriples_coefficient_tail_scaled_le_linearGap` proves

```text
(sum_{10*r < D ≤ 2*G} [z^(20*r) y^D] enumerator) * 2^(10*r)
  ≤ |{sigma : Restriction n | stars sigma = 20*r}|.
```

The proof passes through semantic common-shallow badness and applies the existing realized-prefix
density theorem with clause width three and one clause per gate.  An attempted direct use of the
older width-two linear-gap specialization was rejected because an ordered three-variable
conjunction is one clause of width three; the general density theorem is the sound interface.

This closes the exact-tail comparison for independent ordered triples, but not for general
overlapping circuit bottom gates.  The precise next frontier is to determine whether an arbitrary
normalized layered bottom family admits a sufficiently large disjoint width-three positive-clause
subfamily (or a fractional/packing replacement) whose coefficient-tail mass survives the passage
to the actual two-polarity family and iterated round schedule.  No P-versus-NP conclusion follows.

### Exact gate subfamilies transfer, but clause packings do not

The first passage from the ordered-triple model to a circuit family is now separated into a sound
interface and a false shortcut.  `CommonShallowAt.of_reindex` proves that a common trunk for a
large indexed family is also a common trunk for any family whose gates occur verbatim under an
arbitrary index map.  Dually, `commonShallowBad_subset_of_reindex` proves

```text
bad(exact packed gates) ⊆ bad(full family).
```

Injectivity is not required.  The specialized theorem
`compatibleDeficitShell_subset_commonShallowBad_of_orderedConjunctionBlocks_reindex` therefore
transfers the entire exact width-three deficit shell whenever the full normalized family contains
the packed singleton conjunction gates exactly.

The weaker condition that each packed clause merely occurs inside some larger DNF is insufficient.
`canonicalDT_depth_not_monotone_of_sublist` gives a kernel-checked one-variable counterexample:
the singleton positive clause has canonical depth one on the all-live root, but adjoining an empty
always-true term produces a containing clause list of depth zero.  Thus no argument may infer the
needed semantic lower bound from clause-list inclusion alone; extra terms can destroy it.

The precise next frontier is consequently sharper than generic clause packing: either extract a
large disjoint collection of **exact singleton width-three gates** from the normalized two-polarity
family, or prove a new gate-local lower bound that controls competing terms (possibly after a
restriction-dependent isolation step) and then combine that bound with a hypergraph or fractional
packing theorem.  Only after such a semantic isolation lemma is available does it make sense to
audit how much tail mass survives all rounds.  No P-versus-NP conclusion follows.

### Canonical endpoint relabeling and semantic quotienting do not repair the balance

The two most direct attempts to weaken exact gate packing have now been audited on the independent
singleton family, where every root and canonical prefix can be computed exactly.
`independentLiteral_prefixEndpoint_iff_existsUnique` characterizes a fixed endpoint by the unique
consumed set of live coordinates lying strictly before the residual endpoint.  Consequently
`independentFixedShellEndpointFiber_card` proves that its multiplicity is

```text
choose(|{i : i < every coordinate of E}|, d).
```

For the proportional shell `K = 2*d`, the maximum is exactly `choose(n-d,d)` and is attained by
the terminal residual `d`-set.  Moreover,
`independentBadEndpointFibers_aggregate_exact` proves that every such realized fiber is genuinely
in `commonShallowBad` at residual depth zero and that the fibers partition the full coordinate
shell.  The resulting exact identity in `independentOrderedFiberMaximum_exact_shell_count` shows
that multiplying the endpoint shell, the attained fiber maximum, and the desired `2^d` saving
exceeds the original restriction shell by

```text
choose(2*d,d) * 2^(2*d).
```

Thus endpoint-conditioned coordinate labels do not recover the missing contraction; the failure
already occurs on an exact semantic bad event, rather than in an overcount of unrealizable labels.

Semantic gate quotienting also fails at the present canonical-tree interface.
`orderedThreeLiteral_canonicalDT_ne` and `depthSensitive_canonicalDT_depth_ne` show that
semantically identical conjunctions with different literal orders can have different canonical
trees and even different canonical depths.  Retaining queried coordinates repairs decoding, but
`not_coordinateSemantic_exact_balance_half` proves that its `(n+1)^d` word alone destroys the
same half-shell balance.  Conversely, charging distinct live support plus ideal semantic excess
is too optimistic: `permutedThreeLiteral_no_alphabet_le_support_add_semanticExcess` gives six clean
ordered keys on three coordinates with zero semantic excess.

Finally, `distinctEssentialCoordinateBaseline_prefixEndpoint_ge_sub` isolates the structural
content that no relabeling can remove: a trunk of budget `d` leaves at least `q-d` of `q` distinct
live essential coordinates.  In particular,
`distinctEssentialCoordinateBaseline_no_switchingFactor_contraction_of_twice_budget_lt` rules out
the required switching-factor contraction whenever `2*d < q`.

The precise next frontier is therefore a circuit-structural restriction lemma, not another prefix
code: prove that a normalized layered bottom family either (i) contains enough restriction-isolated
exact width-three singleton gates to invoke the verified coefficient-tail obstruction, or (ii) has
its distinct live essential coordinates reduced to `O(d)` by a trunk of depth `d`, with the
remaining semantic-replica/component charge explicitly bounded.  Any proposed isolation step must
also control competing DNF terms, since clause inclusion alone is false.  Only after this dichotomy
is kernel-checked should the multi-round survivor schedule be revisited.  No P-versus-NP conclusion
follows.

### Restriction-isolated singleton gates now transfer exactly

The semantic isolation interface needed by the structural frontier is now kernel-checked.
`liveTermFilter_eq_singleton` proves that a duplicate-free gate has root-live filter exactly `[T]`
when `T` survives and every competing term is already falsified.  This is strictly stronger than
clause occurrence and explicitly excludes the preserved empty-term counterexample above.

`CommonShallowAt.of_reindex_liveFilter` then uses falsification monotonicity along every trunk leaf:
a full-family common-shallow certificate transfers to any reindexed family equal to the selected
gates' live filters at the root restriction.  The filter is chosen once at the root; terms killed
there remain killed throughout the trunk, so no restriction-dependent change of canonical tree is
hidden in the argument.

Finally, `mem_commonShallowBad_of_isolatedSingleton_reindex` gives the pointwise bad-event lift
needed for counting.  If a restriction is bad for selected singleton targets, and each target is
the unique live term of its chosen normalized full gate at that restriction, the same restriction
is bad for the full family.  Thus the earlier exact width-three coefficient-tail obstruction can
now be imported under a concrete isolation predicate rather than verbatim gate equality.

The precise next frontier is quantitative, not semantic: define and count a restriction shell on
which many pairwise-disjoint width-three targets are simultaneously unique-live terms of their
selected full gates.  This requires a packing or hitting-set bound for falsifying all competing
terms while preserving the targets and the fixed live-coordinate budget.  If such a shell cannot
be large, the alternative branch must turn that failure into an `O(d)` bound on distinct live
essential support with an explicit semantic-replica/component charge.  Only after that dichotomy is
proved should the multi-round survivor schedule be revisited.  No P-versus-NP conclusion follows.

### Restriction isolation requires inclusion-minimal targets

The first structural obstruction to the proposed unique-live shell is now kernel-checked.
`termFalsified_true_of_lits_subset` proves that if every literal of a competing term `U` occurs in
the target `T`, then any restriction falsifying `U` also falsifies `T`.  Its contrapositive,
`termFalsified_false_of_lits_subset`, says that preserving `T` necessarily preserves every such
weaker competitor.

Consequently, `not_lits_subset_of_isolatedSingleton` proves a necessary antichain condition for
the isolation interface: a uniquely live target cannot have a distinct competing term whose
literal list is contained in the target's literal list.  This obstruction is independent of
duplicate clauses and is therefore not repaired by `eraseDups`.  It also explains why a generic
hitting-set argument cannot begin from an arbitrary selected width-three clause: some competitors
cannot be hit without killing the target at all.

The precise next frontier is to separate normalized bottom-gate terms into inclusion-minimal
candidates and dominated targets.  For the minimal candidates, prove a quantitative packing or
hitting-set bound that falsifies competitors using literals outside each preserved target while
respecting the fixed-live shell budget.  If too few disjoint minimal width-three candidates exist,
the alternative branch must charge dominated targets to their minimal witnesses and turn the
result into the proposed `O(d)` live-essential-support/component bound.  Subsumption deletion
cannot simply be assumed to preserve canonical trees, so that route must be audited explicitly if
used.  No P-versus-NP conclusion follows.

### Subsumption deletion preserves semantics but not canonical depth

The proposed shortcut of deleting terms dominated by inclusion-minimal witnesses has now been
audited and rejected at the current canonical-tree interface.  `subsumptionRedundantGate` is the
ordered DNF

```text
(x₁ ∧ x₀) ∨ x₀,
```

with the stronger absorbed term placed first, while `subsumptionMinimalGate` is just `x₀`.
`subsumptionMinimal_lits_subset_redundant` verifies the literal inclusion responsible for
absorption.  More strongly, `subsumptionRedundantGate_anyTermSat` proves that the two gates have
the same `anyTermSat` value under **every partial restriction**, not merely every total assignment.

Nevertheless, on the all-live root with fuel two,
`subsumptionRedundantGate_depth_two` and `subsumptionMinimalGate_depth_one` compute canonical
depths two and one.  The combined theorem
`canonicalDT_depth_not_preserved_by_subsumption_deletion` therefore kernel-checks a semantic
equivalence whose canonical depth changes after subsumption deletion.  The cause is syntactic
order: the canonical procedure begins with the first term and queries its irrelevant `x₁` before
it can exploit the absorbing `x₀` term.

Thus inclusion-minimal reduction cannot be inserted before the existing switching encoder or
layered-collapse bridge merely from semantic equivalence.  The precise next frontier is to work
with inclusion-minimal targets **inside the original ordered gates**: quantify the outside literals
available in each non-dominated competitor and prove either a simultaneous restriction-isolation
packing bound, or a charging lemma showing that failure of such a packing bounds the original
gate's distinct live essential support/components by `O(d)`.  Any alternative normalization must
prove canonical-tree simulation with an explicit depth overhead rather than equality.  Only after
that dichotomy is kernel-checked should the multi-round survivor schedule be revisited.  No
P-versus-NP conclusion follows.

### Inclusion-minimal targets expose an outside literal in every competitor

The local combinatorial premise for the proposed isolation packing is now explicit and
kernel-checked without modifying the ordered gate.  `InclusionMinimalIn cs T` says that every term
of `cs` whose literal list is contained in `T.lits` is actually `T`.
`exists_outside_literal_of_inclusionMinimal` then proves that every distinct competitor `U`
contains a literal absent from `T`.  This is precisely the literal-level resource an isolation
restriction may try to falsify while preserving `T`.

Conversely, `inclusionMinimal_of_isolatedSingleton` proves that the existing unique-live
isolation predicate forces this inclusion-minimality.  Together with
`not_lits_subset_of_isolatedSingleton`, this shows the proposed target class is exact at the local
order-theoretic level: no uniquely live target is lost, and every remaining competitor supplies an
outside literal.  No subsumption deletion, term reordering, or semantic-to-canonical simulation is
assumed.

The precise next frontier is global compatibility.  For a packed family of minimal targets,
select one outside literal from every competitor and bound conflicts where a selected literal
belongs to another preserved target (or shares its variable with incompatible polarity).  Prove
either a large conflict-free selection whose falsifying assignments preserve all targets and fit
the fixed-live shell, or charge every selection failure to a bounded target-support/component
hitting set.  Only then can the verified isolated-singleton transfer and width-three coefficient
tail be applied.  No P-versus-NP conclusion follows.

### A compatible outside-literal selection now constructs simultaneous isolation

The positive branch of the global-compatibility frontier is now kernel-checked.
`GloballyCompatibleIsolationSelection` records the three exact obligations on one finite selected
literal list: literals selected on the same variable demand the same falsifying value; no selected
variable occurs in any preserved target (a polarity-sensitive strengthening of literal
non-membership); and every non-target competitor contains a selected literal.

`compatibleIsolationRestriction` turns such a list into a single restriction.  The proved lemmas
`compatibleIsolationRestriction_litFalse`, `compatibleIsolationRestriction_target_live`, and
`compatibleIsolationRestriction_competitor_falsified` show respectively that every selected
literal is forced false, every target remains entirely live, and every competitor is killed.
Finally, `mem_commonShallowBad_of_globallyCompatibleIsolationSelection` composes this construction
with the previously verified isolated-singleton transfer, lifting badness of the packed singleton
family to the unchanged full ordered family.

This removes the remaining semantic ambiguity from the positive branch: no further canonical-tree
simulation or restriction-construction lemma is needed once a compatible selection has been
found.  The precise next frontier is the finite combinatorics of existence and size.  Build the
competitor-versus-literal conflict hypergraph for inclusion-minimal targets and prove either a
large hitting selection satisfying the two compatibility conditions, with an explicit bound on
the number of fixed variables and resulting shell size, or extract from every failure a bounded
target-support/component hitting set.  The fixed-shell accounting is essential because the
constructed restriction itself need not lie on the intended shell without an additional free-set
extension/counting argument.  No P-versus-NP conclusion follows.

### The compatible-selection restriction now has exact shell accounting

The fixed-coordinate cost of the positive isolation construction is now kernel-checked rather
than inferred from the selected literal list.  `compatibleIsolationSelectedVars` is the finset of
variables occurring in the selection, and `freeVars_compatibleIsolationRestriction` proves the
exact identity

```text
freeVars(compatibleIsolationRestriction selected)
  = univ \ compatibleIsolationSelectedVars selected.
```

Consequently `stars_compatibleIsolationRestriction` gives

```text
stars = n - |selected variables|.
```

The supporting bounds `compatibleIsolationSelectedVars_card_le` and
`sub_le_stars_compatibleIsolationRestriction` show that a selection of length at most `q` fixes at
most `q` coordinates and hence leaves at least `n-q` stars.  When selected variables are duplicate
free, `stars_compatibleIsolationRestriction_eq_sub_length` identifies the shell exactly as
`n-selected.length`.  Repeated same-variable witnesses therefore cost no additional shell mass;
the relevant hypergraph cost is distinct selected variables, not literal occurrences.

This also sharpens the remaining gap.  A short compatible selection produces one high-star base
restriction, not by itself a large family on an arbitrary intended `K`-star shell.  The precise
next frontier is to define the competitor--outside-literal conflict hypergraph and prove either a
large compatible hitting selection with a bound on its **distinct-variable** support, together
with a counted extension of the resulting base restriction to the intended shell that preserves
target survival, or extract a bounded target-support/component hitting set from failure.  No
P-versus-NP conclusion follows.

### Target-preserving extension is feasible on the exact interval

The existence half of the intended-shell extension is now kernel-checked.  `keepFreeExtension`
retains an arbitrary chosen subset of the base-live coordinates, fixes every other formerly live
coordinate, preserves all earlier assignments, and has exactly as many stars as the chosen subset.
`compatibleIsolationTargetVars` records the distinct variables in all packed targets; global
compatibility proves that this entire support is live in the compatible-selection base.

The capstone
`exists_shell_extension_of_globallyCompatibleIsolationSelection'` proves that a compatible
selection extends to a target-preserving restriction on every `K`-star shell satisfying exactly

```text
|distinct target variables| ≤ K ≤ stars(compatible base).
```

Every target remains live and every competitor remains falsified.  Thus there is no additional
semantic or existence obstruction to moving the positive construction down to an intended shell.
The construction deliberately chooses one deterministic extension, so it does not yet supply the
large family required by a density lower bound.

The precise next frontier is now the exact fiber count: define all target-preserving `K`-star
extensions of a compatible base and prove their cardinality, expected to separate into a choice of
`K-|target support|` extra live variables and Boolean assignments to the remaining base-live
coordinates.  In parallel, the competitor--outside-literal conflict hypergraph must still produce
a compatible hitting selection with bounded distinct-variable support, or a bounded
target-support/component obstruction.  No P-versus-NP conclusion follows.

### The target-preserving shell-extension fiber has the exact binomial--Boolean count

The counting half of the intended-shell extension is now kernel-checked.  The finite family
`targetPreservingShellExtensions base required K` contains every restriction that extends `base`,
has exactly `K` stars, and keeps the complete required target support live.
`card_restrictionExtends_freeVars_eq` first proves that, for a prescribed final free set `S` inside
the base-live coordinates, the extension fiber has exactly

```text
2^(|freeVars base| - |S|)
```

members: old fixed coordinates are forced, coordinates in `S` remain live, and every other
base-live coordinate receives either Boolean value.  `card_targetSuperset_freeSets` separately
counts the admissible `K`-element free sets containing `required`.  The capstone
`targetPreservingShellExtensions_card` combines the two partitions to give the exact formula

```text
choose(|freeVars base| - |required|, K - |required|)
  * 2^(|freeVars base| - K).
```

Thus the positive isolation branch loses no unaccounted shell mass after a compatible base is
found: the binomial factor chooses the extra live variables beyond the targets, while the Boolean
factor counts assignments to the remaining formerly live coordinates.  The deterministic
`keepFreeExtension` from the preceding milestone is one member of this complete fiber.

The precise next frontier is no longer extension feasibility or counting.  Construct the finite
competitor--outside-literal conflict hypergraph for inclusion-minimal targets and prove either a
compatible hitting selection with bounded **distinct-variable** support, so that the exact fiber
above supplies its shell mass, or extract from selection failure a bounded target-support or
component hitting set.  That dichotomy is the remaining structural input before the isolated
width-three coefficient tail can be applied to general normalized bottom families.  No
P-versus-NP conclusion follows.

### Empty competitor edges give an explicit target-support obstruction

The first negative branch of the competitor conflict hypergraph is now kernel-checked.
`competitorOutsideTargetVars target U` is the finite set of variables occurring in a competitor
`U` after deleting the union of all preserved-target supports.  The theorem
`not_exists_globallyCompatibleIsolationSelection_of_outsideTargetVars_eq_empty` proves that if
this edge is empty, no globally compatible isolation selection exists: hitting `U` would require
fixing a variable that global compatibility must leave live for a target.

This obstruction is not ruled out by local inclusion-minimality.
`exists_targetSupport_conflict_of_inclusionMinimal_of_outsideTargetVars_eq_empty` combines an
empty edge with an inclusion-minimal target to extract a literal that is outside its own target
but shares a variable with some preserved target.  Thus the earlier local outside-literal lemma
does not by itself feed the positive selection branch; cross-target support is a genuine failure
mode, now retained as a proved certificate rather than an informal caveat.

The precise next frontier is to form the family of all **nonempty** competitor edges after target
support deletion and solve its remaining two constraints together: choose a bounded-size
distinct-variable transversal, and choose polarities consistently whenever several edges use the
same variable.  Failure should yield either many empty-edge target-support certificates (now
formalized) or a bounded component/polarity-conflict hitting set.  Only after that dichotomy is
quantified should the exact shell-extension fiber be combined with the isolated width-three
coefficient tail.  No P-versus-NP conclusion follows.

### Nonempty edges split cleanly at the polarity constraint

The literal-level conflict pool and both sides of its first dichotomy are now kernel-checked.
`outsideTargetLiteralPool` retains every full-family literal whose variable avoids the complete
preserved-target support.  Its membership theorem identifies these occurrences exactly, without
discarding their polarity as `competitorOutsideTargetVars` does.

The positive capstone
`exists_globallyCompatibleIsolationSelection_of_nonempty_edges_of_pool_consistent` proves that if
every competitor variable edge is nonempty and all occurrences of a shared variable in this pool
have the same falsifying value, then selecting the complete pool is a globally compatible
isolation selection.  This construction is intentionally nonminimal: it settles existence while
leaving the distinct-variable transversal bound visible as the quantitative task.

The negative capstone
`not_exists_globallyCompatibleIsolationSelection_of_singleton_polarity_conflict` proves that two
singleton competitor edges demanding different falsifying values on the same variable rule out
every globally compatible selection.  Therefore nonempty edges alone are insufficient even after
all target-support conflicts have been deleted.  The obstruction is intrinsically polarity-aware,
not an artifact of the restriction construction.

The precise next frontier is to replace the strong whole-pool consistency condition by a bounded
polarity-consistent transversal theorem.  Model each outside variable with its two possible
falsifying orientations and prove either a small oriented hitting set for all competitor edges or
extract a bounded unsatisfiable component generalizing the proved two-singleton conflict.  The
bound must count distinct variables so it composes with the exact target-preserving shell fiber.
No P-versus-NP conclusion follows.

### The oriented-transversal existence problem is exactly Boolean clause satisfiability

The proposed polarity-aware transversal has now been reduced to its exact assignment semantics.
`HitsOutsideCompetitors` gives every variable a Boolean orientation and requires each competitor
to contain an outside-target literal whose falsifying value matches that orientation.  The
capstone
`exists_globallyCompatibleIsolationSelection_iff_exists_hitsOutsideCompetitors` proves

```text
(∃ globally compatible isolation selection)
  ↔ (∃ Boolean assignment hitting every outside-target competitor clause).
```

Forward, the consistent partial assignment carried by a selection is extended arbitrarily on
unselected variables.  Reverse, all available literal occurrences matched by a hitting assignment
form a compatible selection.  Target-support deletion is built into both sides.  Empty edges and
the previously proved opposite singleton pair are therefore the first two unsatisfiable instances
of this exact clause system, not the complete list of possible obstructions.

This changes the defensible frontier.  Nonempty edges, bounded clause width, and polarity-aware
language alone do not supply the desired positive selection or a constant-size unsatisfiable
component; the missing statement is a satisfiability assertion and needs additional structure
from the way targets and competitors arise.  The precise next frontier is to identify and prove
such structure—for example by choosing the packed targets jointly with the orientation assignment,
or by proving a quantitative lower bound on hitting assignments averaged over target choices—and
then bound the distinct matched-variable support before applying the exact shell-extension fiber.
A generic oriented-transversal lemma should not be assumed.  No P-versus-NP conclusion follows.

### Joint target choice also fails under the current local hypotheses

The first proposed source of extra structure has been tested at its smallest instance.
`oppositeSingletonGate` is the normalized width-one gate

```text
[x], [¬x].
```

The kernel-checked theorem `oppositeSingletonGate_nodup_width_one` records that the gate is
duplicate-free, every term is literal-duplicate-free, and every term has width exactly one.  The
capstone `oppositeSingleton_no_joint_target_isolation` proves that there is nevertheless no choice
of a member target together with a globally compatible isolation selection.  Preserving either
singleton protects the only variable, while falsifying the other singleton requires fixing that
same protected variable.  Thus choosing targets jointly with orientations is not a generic repair,
even for one clean gate of width one; the empty-edge obstruction can persist for every target.

This rules out another hypothesis-free route without weakening or deleting the counterexample.
The precise next frontier is to characterize a circuit-derived condition that excludes unavoidable
opposite-polarity support conflicts (or to stratify and charge gates exhibiting them), and only
then test an averaged target-choice bound on that restricted class.  Any positive theorem must
state this extra structure explicitly before bounding matched-variable support and invoking the
exact shell-extension fiber.  No P-versus-NP conclusion follows.

### The minimal isolation obstruction is already residual-depth one

The semantic status of the preserved counterexample is now kernel-checked rather than inferred
from its syntax.  `complementarySingleton_canonicalDT_depth_le` proves, for every variable in every
ambient dimension, every restriction, and every fuel budget, that the canonical tree of

```text
[x_i], [¬x_i]
```

has depth at most one.  If the variable is fixed, one singleton is already satisfied; if it is
live, the canonical procedure queries it once and both children terminate immediately.

The capstone `oppositeSingletonFamily_commonShallowAt_one` upgrades this pointwise fact to the exact
multi-switching interface: for every root restriction and every allowed trunk budget, the
one-gate counterexample has a zero-query common trunk with residual depth one.  Consequently the
same family simultaneously has no joint target/isolation selection and is never in the
residual-depth-one bad event.  Isolation failure is therefore strictly stronger than failure of
the switching conclusion, and charging all conflict gates as bad would overcount even at the
smallest instance.

The precise next frontier is to stratify the conflict analysis by actual residual canonical depth:
remove gates already at the target depth, then ask whether every genuinely deep normalized gate
admits a target avoiding unavoidable support conflicts, or whether a deep conflict certificate can
be quantitatively charged to the canonical path that witnesses depth.  Only such a depth-sensitive
dichotomy should be combined with averaged target choice and the exact target-preserving shell
fiber.  No P-versus-NP conclusion follows.

### Genuine residual depth does not restore target isolation

The positive half of the proposed depth-sensitive dichotomy has now been tested and falsified at
the smallest next dimension.  `exhaustiveTwoBitGate` consists of the four width-two minterms on two
variables.  The kernel-checked theorem `exhaustiveTwoBitGate_nodup_width_two` records that its term
list is duplicate-free and every term uses two distinct variables.  At full freedom and fuel two,
`exhaustiveTwoBitGate_canonicalDT_depth_eq_two` proves that its canonical tree has depth exactly
two.

This is genuine switching badness at the target cutoff, not just root depth in isolation:
`exhaustiveTwoBitFamily_not_commonShallowAt_one` proves that no zero-query common trunk can leave
residual depth at most one, and `allFreeTwo_mem_exhaustiveTwoBit_commonShallowBad_one` places the
fully live restriction in the exact two-star bad event.  Nevertheless,
`exhaustiveTwoBit_no_joint_target_isolation` proves that no member target admits a globally
compatible isolation selection.  Every possible target protects both variables, while every
distinct competitor is supported on those same protected variables.

Thus deleting gates already shallow at the target depth still does not make target isolation a
generic positive branch.  The surviving route is the other half of the dichotomy: define a
canonical-path charge for deep support-conflict certificates.  The exhaustive square suggests the
right first local statement: a depth-two witness supplies an ordered pair of queried coordinates
that covers its four target-conflict patterns.  The precise next frontier is to formalize the
query-path/support-conflict incidence map and prove a bounded-fiber charge (or find a deeper
counterexample where conflicts cannot be assigned to the witnessing path).  Only after that local
map exists should its multiplicity be compared with the exact target-preserving shell fiber.  No
P-versus-NP conclusion follows.

### The first conflict-to-query incidence fiber is exact but already term-quadratic

The proposed local charge has now been instantiated and counted on the exhaustive square.
`exhaustiveTwoBitGate_queriedVars_eq_univ` proves that the canonical tree queries exactly the two
coordinates used by its four minterms.  `exhaustiveTwoBitConflictIncidences` records an ordered
target--competitor pair together with a coordinate occurring in both terms and in that queried set.

The exact counts expose the multiplicity rather than hiding it in a qualitative charge.
`exhaustiveTwoBitConflictIncidences_card` gives 24 incidences: there are 12 distinct ordered term
pairs and both coordinates witness every pair.  More sharply,
`exhaustiveTwoBitConflictIncidences_coordinate_fiber_card` proves that each queried coordinate has
fiber exactly 12.  Thus a canonical-query charge exists for this deep obstruction, but its naive
coordinate projection already pays the full `m*(m-1)` ordered-pair factor at `m = 4`; depth alone
does not force a constant fiber.

The precise next frontier is to generalize this audit to the `d`-variable exhaustive-minterm gate
and prove the expected coordinate fiber `2^d * (2^d - 1)`, or find a more selective conflict
certificate whose fiber is only linear (or better) in the term count while still certifying every
isolation failure.  Only the latter kind of compression could improve on charging all ordered
competitors before comparison with the existing term-key and shell-extension factors.  No
P-versus-NP conclusion follows.

### The complete incidence fiber is generically quadratic

The dimension-free combinatorial core of the proposed generalization is now kernel-checked.
`offDiagonalTermPairs_card` proves that an `M`-term gate has exactly `M*(M-1)` distinct ordered
target--competitor pairs.  `completeConflictQueryIncidences_card` forms the complete relation with
`d` queried coordinates and proves its size is `M*(M-1)*d`.  More sharply,
`completeConflictQueryIncidences_coordinate_fiber_card` proves that projection to every individual
coordinate has fiber exactly `M*(M-1)`.

The specialization `exhaustiveMinterm_completeConflict_coordinate_fiber_card` sets `M = 2^d` and
obtains the expected `2^d*(2^d-1)` coordinate fiber.  This theorem isolates the exact counting
content of the exhaustive-minterm example: once every ordered competitor and every queried
coordinate are retained, the quadratic loss is forced for every dimension, rather than being an
artifact of the four-term square.  The existing concrete two-bit construction supplies the
semantic realization at `d = 2`; a generic exhaustive-gate/canonical-tree realization has not been
claimed here.

The precise next frontier is therefore certificate compression, not another count of the complete
relation.  Define a selective conflict certificate that still witnesses every failed isolation
target but retains only one canonical competitor or one canonical conflicting coordinate per
target, then test whether its coordinate fibers are `O(M)` on exhaustive minterms and whether the
selection remains sound for arbitrary genuinely deep normalized gates.  If no such sound selector
exists, preserve the smallest counterexample and quantify its unavoidable multiplicity.  No
P-versus-NP conclusion follows.

### One-witness certificate counting is linear; semantic selection is the remaining gap

The counting half of certificate compression is now kernel-checked independently of any
unproved selector.  `selectiveConflictQueryIncidences` retains one chosen competitor and one chosen
queried coordinate for each of `M` targets.  Because the target index remains in the certificate,
`selectiveConflictQueryIncidences_card` proves that the resulting relation has exactly `M`
elements, and `selectiveConflictQueryIncidences_coordinate_fiber_card_le` proves that every
coordinate fiber has size at most `M`.  Finally,
`selectiveConflictQueryIncidences_subset_complete` proves that distinct chosen competitors make
this a genuine subrelation of the complete quadratic incidence relation.

Thus the quadratic fiber is not an unavoidable consequence of recording a conflict witness: it
comes from retaining every ordered competitor.  A one-witness-per-target representation has the
desired linear multiplicity even before using exhaustive-minterm structure.  This does **not** yet
give a sound switching charge.  The missing semantic theorem must construct the two selector
functions from a genuinely deep normalized gate and prove that each chosen coordinate lies on the
relevant canonical query path and witnesses the failed isolation target.  Global incompatibility
may also require a certificate richer than independent local choices, as the preserved polarity
counterexamples warn.

The precise next frontier is to formulate that selector-validity predicate against the existing
`GloballyCompatibleIsolationSelection` failure condition, then prove existence for exhaustive
minterms as the first semantic model.  After that, test whether arbitrary genuinely deep
normalized gates admit the same selector or preserve the smallest obstruction showing that a
cycle/global certificate is necessary.  No P-versus-NP conclusion follows.

### The exhaustive obstruction has a sound linear selector

The missing semantic interface is now explicit.  `SelectiveConflictSelectorValid` requires, for
each indexed target, a distinct member competitor whose complete support lies inside that target's
protected support, together with a shared coordinate that is actually queried by the canonical
tree.  The support condition is stated as an empty `competitorOutsideTargetVars` edge, so the
bridge theorem `SelectiveConflictSelectorValid.no_singleton_target_isolation` feeds it directly
to the existing `GloballyCompatibleIsolationSelection` obstruction rather than treating overlap
as a surrogate for failed isolation.

The first semantic model succeeds.  `exhaustiveTwoBitSelectiveCompetitor` pairs every minterm with
its bitwise opposite and `exhaustiveTwoBitSelectiveCoordinate` retains coordinate zero.  The
kernel-checked theorem `exhaustiveTwoBit_selectiveConflictSelectorValid` proves membership,
clause and index distinctness, empty outside support, shared support, and canonical-query
incidence for all four targets.  The associated selective incidence set has exactly four elements
by `exhaustiveTwoBit_selectiveConflictQueryIncidences_card`, versus twenty-four in the complete
relation.  Thus certificate compression is semantically sound, not merely combinatorially
possible, on the exhaustive depth-two gate.

This predicate intentionally captures the local empty-edge obstruction, not every failure of
global isolation.  The already preserved opposite-polarity example shows that nonempty competitor
edges can instead fail through inconsistent orientations.  The precise next frontier is therefore
to build the smallest genuinely deep normalized gate whose isolation failure has no empty edge,
and test whether its polarity obstruction admits an `O(M)` cycle certificate tied to canonical
queries.  If such a deep example does not exist at the smallest dimensions, prove the restricted
dichotomy: a deep failed target has either a valid local selector or a bounded polarity-cycle
selector.  No P-versus-NP conclusion follows.

### A depth-two nonempty-edge obstruction has a two-incidence polarity certificate

The local-selector/global-cycle split is now witnessed inside one genuinely deep normalized
gate.  `deepPolarityCycleGate` is the ordered three-term DNF
`x₀ ∨ (¬x₀ ∧ x₁) ∨ (¬x₀ ∧ ¬x₁)`.  It is duplicate-free, repeats no variable inside a term, has
width at most two, and every term is inclusion-minimal in the unchanged gate.  At the all-free
root with fuel two its canonical tree has exact depth two and queries both coordinates.

Preserving the first term protects coordinate zero.  The two proper competitors then have exact
outside-support edges `{1}` and `{1}`; in particular every competitor edge is nonempty, so the
empty-edge `SelectiveConflictSelectorValid` branch is unavailable.  Nevertheless
`deepPolarityCycle_no_target_isolation` proves that no globally compatible isolation selection
exists: the two competitors force selection of `x₁` with opposite falsifying values.  This is a
polarity obstruction at the same residual-depth threshold used by the switching bad event, not
the previously audited depth-one complementary-singleton artifact.

The concrete cycle compresses to `deepPolarityCycleIncidences = {(1,1),(2,1)}`.  Its exact card is
two, at most the three-term gate length, and `deepPolarityCycleIncidences_valid` checks both that
the retained coordinate is canonically queried and that the two outside literals demand opposite
values.  Thus the first deep nonempty-edge test admits an `O(M)` semantic cycle certificate.

The precise next frontier is to replace this concrete two-edge witness by a general
polarity-cycle validity predicate over nonempty outside-target clauses, prove that any valid cycle
rules out `GloballyCompatibleIsolationSelection`, and test the restricted dichotomy on arbitrary
deep normalized gates: either an empty-edge selector exists or an unsatisfiable outside-literal
instance yields a cycle certificate whose size can be charged linearly to canonical queries.
General unsatisfiable clause families need not have short two-edge cores, so no global linear
bound is claimed yet.  No P-versus-NP conclusion follows.

### Polarity-cycle soundness is now abstract and kernel-checked

The concrete two-edge calculation has been lifted to a reusable semantic interface.
`HitsOutsideCompetitorCore` states that one Boolean orientation hits every retained competitor
through a literal outside the complete preserved-target support.  `PolarityCycleValid` packages a
finite nonempty core of genuine proper competitors, requires each outside edge to be nonempty and
contained in a recorded canonical-query support, and requires the retained outside-clause system
to be unsatisfiable.  The query-support field is deliberately quantitative bookkeeping; the
soundness argument itself uses only the exact unsatisfiability condition.

The theorem
`PolarityCycleValid.not_exists_globallyCompatibleIsolationSelection` proves that every such core
blocks the existing compatible-isolation interface.  Its proof factors through the already exact
selection--orientation equivalence: a compatible literal selection would extend to a total
orientation hitting all competitors, hence the retained core, contradicting validity.  This is a
general obstruction theorem, not a restatement specialized to opposite singleton clauses.

`deepPolarityCycleCore` instantiates the predicate with the two proper competitors of the
three-term depth-two gate.  `deepPolarityCycle_polarityCycleValid` checks that both nonempty
outside edges lie on the canonical query support and that their opposite demands make the core
unsatisfiable.  The core has exact cardinality two, bounded by the gate's three terms, and
`deepPolarityCycle_no_target_isolation_via_cycle` recovers the earlier hand proof through the new
generic theorem.  The hand proof and concrete incidence audit remain preserved as independent
checks.

The remaining issue is now cleanly quantitative rather than semantic soundness.  The precise next
frontier is to define the full finite outside-competitor core for an arbitrary packed target family
and prove a completeness theorem: when all outside edges are nonempty, failure of compatible
isolation yields an unsatisfiable core.  Then audit its cardinality and, crucially, whether a core
can be reduced or charged so that its outside variables lie on the relevant canonical query paths
with only linear multiplicity across all packed targets.  A short two-clause core is not assumed in
general, and no P-versus-NP conclusion follows.

### The target-preserving extension fiber has an exact shell balance

The shell-extension feasibility argument has now been upgraded to an exact finite count.
`targetPreservingShellExtensions_card` proves that if a compatible isolation base has `B` live
coordinates, the union of protected target supports has size `R`, and `R ≤ K ≤ B`, then the
number of `K`-star extensions that keep every protected coordinate live is exactly

```text
choose(B - R, K - R) * 2^(B - K).
```

The new capstone `targetPreservingShellExtensions_exact_balance` relates that fiber to the full
base-extension shell without division:

```text
choose(B,R) * fiber = choose(B,K) * choose(K,R) * 2^(B-K).
```

Thus the exact target-preservation density inside the `K`-live extension shell is the binomial
ratio `choose(K,R) / choose(B,R)`.  This replaces the previous existence-only extension with the
sharp stars-and-bars multiplicity and shows precisely how total distinct target support, rather
than the raw number of target terms, consumes shell mass.  It does not yet show that enough packed
targets admit compatible isolation, nor that polarity cores have a linear canonical-path charge.

The precise next frontier is to combine this density with a complete full outside-competitor core:
prove that nonempty-edge isolation failure is exactly unsatisfiability of the full finite clause
system, then compare the smallest sound core/charge multiplicity against the newly exact
`choose(K,R) / choose(B,R)` preservation factor.  No short-core or linear-charge theorem is
assumed, and no P-versus-NP conclusion follows.

### Isolation failure is exactly full-core unsatisfiability

The full finite clause system is now explicit and kernel-checked. `fullOutsideCompetitorCore`
contains exactly the indexed pairs `(g,U)` for which `U` is a proper competitor of the preserved
target `target g` in gate `large (e g)`; duplicate occurrences inside a gate are erased because
they do not change satisfiability, while the target index remains part of the clause identity.
`mem_fullOutsideCompetitorCore` proves this membership characterization exactly.

`hitsOutsideCompetitorCore_full_iff_hitsOutsideCompetitors` proves that a Boolean orientation hits
this finite core exactly when it hits every proper competitor in the earlier quantified
interface.  Composing with the existing selection--orientation equivalence gives both
`exists_globallyCompatibleIsolationSelection_iff_fullCore_satisfiable` and its failure form
`not_exists_globallyCompatibleIsolationSelection_iff_fullCore_unsatisfiable`.  The logical
equivalence is stronger than the requested nonempty-edge statement: no edge hypothesis is needed,
because an empty outside edge is already a one-clause unsatisfiable obstruction.

Finally, `fullOutsideCompetitorCore_polarityCycleValid_of_failure` proves completeness for the
existing polarity-cycle interface.  If every proper competitor edge is nonempty, every such edge
lies in the recorded canonical-query support, and isolation fails, then the full competitor core
is a valid `PolarityCycleValid` certificate.  The theorem explicitly retains all competitors and
therefore makes no short-core or linear-charge claim.

The precise next frontier is quantitative core reduction.  Define an inclusion-minimal
unsatisfiable subcore of the full system, prove the best unconditional cardinality bound available
from its outside-variable support (the generic finite-variable bound may already be exponential),
and audit coordinate incidence multiplicity against the exact preservation density
`choose(K,R) / choose(B,R)`.  A linear canonical-path charge must be proved rather than inferred
from finiteness or minimality.  No P-versus-NP conclusion follows.

### Minimal polarity cores have only an exponential generic support bound

`InclusionMinimalUnsatisfiableCore` now records exactly the finite minimality needed here: the core
is unsatisfiable, but deleting any one indexed competitor leaves a satisfiable system.
`exists_inclusionMinimalUnsatisfiableCore_subset` proves by strict finite-set descent that every
unsatisfiable full core contains such a subcore.

Minimality supplies a canonical counting argument, but not a linear one.  Choose for every retained
competitor an assignment satisfying the core with that competitor deleted.  Witness assignments
for two distinct competitors cannot agree: agreement would make either witness also hit its one
missing competitor and hence satisfy the entire core.  The resulting injection proves
`InclusionMinimalUnsatisfiableCore.card_le_two_pow`, namely

```text
core.card <= 2^n.
```

More importantly for the canonical-query interface,
`InclusionMinimalUnsatisfiableCore.card_le_two_pow_queried` restricts each witness to the recorded
query support.  If every outside edge is contained in `queried`, the restricted witnesses remain
injective, giving the sharper exact-support bound

```text
core.card <= 2^(queried.card).
```

Finally, `exists_minimalPolarityCycleValid_card_le_two_pow_queried` composes finite descent with the
full-core completeness theorem.  Under the established nonempty-edge and query-support hypotheses,
every isolation failure has a valid inclusion-minimal polarity certificate contained in the full
core and satisfying the support-exponential bound.

This resolves the best immediate consequence of minimality and exposes a quantitative mismatch:
the preservation benefit is the binomial ratio `choose(K,R) / choose(B,R)`, while generic core
reduction still permits `2^Q` retained clauses for `Q = queried.card`.  Thus neither finiteness nor
inclusion-minimality justifies a linear canonical-query charge.

The precise next frontier is to define the minimal core's query-incidence relation and test whether
the canonical construction supplies structure absent from arbitrary minimally unsatisfiable CNFs:
either prove a per-coordinate or aggregate incidence bound strong enough to coexist with
`choose(K,R) / choose(B,R)`, or construct a canonical-gate family realizing exponential minimal-core
multiplicity and record that obstruction.  No P-versus-NP conclusion follows.

### Minimal-core query incidence remains exponential in the generic audit

`polarityCoreQueryIncidences` now records the exact retained-clause--coordinate relation of a
polarity core: a pair is present only when the clause belongs to the reduced core, the coordinate
belongs to the canonical query support, and the coordinate occurs in that clause's outside-target
edge.  This is the incidence object requested by the preceding frontier, rather than the earlier
complete all-target/all-competitor relation.

The generic rectangle bounds are now kernel-checked.  The aggregate incidence cardinality is at
most `core.card * queried.card`, and every individual coordinate fiber has cardinality at most
`core.card`.  Combining the aggregate bound with
`InclusionMinimalUnsatisfiableCore.card_le_two_pow_queried` gives

```text
|polarityCoreQueryIncidences target core queried|
  <= 2^(queried.card) * queried.card.
```

Thus merely passing from core cardinality to its actual query-incidence relation does not recover
a linear charge: the best unconditional aggregate estimate still carries the exponential
minimal-core factor.  The per-coordinate statement is useful bookkeeping, but it inherits the
same possible `2^Q` multiplicity.

The precise next frontier is structural rather than definitional.  Either prove that polarity
cores arising from canonical gate walks admit a selector or ownership map with total multiplicity
compatible with `choose(K,R) / choose(B,R)`, or construct a canonical normalized gate family whose
minimal-core incidence saturates a superlinear or exponential lower bound.  Generic rectangle
counting and minimality alone cannot decide between these routes, and no P-versus-NP conclusion
follows.

### The fixed exhaustive-core route is now source-audited

The latent `exhaustiveThreeProtectedGate` block had been appended after the namespace carrying
the required `Depth3` and `SwitchingCounting` opens had closed.  More seriously, its claimed
minimality theorem used `by decide` on a proposition for which Lean could not synthesize a
`Decidable` instance.  A clean source compilation therefore exposed `sorryAx` in the reported
capstone.  The invalid minimality and polarity-validity declarations have been removed rather
than treated as evidence; the concrete construction itself is preserved.

What remains kernel-checked is still useful.  The gate contains all eight polarity patterns on
three outside coordinates and a protected singleton target on a fourth coordinate.  It is
duplicate-free, has no repeated coordinate within a clause, has width three, and its canonical
tree queries exactly the three outside coordinates.  Its displayed eight-element core is exactly
the full proper-competitor core.  The full unweighted incidence relation has size `2^3 * 3`, and
`exhaustiveThreeProtectedCore_queryIncidences_coordinate_fiber_card` proves that each actually
queried coordinate has exactly `2^3` incident full-core clauses.

These full-core counts show that normalization and canonical querying do not make the raw
incidence rectangle sparse.  They do **not** yet refute a low-multiplicity ownership map on a
reduced valid core: source-checked unsatisfiability and inclusion-minimality of this concrete core
are precisely the missing facts.  Nor can one fixed `Q = 3` instance establish asymptotic
exponential growth.

The precise next frontier is first to prove the eight-clause core's unsatisfiability and
one-deletion satisfiability without computational shortcuts that introduce forbidden axioms.
Only then should the construction be parameterized over arbitrary `Q`, with separate proofs that
the canonical tree queries all `Q` outside coordinates and that every coordinate fiber has
cardinality `2^Q`.  No P-versus-NP conclusion follows.

### The fixed exhaustive core is constructively inclusion-minimal

The missing semantic facts for the normalized three-coordinate obstruction are now
source-checked.  `exhaustiveThreeProtectedCore_unsatisfiable` splits directly on the three
outside Boolean values and shows that the matching exhaustive competitor has no falsified
literal.  It does not invoke `decide` on the higher-order satisfiability proposition.

`exhaustiveThreeProtectedCore_inclusionMinimal` supplies all eight deletion witnesses explicitly:
after removing a polarity pattern, the corresponding satisfying assignment hits every other
competitor.  Thus the earlier failed `by decide` route has been replaced by a constructive proof,
not reinstated as an opaque computational claim.

The result is connected to the quantitative interface in two ways.
`exhaustiveThreeProtectedCore_polarityCycleValid` proves that this same core is a valid polarity
certificate for the normalized canonical gate, and
`exhaustiveThreeProtectedCore_card_eq_two_pow_queried` proves the exact equality

```text
core.card = 2^(queried.card) = 2^3.
```

Together with the existing incidence theorems, the fixed example now genuinely realizes an
inclusion-minimal valid core with 24 clause-coordinate incidences and eight clauses in every
queried-coordinate fiber.  This closes the logical gap in the fixed obstruction.  It still does
not establish an asymptotic lower bound: one instance at `Q = 3` cannot rule out a different
uniform ownership theorem or prove exponential growth over arbitrary support sizes.

The precise next frontier is to parameterize the exhaustive competitor family over arbitrary
`Q`.  The most informative order is: define clauses from Boolean vectors on `Fin Q`; prove
unsatisfiability and one-deletion satisfiability by the matching-vector argument; then prove the
chosen list ordering makes the canonical tree query every outside coordinate and derive exact
core and coordinate-fiber cardinalities `2^Q`.  No P-versus-NP conclusion follows.

### The exhaustive minimal core is now parameterized over arbitrary support

`exhaustiveVectorClause` encodes each Boolean vector `a : Fin Q → Bool` as the ordered width-`Q`
clause whose literal on coordinate `i` has falsifying value `a i`.  The final coordinate is
reserved for the disjoint protected target.  Clause injectivity is proved from the ordered
`List.ofFn` representation, so `exhaustiveVectorCore` contains exactly one indexed competitor per
Boolean vector and

```text
exhaustiveVectorCore Q |>.card = 2^Q.
```

The semantic obstruction is uniform in `Q`.  Given any proposed hitting assignment, its
pointwise opposite vector indexes a clause with no falsified literal, proving unsatisfiability.
After deleting the clause indexed by `a`, the pointwise complement of `a` hits every remaining
clause at a coordinate where its index differs from `a`.  Consequently
`exhaustiveVectorCore_inclusionMinimal` proves inclusion-minimal unsatisfiability for every `Q`,
including the empty-support boundary case.

This establishes the asymptotic combinatorial lower-bound family that the fixed `Q = 3` audit
could not supply: inclusion-minimal outside-competitor cores can genuinely attain `2^Q` clauses
for arbitrarily large outside support.  It does not yet establish the stronger canonical-gate claim.
The new core is represented by valid depth-3 clauses and a protected target, but no theorem yet
shows that one uniform enumeration of those clauses makes `canonicalDT` query exactly all `Q`
outside coordinates, nor that its canonical query-incidence fibers have size `2^Q`.

The precise next frontier is to define a recursion-compatible ordering of the Boolean-vector
clauses, prove by induction on `Q` that its canonical tree queries the entire embedded `Fin Q`
support, and then connect `exhaustiveVectorCore` to that gate's full competitor core.  The exact
per-coordinate incidence theorem should follow once that support equality is available.  No
P-versus-NP conclusion follows.

### The arbitrary-support core is now realized by a concrete full competitor gate

`exhaustiveVectorGate Q` lists every Boolean-vector clause once and then appends the protected
target; `exhaustiveVectorFamily Q` packages it as the one-gate family required by the polarity
interface.  The representation theorem `exhaustiveVectorCore_eq_full` proves that the previously
constructed abstract core is exactly this gate's full proper-competitor core.  Thus the
asymptotic obstruction is no longer merely a collection of valid clauses detached from a gate.

The outside-edge and incidence calculations are also exact without assuming anything about the
canonical walk.  For every vector clause, `competitorOutsideTargetVars` is precisely the embedded
copy of `Fin Q`.  Consequently `exhaustiveVectorCore_queryIncidences_eq_product` identifies the
incidence relation with the complete core-by-support rectangle and proves

```text
|incidences| = 2^Q * Q,
|coordinate fiber i| = 2^Q.
```

For `Q > 0`, `exhaustiveVectorCore_polarityCycleValid` further proves that the same exponential
inclusion-minimal core is a valid polarity certificate relative to the complete outside support.
The positivity hypothesis is real: at `Q = 0` the unique competitor has an empty outside edge,
so it cannot satisfy the nonempty-edge clause of `PolarityCycleValid` (although it remains the
one-clause unsatisfiable minimal core).

This separates the final canonical obligation cleanly.  It is no longer necessary to make the
combinatorial core or incidence proof depend on a fragile enumeration order.  What remains is to
prove

```text
queriedVars (canonicalDT (exhaustiveVectorGate Q) Q (fun _ => none))
  = Finset.univ.map Fin.castSuccEmb.
```

The most promising proof is order-independent: under any partial assignment fixing fewer than
`Q` outside coordinates, no exhaustive term is satisfied, while at least one compatible vector
clause remains active and its first free literal is a fresh outside coordinate.  Formalize that
invariant and induct on remaining fuel; the exact canonical incidence and support-exponential
validity statements will then follow by rewriting the theorems already proved here.  No
P-versus-NP conclusion follows.

### The order-independent canonical root invariant is now formalized

The enumeration-sensitive selector gap has been removed.  The theorem
`activeTerm_exhaustiveVectorClause_of_free` proves that whenever the protected final coordinate
and at least one outside coordinate are free, `activeTerm` selects an exhaustive Boolean-vector
clause from the prefix, not the appended protected target.  The proof uses only that some prefix
clause is live; it does not inspect or constrain the order chosen by `Finset.toList`.

The structural corollary `canonicalDT_exhaustiveVectorGate_root_query_of_free` unfolds one
canonical-tree step and proves that its root query is `i.castSucc` for some `i : Fin Q`.  Since
the selected literal belongs to `freeLits`, this is a fresh outside coordinate.  Thus the exact
local invariant proposed above is now source-checked for every partial restriction and every
remaining fuel.

The stricter module-target build also exposed latent code-generation and proof gaps in the
previous arbitrary-support block that a top-level replay had not rebuilt.  In particular,
`Finset.toList` made the concrete gate inherently noncomputable.  The gate and family are now
marked `noncomputable`, and the target-disjointness, live-clause, coordinate-fiber, and positive-
support validity proofs were repaired.  The module now builds as an actual Lake target (8,347
jobs), with all arbitrary-support capstones depending only on `propext`, `Classical.choice`, and
`Quot.sound`.

What remains is the global induction.  The precise next frontier is to prove that `fixVar` on
such a root preserves the protected-coordinate hypothesis and removes exactly that one element
from the free outside support, then induct on the support cardinality (not on the unspecified
clause order).  This should yield

```text
queriedVars (canonicalDT (exhaustiveVectorGate Q) Q (fun _ => none))
  = Finset.univ.map Fin.castSuccEmb
```

and allow the already proved exact core-incidence rectangle to be rewritten over the gate's
actual canonical queried set.  No P-versus-NP conclusion follows.

### The arbitrary-support canonical query set is now exact

The local invariant now closes under the full canonical walk.  The new finite support
`exhaustiveVectorFreeSupport sigma` records precisely the outside coordinates still free under
`sigma`.  The transition lemmas `fixVar_castSucc_last` and
`exhaustiveVectorFreeSupport_fixVar` prove that fixing an embedded outside coordinate preserves
the protected final coordinate and erases exactly that one support element, for either Boolean
branch.

`exhaustiveVectorGate_queriedVars_eq_freeSupport` then inducts on the support cardinality.  At
every nonempty stage the previously proved root invariant supplies a fresh embedded query; both
children have the same support with that coordinate erased, so the induction hypotheses identify
both child query sets exactly.  This proof never inspects the order of `Finset.toList`.

Specializing to the all-free root gives the formerly missing equality

```text
queriedVars (canonicalDT (exhaustiveVectorGate Q) Q (fun _ => none))
  = Finset.univ.map Fin.castSuccEmb.
```

Consequently `exhaustiveVectorCore_polarityCycleValid_canonical` proves, for every `Q > 0`, that
the concrete canonical gate has a valid inclusion-minimal unsatisfiable polarity core of size
`2^Q` on its actual queried support.  The rewritten incidence capstone
`exhaustiveVectorCore_canonicalQueryIncidences_card` proves the exact canonical incidence count
`2^Q * Q`; the earlier coordinate-fiber theorem therefore applies to actual canonical queries,
with all `2^Q` clauses incident to every queried coordinate.

This establishes the asymptotic obstruction requested by the incidence audit: normalization,
minimal-core reduction, and canonical querying alone do not yield a subexponential raw incidence
bound.  The precise next frontier is the remaining ownership-map possibility.  Define a selector
that assigns each retained clause to one incident canonical coordinate and prove the sharp
pigeonhole load for this exhaustive family (at least `ceil(2^Q / Q)` on some coordinate).  Then
compare that unavoidable load directly with the preservation ratio `choose(K,R) / choose(B,R)`;
if it is still incompatible, the generic polarity-ownership route is closed and the project
should return to a stricter run-sensitive encoder.  No P-versus-NP conclusion follows.

### Incident ownership has an unavoidable exponential-over-support load

The ownership-map possibility now has a precise interface.  `IncidentCoordinateOwner` requires
an arbitrary rule on indexed retained clauses to select both an actual canonical query and a
coordinate in that clause's outside-target edge.  The definition does not assume that ownership
is canonical, local, or order-independent, so the lower bound applies to every proposed rule of
this form.

`IncidentCoordinateOwner.exists_ceilDiv_le_load` proves the sharp finite averaging statement

```text
exists v in queried,
  ceil(core.card / queried.card) <= |{p in core | owner p = v}|.
```

The proof partitions the core exactly into ownership fibers and uses natural ceiling division;
nonempty core plus incident ownership supplies the required nonempty queried set.  Thus there is
no hidden positivity or totality premise.

The exhaustive family is nonvacuously inside this interface.  For `Q > 0`,
`exhaustiveVectorFirstOwner` assigns every clause to the first outside coordinate, and
`exhaustiveVectorFirstOwner_incident` proves this is a valid incident owner because every
exhaustive competitor contains every outside coordinate.  More importantly, the universal
capstone `exhaustiveVectorCore_incidentOwner_exists_load` proves for *every* incident owner that

```text
exists v in queriedVars(canonicalDT exhaustiveVectorGate),
  ceil(2^Q / Q) <= |{p in exhaustiveVectorCore Q | owner p = v}|.
```

Hence ownership can reduce the raw `2^Q * Q` incidence charge only to an unavoidable maximum
load of at least `ceil(2^Q / Q)`, still exponential up to a polynomial support factor.  This does
not by itself close the ownership route: the restriction-preservation probability attached to a
fiber has not yet been aligned with the existing shell parameters.

The precise next frontier is to formalize the comparison with the preservation ratio
`choose(K,R) / choose(B,R)`.  Instantiate the owner-load obstruction at the round's actual
`Q`, `K`, `R`, and `B`, and determine whether the ratio can absorb `ceil(2^Q / Q)` uniformly over
the intended multi-round schedule.  If not, record the quantitative incompatibility and return to
a stricter run-sensitive encoder.  No P-versus-NP conclusion follows.

### The exhaustive ownership obstruction is already bounded by the round's width factor

The attempted shell-ratio instantiation exposed a necessary width check before any density
comparison.  `exhaustiveVectorClause_length` proves that every Boolean-vector competitor in the
exhaustive family has length exactly `Q`.  Consequently
`exhaustiveVectorGate_width_forces_support_le` proves that any uniform width-`w` hypothesis on this
gate forces `Q <= w`.  The construction's exponential support is therefore simultaneously
growing clause width; it is not a constant-width exponential obstruction.

For a layered round whose residual clause width is bounded by `s+1`, the new arithmetic capstone
`exhaustiveVectorOwnerLoad_le_residualWidthFactor` proves, for positive `Q <= s+1`,

```text
ceil(2^Q / Q) <= 2^(s+1).
```

That right-hand side is already an explicit factor in `layeredRoundKeyCap`.  Thus the exhaustive
family does not close the ownership route under the actual bounded-width schedule, even before
using the additional preservation density `choose(K,R) / choose(B,R)`.  Its earlier exact
canonical-query and minimal-core lower bounds remain valid, but their asymptotic interpretation
must retain the growing-width cost.

The stricter target replay also found and repaired an elaboration gap in
`exhaustiveVectorFirstOwner_incident`: membership in the mapped canonical-query support is now
proved with the explicit first `Fin Q` witness instead of relying on a `simp` call that left a
goal in a fresh rebuild.

The precise next frontier is width-sensitive.  Either prove a general ownership/load upper bound
for normalized width-`w` polarity cores that fits the existing `2^(s+1)` recurrence charge, then
combine it with the exact target-preservation balance, or construct a normalized constant-width
canonical family whose minimal-core ownership load grows beyond every width-only bound.  The
current exhaustive family cannot serve as that counterexample.  No P-versus-NP conclusion
follows.

### Minimal polarity cores are injective after semantic outside-literal normalization

The first width-sensitive reduction is now formalized.  The new
`competitorOutsideTargetLiteralSet target U` retains exactly the polarity-sensitive literals of
`U` whose variables avoid the complete protected-target support, while forgetting target index,
protected literals, order, and duplicate occurrences.  Its cardinality is at most `U.lits.length`,
so an input width bound transfers directly to this semantic signature.

`InclusionMinimalUnsatisfiableCore.outsideLiteralSet_injectiveOn` proves that this signature is
injective on every inclusion-minimal unsatisfiable core.  If two indexed competitors had the same
signature, the satisfying witness obtained after deleting the first would hit the second; the
identical signature would then make it hit the deleted competitor as well, contradicting
unsatisfiability.  The capstone `card_image_outsideLiteralSet` records the exact equinumerosity of
the core and its signature image.

This removes several false sources of ownership growth at once: repeating a semantic competitor
under many target indices, changing literal order, adding protected literals, or repeating an
outside literal cannot increase a minimal core.  The remaining problem is therefore the genuine
combinatorics of distinct nonempty polarity-labelled subsets of queried coordinates of size at
most `w`; syntactic gate multiplicity is no longer relevant.

The precise next frontier is to exploit minimal unsatisfiability beyond this injectivity.  First
derive (or refute with a normalized constant-width family) a bounded-load orientation theorem for
the resulting irredundant semantic signatures.  A mere enumeration of all width-`w` signatures
would still depend polynomially on the queried-support size and would not fit the existing
`2^(s+1)` width-only recurrence charge; the needed next lemma must use the deletion witnesses, not
only distinctness and width.  No P-versus-NP conclusion follows.

### Bounded-load ownership reduces to a capacitated Hall-density problem

The ownership question now has a proved local interface.  `incidentQueriedVars` intersects each
competitor's genuine outside-target edge with the recorded query support, and
`incidentOwnerSlots` gives every such coordinate `L` distinguishable ownership slots.  Hall's
marriage theorem then yields
`exists_incidentCoordinateOwner_load_le_of_localDensity`: for a nonempty core with nonempty
incident queried edges, if every subfamily `S` satisfies

```text
|S| <= L * |union_{p in S} incidentQueriedVars(p)|,
```

there is an incident owner whose every coordinate fiber has size at most `L`.  Thus a sufficient
route to the orientation theorem is neither an informal averaging argument nor a whole-core
cardinality bound: it is capacitated Hall density over all subfamilies.  A direct converse is
mathematically elementary, but the attempted Lean proof was deliberately not retained because its
first proof route inherited `sorryAx` under the repository's axiom audit.

This sharpens the role of the deletion witnesses.  Minimal unsatisfiability applies to the whole
core, while Hall tests arbitrary subfamilies, which need not themselves be minimal or
unsatisfiable.  Consequently the existing whole-core witness injection and semantic-signature
injectivity do not yet discharge the new premise.

The precise next frontier is to test the width budget `L = 2^w` against this Hall condition.
Either use the deletion witnesses to prove, for every subfamily of a normalized width-`w` minimal
polarity core, `|S| <= 2^w * |union incidentVars(S)|`, which immediately produces the ownership
bound needed by the recurrence, or construct a normalized constant-width minimal core containing
a subfamily whose clause-to-variable density exceeds every width-only `L`.  Any counterexample
must violate this local inequality, not merely have a large total core.  No P-versus-NP conclusion
follows.

### Deletion witnesses give an exact local exponential bound, not yet the Hall bound

The deletion-witness injection now works at the quantifier strength required by Hall.
`InclusionMinimalUnsatisfiableCore.subfamily_card_le_two_pow_incidentUnion` proves for every
subfamily `S` of a globally inclusion-minimal core, assuming all outside edges lie in the queried
support,

```text
|S| <= 2 ^ |union_{p in S} incidentQueriedVars(p)|.
```

The subfamily need not itself be unsatisfiable or inclusion-minimal.  For each retained clause,
the proof restricts its global deletion witness to the union touched by `S`; equality of two
restricted witnesses would let one witness hit its own deleted clause through the other clause,
contradicting global unsatisfiability.  This is therefore a genuine local consequence of the
deletion witnesses, rather than a reuse of the earlier whole-core cardinality estimate.

This identifies the remaining quantitative gap exactly.  If `q` coordinates occur in a Hall
subfamily, the proved input is `|S| <= 2^q`, while the desired width budget requires
`|S| <= 2^w * q`.  The former implies the latter only in the arithmetic range where
`2^q <= 2^w * q`; minimality alone has not supplied a reason that every subfamily lies in that
range.  The proof deliberately does not replace this exponential dependence by an unsupported
width-only estimate.

The precise next frontier is to add the missing width structure to this local witness code.
Either prove that width-`w` private deletion witnesses force a compression/orientation of every
subfamily from `2^q` down to `2^w * q`, or construct a normalized constant-width minimal core
whose private-witness subfamily has density above `2^w`.  The latter must be a genuine minimal
subcube cover/canonical-gate example, not merely an arithmetic counterexample to the current
upper bound.  No P-versus-NP conclusion follows.

### The witness code meets the Hall budget through support `w + 1`

The first exact width-sensitive cutoff is now formalized.
`InclusionMinimalUnsatisfiableCore.subfamily_card_le_widthBudget_of_smallSupport` combines the
local deletion-witness injection with the nonempty incident-edge premise used by capacitated
Hall.  For positive `w`, every subfamily `S` whose incident union has cardinality `q <= w + 1`
satisfies

```text
|S| <= 2^w * q.
```

The endpoint `q = w + 1` is included: `2^(w+1) = 2^w * 2`, and positivity of `w` gives
`2 <= w + 1`.  Empty subfamilies are handled separately, so no hidden support-positivity premise
is introduced.

The contrapositive capstone
`InclusionMinimalUnsatisfiableCore.width_add_two_le_incidentUnion_of_density_failure` proves that
any actual failure of the desired load-`2^w` Hall inequality must have

```text
w + 2 <= q.
```

Thus the first support size beyond width is not an obstruction.  The unresolved range is now
strictly the large-support regime, where the raw witness bound `2^q` ceases to fit the linear
budget.  This does not prove the full Hall premise and does not produce the required owner.

The precise next frontier is to exploit clause width inside that `q >= w + 2` regime.  A useful
next discriminator is either a deletion/splitting recurrence that reduces a large-support
subfamily to smaller-support pieces while paying at most `2^w` per coordinate, or a normalized
constant-width minimal canonical core with a Hall-violating subfamily at the now-forced support
threshold.  Any proposed counterexample with `q <= w + 1` is ruled out.  No P-versus-NP
conclusion follows.

### The witness-code cutoff extends through support `w + 2` for width at least two

The next arithmetic endpoint of the local deletion-witness code is now formalized.
`InclusionMinimalUnsatisfiableCore.subfamily_card_le_widthBudget_of_support_le_add_two` proves
that when `2 <= w`, every Hall subfamily touching `q <= w + 2` incident queried coordinates
satisfies

```text
|S| <= 2^w * q.
```

The only case not covered by the previous `q <= w + 1` theorem is `q = w + 2`.  There the
existing private-witness injection gives `|S| <= 2^(w+2) = 4 * 2^w`, and `2 <= w` gives
`4 <= w + 2`.  No new combinatorial hypothesis is hidden in the improvement.

The contrapositive capstone
`InclusionMinimalUnsatisfiableCore.width_add_three_le_incidentUnion_of_density_failure` therefore
forces every genuine failure of the desired load-`2^w` Hall inequality, for width at least two,
into the stricter regime

```text
w + 3 <= q.
```

This remains an arithmetic consequence of the exponential witness code, not the full Hall
premise.  The precise next frontier is to expose the complete arithmetic envelope
`2^(q-w) <= q` and then use actual clause-width structure where that envelope fails.  Concretely,
either prove a deletion/splitting recurrence for the first unsupported `(w,q)` pairs, or construct
a normalized constant-width minimal canonical core violating Hall there.  No P-versus-NP
conclusion follows.

### The complete arithmetic envelope is now explicit

The private deletion-witness code has now been separated exactly from the remaining structural
problem.  The theorem
`InclusionMinimalUnsatisfiableCore.subfamily_card_le_widthBudget_of_pow_sub_le` proves that every
Hall subfamily with incident-support size `q` satisfies

```text
|S| <= 2^w * q
```

whenever `2^(q-w) <= q`.  The proof also handles `q <= w` directly by monotonicity, so the stated
condition is a complete sufficient arithmetic envelope rather than only a large-support lemma.
For `w <= q`, it is exactly the factorization

```text
2^q = 2^w * 2^(q-w)
```

applied to the already proved local injection `|S| <= 2^q`.

The contrapositive capstone
`InclusionMinimalUnsatisfiableCore.pow_sub_gt_incidentUnion_of_density_failure` proves that any
genuine load-`2^w` Hall-density failure must simultaneously satisfy

```text
w < q
q < 2^(q-w).
```

Thus the remaining region is no longer described by a coarse cutoff such as `q >= w+3`; it is
the exact scalar failure region of the witness code.  For example, the first still-unsupported
endpoint is `(w,q) = (2,5)`, where `8 > 5`, while larger widths can remain inside the envelope
for additional support levels.

The precise next frontier is structural: analyze the first envelope-failing normalized
constant-width cases (beginning with width two on five queried coordinates).  Either derive a
deletion/splitting recurrence that uses each clause's width to recover the Hall budget there, or
preserve a concrete inclusion-minimal canonical polarity core whose subfamily actually violates
that budget.  Arithmetic refinement of the existing `2^q` code alone cannot decide this region.
No P-versus-NP conclusion follows.

### The first width-two obstruction is confined to a 21--32 clause window

The first arithmetic-envelope failure has now been reduced to an exact finite cardinality target.
`InclusionMinimalUnsatisfiableCore.widthTwo_fiveSupport_card_window_of_density_failure` proves
that a Hall-violating subfamily on five incident coordinates at load `2^2 = 4` would have to
satisfy

```text
21 <= |S| <= 32.
```

The lower endpoint is the strict Hall failure `4 * 5 < |S|`; the upper endpoint is the already
proved deletion-witness injection `|S| <= 2^5`.  This theorem deliberately does not manufacture
width structure that is absent from the generic witness argument.

As a non-kernel discriminator, an exact mixed-integer model of all 50 non-tautological unit and
binary semantic clauses on five Boolean variables was also tested.  The model enforces coverage
of every assignment and gives every selected clause a private falsifying assignment, exactly the
finite irredundant-cover conditions corresponding to inclusion-minimal unsatisfiability.  A
30-second HiGHS run found a 10-clause feasible core and returned a valid branch-and-bound upper
bound of 19 selected clauses.  Thus this search found no candidate in the Lean-proved 21--32
obstruction window.  The solver run is useful route-selection evidence only: no solver
certificate has been imported into Lean, so the width-two/five-support Hall bound is not claimed
as proved.

The precise next frontier is to formalize the width-two implication-graph (weak-double-cycle)
bound needed to close this finite window, preferably as a reusable theorem that every normalized
inclusion-minimal width-two core has at most four clauses per incident variable.  A smaller
alternative is a kernel-checkable exhaustive certificate ruling out cardinalities 21 through 32
on five variables.  Only after that bound is proved should the analysis move to the next
arithmetic-envelope failure.  No P-versus-NP conclusion follows.

### Minimal cores now have a kernel-checked private-point dimension interface

The implication-graph route is not the shortest currently visible route.  Define the outside-term
indicator of a retained indexed competitor to be one exactly when none of its available
outside-target literals is falsified.  The theorem
`InclusionMinimalUnsatisfiableCore.outsideTermIndicators_linearIndependent` proves over `ℚ` that
all such indicators in an inclusion-minimal unsatisfiable core are linearly independent.

The proof uses the deletion witness for a term `p`.  That assignment hits every other retained
term.  It cannot also hit `p`, since it would then satisfy the whole core, contradicting global
unsatisfiability.  It is therefore a private point where the indicator of `p` is one and every
other indicator is zero.  Evaluating a putative linear dependence at this point isolates the
coefficient of `p`.

The companion theorem
`InclusionMinimalUnsatisfiableCore.card_le_of_outsideTermIndicators_mem_span` packages the exact
dimension consequence: if a finite function basis spans all outside-term indicators, then

```text
|core| <= |basis|.
```

This changes the best route to the five-variable width-two window.  After localizing to the five
incident coordinates, every consistent width-two term indicator should lie in the span of the
squarefree monomials of degrees zero, one, and two.  That basis has size

```text
choose(5,0) + choose(5,1) + choose(5,2) = 1 + 5 + 10 = 16,
```

which is already strictly below the Hall-failure threshold 21.  Thus the non-kernel MILP upper
bound 19 is no longer the sharp guide; the private-point dimension argument predicts a stronger
kernel-checkable bound of 16 under the required width and localization premises.

The precise next frontier is to formalize the localization map from the five-coordinate incident
union, express each outside-term indicator as a degree-at-most-two squarefree polynomial (including
unit and empty outside signatures), and instantiate the abstract span theorem with the 16-element
monomial basis.  That would close the first `w = 2, q = 5` obstruction without an implication-graph
classification.  The same construction should then be generalized to the binomial-sum bound
`sum_{i <= w} choose(q,i)` and tested against the subsequent arithmetic-envelope failures.  No
P-versus-NP conclusion follows.

### Outside-term indicators are now localized to the queried support

The ambient-coordinate part of the private-point dimension route has now been removed.
`outsideCompetitorTermFires_congr_of_eqOn` proves that, whenever a competitor's available
outside variables lie in `queried`, its indicator has the same value on any two assignments
agreeing on `queried`.  The explicit maps `restrictQueriedAssignment` and
`extendQueriedAssignment` package this as

```text
ambient indicator assignment
  = localized indicator (assignment restricted to queried).
```

More importantly,
`InclusionMinimalUnsatisfiableCore.localizedOutsideTermIndicators_linearIndependent` proves
that the localized indicators are already linearly independent over `ℚ` as functions on
assignments `(queried → Bool)`.  The companion theorem
`card_le_of_localizedOutsideTermIndicators_mem_span` therefore bounds the core directly by any
finite basis on that localized assignment space.  No ambient-coordinate monomials or arbitrary
off-support values need to be carried into the five-variable argument.

This completes the localization substep but does not yet prove the bound 16.  The precise next
frontier is now purely algebraic: define the degree-at-most-two squarefree monomials on
`↥queried`, prove every localized indicator arising from an outside signature of length at most
two lies in their span (including empty and unit signatures and both polarities), and prove that
this basis has cardinality at most `1 + q + choose(q,2)`.  Instantiating at `q = 5` would give 16
and close the 21--32 Hall-failure window.  No P-versus-NP conclusion follows.

### The localized degree-two monomial family and its exact size budget are formalized

The algebraic target is now a concrete finite family rather than an informal dimension count.
`localizedSquarefreeMonomial` defines the rational-valued Boolean monomial on a finite subset of
the queried coordinates, and `localizedDegreeTwoMonomialBasis` collects the images of all
supports of cardinality zero, one, or two.  Defining the family as an image deliberately avoids
needing monomial injectivity: any coincident functions only make the eventual upper bound
stronger.

The theorem `localizedDegreeTwoMonomialBasis_card_le` proves the kernel-checked estimate

```text
|basis| <= 1 + q + choose(q,2),
```

using `powersetCard` and its exact binomial cardinality.  The companion theorem
`localizedSquarefreeMonomial_mem_degreeTwo_span` proves that every monomial whose support has
size at most two is already in the span of this displayed family.  In particular, at `q = 5`
the available dimension budget is at most 16; this is now a proved arithmetic fact about the
actual basis that will be passed to the localized dimension cap.

This does not yet show that each width-two outside-term indicator belongs to the span.  The
precise next frontier is the signed expansion lemma: rewrite the indicator as the product of at
most two affine coordinate factors, handle repeated variables with equal or opposite polarity,
and expand it into the proved constant, singleton, and pair generators.  Composing that lemma
with `card_le_of_localizedOutsideTermIndicators_mem_span` will yield the 16-clause cap and close
the five-coordinate 21--32 failure window.  No P-versus-NP conclusion follows.

### The signed width-two expansion and the five-coordinate full-core cap are formalized

The algebraic gap is now closed.  `localizedLiteralFiringFactor` is the affine factor contributed
by one available outside literal.  The two span lemmas prove that one such factor and the product
of two such factors belong to `localizedDegreeTwoMonomialBasis`.  The product proof explicitly
handles repeated coordinates: equal falsifying polarities collapse to one factor, while opposite
polarities give the zero function; distinct coordinates expand into the constant, singleton, and
pair monomials.

`localizedOutsideCompetitorTermIndicator_mem_degreeTwo_span` connects those factors to the actual
competitor semantics for every syntactic clause of width at most two.  Its list analysis includes
empty and unit clauses and literals protected by the target support.  Composing this theorem with
localized private-point linear independence gives

```text
|core| <= 1 + q + choose(q,2).
```

Thus a width-two inclusion-minimal core whose entire outside support is localized to five queried
coordinates has at most 16 members.  The theorem
`not_widthTwo_fiveSupport_density_failure` rules out the 21--32 density window under exactly this
full-core five-coordinate localization.

This last qualifier matters.  The Hall audit needs the same dimension argument for an arbitrary
subfamily `s` localized to its own incident union, even when other members of the ambient minimal
core use coordinates outside that union.  The current full-core theorem cannot simply replace
`queried` by that local union because its support premise quantifies over every core member.
The precise next frontier is therefore to restrict the private-point linear-independence family
to `s`, localize only those indicators to `s.biUnion incidentQueriedVars`, and derive the
subfamily bound `|s| <= 1 + q + choose(q,2)`.  That would genuinely close the width-two `q = 5`
window (and also the `q = 6` load-four inequality); at `q = 7` this quadratic budget becomes 29
against a Hall budget of 28, exposing the next structural boundary.  No P-versus-NP conclusion
follows.

### The width-two private-point bound now applies to every Hall subfamily

The full-core qualifier has been removed.  The theorem
`subfamily_localizedOutsideTermIndicators_linearIndependent` restricts the deletion-witness
argument to an arbitrary `s : Finset ↥core`: every selected clause still has a private point
against all other core clauses, hence in particular against the other selected clauses.  Only
the selected indicators must localize to the chosen coordinate set; unselected ambient core
members may use unrelated coordinates.

Combining this restricted independence with the signed degree-two expansion gives
`subfamily_card_le_degreeTwo_incidentUnion`:

```text
|s| <= 1 + q + choose(q,2),
q = |s.biUnion incidentQueriedVars|.
```

The two arithmetic corollaries
`not_widthTwo_subfamily_density_failure_five` and
`not_widthTwo_subfamily_density_failure_six` now rule out load-four Hall failure at `q = 5` and
`q = 6` for arbitrary subfamilies, not merely when the whole minimal core has that support.
Their budgets are respectively `16 <= 20` and `22 <= 24`.

The precise next frontier is `q = 7`.  The current degree-two dimension estimate gives 29 while
load four permits only 28, so span dimension alone misses by exactly one.  The highest-value next
test is to identify a universally absent degree-two direction forced by unsatisfiability or by
nonempty incidence, or else construct a normalized inclusion-minimal width-two core/subfamily
realizing all 29 dimensions on seven incident coordinates.  That decides whether the Hall route
extends past this first one-dimensional deficit.  No P-versus-NP conclusion follows.

### Full degree-two dimension now forces a pointwise partition

The one-dimensional `q = 7` deficit has been reduced to an equality-case packing problem.
`sum_eq_one_of_privatePoints_of_finrank_le_card` proves an abstract finite-dimensional statement:
if a linearly independent family fills a function subspace and every vector has a coordinate
private point, then the vectors sum pointwise to the constant-one function.  Evaluation at a
private point forces the corresponding coefficient of the constant function to be exactly one.

The circuit-facing theorem
`InclusionMinimalUnsatisfiableCore.subfamily_indicators_partition_of_degreeTwo_full` instantiates
this fact for an arbitrary Hall subfamily.  If the subfamily attains

```text
|s| = 1 + q + choose(q,2),
```

then on every localized Boolean assignment exactly one of its zero-one outside-term indicators
fires.  In particular, a hypothetical `q = 7`, 29-member obstruction cannot merely realize all
29 polynomial directions: its width-two firing subcubes must partition the 128-point Boolean
cube.  This is substantially more rigid than linear independence and rules out searching for an
arbitrary 29-element degree-two basis as a counterexample.

### The partition-mass obstruction closes the seven-coordinate Hall case

The finite-fiber step is now kernel checked.  The abstract theorem
`boolAssignment_card_le_four_mul_firingFiber_of_twoCoordinateRetraction` records the two bits
erased when an assignment is overwritten on two coordinates, producing an injection into four
copies of the firing fiber.  The circuit-facing dependency theorem
`localizedOutsideCompetitorTermFires_dependsOn_twoCoordinates` proves that every localized
syntactic-width-two indicator has such a two-coordinate support.  Protected literals are treated
as constant factors, repeated coordinates are allowed, and the contradictory repeated-polarity
case is not discarded: `localizedOutsideCompetitorTermFires_cube_card_le_four_mul_fiber` requires
an explicit firing witness.  Minimal-core deletion witnesses provide exactly that nonzeroness.

The double-counting theorem `card_le_four_of_partition_and_quarter_fibers` shows that a pointwise
partition by nonempty subsets, each occupying at least one quarter of a finite cube, has at most
four parts.  Combining it with the full-dimension partition gives the strict general bound
`InclusionMinimalUnsatisfiableCore.subfamily_card_lt_degreeTwo_binomialBudget` whenever the
degree-two budget exceeds four.  In particular,
`widthTwo_subfamily_card_le_twentyEight_of_seven` improves the seven-coordinate cap from 29 to 28,
and `not_widthTwo_subfamily_density_failure_seven` closes load-four Hall failure at `q = 7`.

The mass arithmetic is actually stronger than the initially proposed `29 * 32 > 128`
specialization: equality in the degree-two dimension budget is impossible whenever that budget
exceeds four.  The precise next frontier is `q = 8`.  The strict degree-two cap is 36 while load
four permits 32, leaving four dimensions of slack; closing this case requires extracting more
than the equality case—either a sharper structural rank defect, a stronger packing inequality for
the deletion-witness indicators, or a normalized counterexample showing the load-four Hall route
stops there.  No P-versus-NP conclusion follows.

### The first eight-coordinate packing stress test is formalized

The most direct strengthening of the partition-mass argument does not by itself close `q = 8`.
`positivePairSupportsEight` is the family of all 28 unordered coordinate pairs, and
`positivePairFiresEight` assigns to each pair the quarter-cube on which both coordinates are true.
The kernel-checked theorems `positivePairSupportsEight_card` and
`positivePairSupportsEight_private` prove that all 28 fibers are irredundant: the assignment true
exactly on a given pair is private to that pair.

This construction does not violate load four: 28 is still below the threshold 32.  It does show
that nonzeroness, quarter-cube mass, and deletion-style private points permit a genuinely
quadratic family already on the exact eight-cube, so no linear packing bound can be inferred from
those ingredients alone.  A direct mixed-integer feasibility search for 33 codimension-at-most-two
subcubes was also run as a diagnostic; it found neither a feasible family nor an infeasibility
certificate within the time limit, so it is recorded only as a failed route and is not used by
any theorem.

The precise next frontier is to exploit the signed two-literal structure beyond bare private
points and decide the narrow 33--36 window.  The highest-value finite target is a certified upper
bound of 32 for irredundant codimension-at-most-two subcubes on eight coordinates, or an explicit
33-member family.  If the abstract cube problem admits 33 members, the next check is whether such
a family can also arise from an inclusion-minimal unsatisfiable core with the bridge's protected
target semantics.  No P-versus-NP conclusion follows.

### Meshulam's bound collapses the eight-coordinate window to 28--29

The preceding 33--36 target overlooked a classical irredundant-subcube bound.  First, allowing
codimension *at most* two does not enlarge the homogeneous extremal problem here.  Choose a private
point in every member and, for each codimension-zero or codimension-one cube, fix arbitrary
additional free coordinates to their values at that private point until the cube has codimension
exactly two.  Every shrunken cube still contains its own private point and lies inside its original
cube, so the private points remain private.  Two shrunken cubes cannot coincide, since then each
would contain the other's private point.  (If the whole cube is the sole member the desired bound
is immediate.)  Thus any relevant family of size greater than one homogenizes injectively to an
irredundant family of six-dimensional subcubes of the eight-cube.

Meshulam's general bound for irredundant `k`-dimensional subcubes is

```text
M(n,k) <= 2^n * choose(n,k) / sum_{i=0}^k choose(n,i).
```

At `n = 8`, `k = 6`, the ball volume is `247` and the incidence budget is
`256 * 28 = 7168`.  Consequently `247 * |family| <= 7168`, hence
`|family| <= 29`.  The new Lean theorem `meshulamEightCodimensionTwo_arithmetic` kernel-checks
this exact integer specialization from the displayed Meshulam inequality; the companion theorem
`meshulamEightCodimensionTwo_twentyNine_compatible` records that the inequality genuinely still
allows 29.  The combinatorial inequality itself is not yet formalized in this repository.  The
external source is David Ellis, *Irredundant Families of Subcubes* (2010), Theorem 4, which gives
a proof of Meshulam's bound via Bollobás' inequality:
https://arxiv.org/abs/1003.2960.

This rules out the entire 30--36 window and makes the failed 33-member feasibility search moot as
an extremal guide, though it remains recorded above as a failed route.  Together with the explicit
28-member positive-pair family, the abstract extremal value is now confined to `28` or `29`.

The precise next frontier is the single equality gap: either formalize enough of the local
Bollobás/Meshulam argument to obtain the kernel-checked cap 29 and then exclude its equality case,
or construct an explicit 29-member irredundant codimension-two family.  If 29 is attainable, test
whether it can arise from an inclusion-minimal unsatisfiable core with the protected-target
semantics; if it is not, the 28 positive-pair construction is optimal and the load-four Hall case
at `q = 8` closes.  No P-versus-NP conclusion follows.

### The Hall frontier moves past the unresolved 28/29 extremal gap

The preceding exact-extremal target is mathematically natural but is not on the critical path for
the load-four Hall argument.  At eight incident coordinates Hall permits `4 * 8 = 32` members, so
the conditional Meshulam cap 29 already excludes density failure regardless of whether 28 or 29 is
the true extremal value.  The new theorem
`not_widthTwo_subfamily_density_failure_eight_of_meshulam` formalizes this implication while
keeping the unformalized combinatorial Meshulam inequality as an explicit premise.

The same audit advances one coordinate further.  At `n = 9`, codimension two means dimension seven,
and Meshulam specializes to

```text
502 * |family| <= 512 * 36 = 18432,
|family| <= 36 = 4 * 9.
```

`meshulamNineCodimensionTwo_arithmetic` and
`not_widthTwo_subfamily_density_failure_nine_of_meshulam` kernel-check the arithmetic and its Hall
consequence.  Thus, conditional on the same external combinatorial inequality, both `q = 8` and
`q = 9` are closed.  The unresolved 28/29 question is retained above as a useful extremal side
problem, and a symmetry-reduced exact mixed-integer search for 29 was also attempted: after fixing
one cube and moving its private point to zero, the model shrank from 112 to 85 candidate cubes but
still returned no construction or infeasibility certificate within the time limit.  It is therefore
recorded only as a failed diagnostic.

The first arithmetic failure is now `q = 10`.  Theorems
`meshulamTenCodimensionTwo_arithmetic` and
`meshulamTenCodimensionTwo_fortyFive_compatible` show exactly

```text
1013 * |family| <= 1024 * 45 = 46080,
|family| <= 45,
```

while load four permits only 40.  The precise next frontier is therefore to formalize the
codimension-two Meshulam inequality for the bridge's homogenized subfamily model and then seek a
five-member improvement at ten incident coordinates, or exploit additional protected-target
semantics before homogenization.  Resolving 28 versus 29 is no longer required to advance the Hall
schedule.  No P-versus-NP conclusion follows.

### The codimension-two homogenization step is now kernel checked

The informal reduction from codimension at most two to codimension exactly two is now a proved
abstract theorem.  `BooleanSubcube` represents a Boolean subcube by its partial assignment, with
`fixedVars` recording its codimension and `Contains` its point membership.  The theorem
`BooleanSubcube.exists_codimensionTwo_refinement_preserving_privatePoints` starts from any finite
indexed family with:

```text
at most two fixed coordinates per member;
one displayed private point per member;
at least two ambient coordinates.
```

For each member it extends the fixed-coordinate set to cardinality exactly two and fixes every
new coordinate to that member's private-point value.  The resulting subcube contains its old
private point, is contained in its original subcube, preserves all cross-member exclusions, and
is injectively indexed.  Thus irredundancy survives homogenization without assuming that the
original family was already uniform.  In particular, the earlier prose reduction used before the
Meshulam arithmetic is no longer an unverified step.

This does not yet prove Meshulam's inequality or automatically identify the bridge's localized
firing predicates with the new partial-assignment representation.  The precise next frontier is
to construct that identification for every nonzero localized width-two competitor indicator
(including protected literals and repeated coordinates), extract the minimal-core deletion
witnesses as private points, and then formalize the homogeneous codimension-two Meshulam bound.
At `q = 10`, Meshulam alone will still leave the recorded five-member `45` versus `40` gap, so a
protected-target refinement remains necessary after that bridge.  No P-versus-NP conclusion
follows.

### Localized width-two indicators are now realized as irredundant Boolean subcubes

The circuit-to-subcube identification is now kernel checked.  `BooleanSubcube` was generalized
from `Fin Q` coordinates to any finite coordinate type, so the bridge can work directly on the
subtype of a queried finset without an arbitrary enumeration.  For a supported competitor,
`localizedOutsideCompetitorFixedVars` records exactly the queried coordinates carrying available
outside-target literals, and `localizedOutsideCompetitorSubcube` fixes those coordinates to the
values of one displayed firing witness.

The theorem `localizedOutsideCompetitorTermFires_iff_subcubeContains` proves that, once the
indicator is nonzero, its firing predicate is exactly membership in this subcube.  This covers
protected literals, duplicate occurrences, same-polarity repeated variables, and contradictory
repeated polarities: the last case simply cannot have a firing witness unless the contradictory
literal is protected.  The companion codimension theorem bounds the number of fixed coordinates
by the original syntactic clause length.

At family level, `InclusionMinimalUnsatisfiableCore.exists_subfamily_booleanSubcubes` chooses each
member's deletion witness, restricts it to the local queried coordinates, and proves that these
are private points for the represented subcubes.  Finally,
`exists_subfamily_codimensionTwo_refinement` composes this result with homogenization: whenever
the local support has at least two coordinates, every localized width-two Hall subfamily has an
injectively indexed, irredundant codimension-exactly-two refinement contained in its original
firing fibers.

Thus the previously missing bridge into Meshulam's homogeneous model is closed.  The precise next
frontier is to formalize Meshulam's codimension-two inequality itself (most economically via the
local Bollobás set-pairs argument) and instantiate it on these refined Hall subfamilies.  That will
kernel-check the conditional `q = 8` and `q = 9` closures already audited above.  At `q = 10`, a
separate protected-target rank or packing refinement must still improve Meshulam's cap from `45`
to the Hall budget `40`.  No P-versus-NP conclusion follows.

### Meshulam's global count is reduced to one local occupancy lemma

The global part of the Bollobás/Meshulam argument is now kernel checked.  The generic theorem
`finiteRelation_card_mul_le_card_mul` double-counts a finite relation from a common row size and a
uniform column cap.  For Boolean cubes, `booleanAssignmentDisagreementEquiv` identifies an
assignment with the set of coordinates on which it differs from a fixed center, and
`booleanHammingBall_card` proves the exact radius-`k` volume

```text
sum_{i=0}^k choose(n,i).
```

The capstone `meshulam_global_fin_of_local_ball_bound` combines these results.  For any displayed
private points `w_p : Fin n -> Bool`, it derives

```text
|family| * sum_{i=0}^k choose(n,i) <= 2^n * choose(n,k)
```

from exactly the pointwise local premise

```text
for every x, at most choose(n,k) private points w_p have Hamming distance at most k from x.
```

Thus Hamming-ball enumeration, incidence rearrangement, and the final global arithmetic are no
longer part of the unformalized Meshulam gap.

### The exact local set-pairs reduction is now formalized

The earlier description of the local step as a direct set-pairs argument on each member's full
fixed-coordinate set was too compressed.  Ellis's proof of the Hamming-ball form of Meshulam's
bound first writes every Boolean subcube as a subset-lattice interval `[v_C,u_C]`.  For a chosen
private point `w_C`, it then uses the smaller interval `[w_C,u_C]` and averages a weighted
Bollobas inequality over all ambient `k`-sets in that interval.

The `BooleanSubcube` namespace now contains the required kernel-checked structural layer:

* `trueSupport`, `fixedTrueVars`, `fixedFalseVars`, and `endVars` give the subset-lattice data;
* `contains_iff_trueSupport_interval` proves exactly
  `Contains c a <-> fixedTrueVars c ⊆ trueSupport a ⊆ endVars c`;
* `fixedTrueVars_subset_privateSupport_iff` proves that if one common set `x` lies above every
  selected private support and below every selected upper endpoint, then
  `fixedTrueVars (c i) ⊆ trueSupport (w j)` iff `i = j`;
* `fixedTrueVars_disjoint_privateComplement_iff` packages the corresponding Bollobas pairs
  `(fixedTrueVars (c i), x \ trueSupport (w i))`, whose intersections vanish exactly on the
  diagonal;
* `card_sdiff_trueSupport_of_subset` identifies the second pair size as
  `x.card - (trueSupport (w i)).card`.

This closes the non-counting heart of the local argument and corrects the route to match Ellis,
Theorem 7.  The precise next frontier is now to formalize the weighted Bollobas inequality

```text
sum_i 1 / choose(|A_i| + |B_i|, |B_i|) <= 1
```

for finite set pairs whose intersections are empty exactly on the diagonal, then sum it over the
`k`-sets `x` in each private-point-to-end interval.  That will prove the local occupancy cap,
after which specializing to codimension two (`k = n - 2`) and transporting the queried-coordinate
subtype to `Fin q` makes the existing `q = 8` and `q = 9` Hall closures unconditional.  The
separate `q = 10` gap remains `45` versus `40`.  No P-versus-NP conclusion follows.

### Weighted interval aggregation is now kernel checked

The averaging step after the pointwise Bollobas inequalities is no longer part of the gap.
`BooleanSubcube.finite_weighted_cover_card_le` proves the exact finite double-counting statement:
if index `i` occurs on a finite set `S_i`, its weight is normalized by

```text
|S_i| * weight_i = 1,
```

and the total weight through every ambient point is at most one, then the number of indices is at
most the number of ambient points.  The reciprocal specialization
`finite_reciprocal_cover_card_le` takes `weight_i = 1 / |S_i|` and exposes only the necessary
nonemptiness premise.  Its proof expands the incidence sum in both orders, so every member
contributes exactly one; no positivity or lossy maximum-weight estimate is used.

For Ellis's application, `S_i` is the set of ambient `k`-sets in the interval from private point
`w_i` to upper endpoint `u_i`, and the ambient type is the collection of all `k`-sets.  The precise
next frontier has consequently narrowed to the genuinely combinatorial input: prove the exact
interval-slice cardinality

```text
|S_i| = choose(|fixedTrue_i| + k - |w_i|, |fixedTrue_i|)
```

for homogeneous `k`-cubes, and prove the weighted Bollobas inequality for the set pairs already
constructed at each ambient `k`-set.  Those two facts feed directly into the verified reciprocal
cover theorem and yield the local occupancy cap.  The `q = 10` gap remains `45` versus `40`.  No
P-versus-NP conclusion follows.

### The exact private-point-to-end slice cardinality is now kernel checked

The first of the two remaining local counting inputs is closed.  The generic theorem
`card_powersetCard_filter_superset` proves that the number of `k`-subsets of an ambient finite set
which contain a required subset is exactly

```text
choose(|ambient| - |required|, k - |required|).
```

Specializing `ambient` to a Boolean subcube's upper endpoint and `required` to the true support of
its displayed private point gives `privateToEndSlice_card`.  The homogeneous specialization
`privateToEndSlice_card_of_dimension` additionally proves the exact Ellis denominator

```text
|S_i| = choose(|fixedTrue_i| + k - |w_i|, |fixedTrue_i|).
```

The proof explicitly identifies every slice member with the uniquely chosen extra coordinates;
it does not estimate the slice by a worst-case binomial coefficient.  The companion endpoint
identity shows that a dimension-`k` subcube's upper endpoint consists of its fixed-true lower
endpoint plus exactly `k` free coordinates.

The precise next frontier is now the weighted Bollobas set-pairs inequality itself for the pairs
`(fixedTrueVars (c i), x \ trueSupport (w i))` already constructed at each ambient `k`-set.  Once
that pointwise rational-weight bound is formalized, the verified reciprocal aggregation theorem
supplies the local Meshulam occupancy cap.  The separate `q = 10` gap remains `45` versus `40`.
No P-versus-NP conclusion follows.

### Bollobas order-event exclusivity is now kernel checked

The permutation route to the remaining weighted set-pairs inequality has passed its first
structural test.  `BooleanSubcube.AllBefore r A B` records that every member of `A` precedes every
member of `B` in an asymmetric relation.  The generic theorem
`allBefore_events_pairwiseExclusive` proves that, whenever

```text
Disjoint (A_i, B_j) <-> i = j,
```

the order events for two distinct indices cannot both occur.  Its proof extracts one element of
each cross-intersection and obtains both `a < b` and `b < a`.  The specialized theorem
`fixedTrueVars_allBefore_events_pairwiseExclusive` instantiates this result directly on the
already-constructed pairs

```text
(fixedTrueVars (c i), x \ trueSupport (w i)).
```

Thus there is no additional compatibility gap between the private-point construction and the
standard permutation proof of Bollobas' inequality.  The precise next frontier is the remaining
enumeration lemma: for disjoint finite `A,B`, count the permutations (or induced orders on
`A ∪ B`) satisfying `AllBefore` and prove that their fraction is exactly
`1 / choose(|A| + |B|, |A|)`.  Pairwise exclusivity will then sum those fractions to at most one,
which feeds the verified reciprocal interval aggregation and yields the local Meshulam occupancy
cap.  The separate `q = 10` gap remains `45` versus `40`.  No P-versus-NP conclusion follows.

### The exact two-block shuffle fraction is now kernel checked

The binomial enumeration inside the remaining permutation argument is no longer implicit.
`BooleanSubcube.firstPositions a b` is the initial `a`-block of `Fin (a + b)`, while
`AllSelectedBefore S` states that every selected position precedes every unselected position.
The theorem `allSelectedBefore_eq_firstPositions` proves that an `a`-element pattern satisfying
this condition must be the initial block.  Consequently `allFirstPatterns_eq_singleton` and
`card_allFirstPatterns` show that exactly one of the

```text
choose(a + b, a)
```

possible rank patterns is favorable.  The rational capstone `allFirstPatterns_fraction` records
the exact required weight

```text
1 / choose(a + b, a).
```

Thus the numerical denominator in the weighted Bollobas argument is now proved, including the
empty-block edge cases; it is not a factorial estimate.  The precise next frontier is to define
the rank-pattern map from ambient permutations to the positions occupied by `A` inside `A ∪ B`,
prove all fibers have equal cardinality, and prove that `AllBefore` is the preimage of the unique
favorable pattern.  Combining that transport with the already-proved pairwise exclusivity yields
the weighted Bollobas inequality, which then feeds the verified reciprocal interval aggregation
into the local Meshulam occupancy cap.  The separate `q = 10` gap remains `45` versus `40`.
No P-versus-NP conclusion follows.

### The order event is now identified with the unique favorable rank pattern

The structural transport half of the remaining permutation argument is now kernel checked.
For disjoint finite blocks `A,B`, `BooleanSubcube.leftBlock` and `rightBlock` place both blocks
inside the finite subtype on `A ∪ B`.  Any equivalence

```text
e : (A ∪ B) ≃ Fin (a + b)
```

then defines `inducedRankPattern A B a b e`, the positions occupied by `A`.  Its cardinality is
exactly `|A|`.  The theorem `allBefore_iff_allSelectedBefore_inducedRankPattern` proves that the
strict order induced by `e` puts all of `A` before all of `B` exactly when every selected rank
precedes every unselected rank.  Specializing `|A| = a`, the capstone
`allBefore_iff_inducedRankPattern_eq_firstPositions` identifies this event with the preimage of
the unique initial-block pattern counted in the preceding section.

This closes the event/preimage identification, including empty-block cases, and makes explicit
that ambient coordinates outside `A ∪ B` are irrelevant.  The precise next frontier is the one
remaining counting statement: prove that the map from rankings `e` to `inducedRankPattern` has
uniform fibers (equivalently, construct the postcomposition bijection between the fibers over any
two `a`-patterns).  That gives the exact event fraction; transporting ambient permutations to
relative rankings and summing the already pairwise-exclusive events then yields weighted
Bollobas.  The separate `q = 10` gap remains `45` versus `40`.  No P-versus-NP conclusion
follows.

### The favorable relative rankings now have an exact factorial count

The favorable relative-order enumeration can be discharged directly, without first proving
uniformity of every shuffle-pattern fiber.  For disjoint finite blocks `A,B`,
`numbering_isPrefix_leftBlock_allBefore` proves that every numbering in which the copy of `A` is
an initial block realizes the required `AllBefore` event.  Mathlib's prefix-numbering
decomposition then gives the exact capstone

```text
|prefixed(leftBlock A B)| = |A|! * |B|!.
```

This count includes empty-block cases and depends only on the relative union: coordinates outside
`A ∪ B` are absent.  Since the full relative-ranking space has size `(|A|+|B|)!`, the usual
reciprocal-binomial weight is now available by the factorial route as well as by the previously
checked unique-pattern route.  Full uniformity of all induced-pattern fibers is therefore not
needed for the favorable event itself.

The precise next frontier is the ambient transport needed to put all indices into one common
permutation space: prove that restricting an ambient numbering to the relative order on `A ∪ B`
has uniform fibers, so each prefix event retains the exact relative fraction.  Then the already
proved pairwise exclusivity sums those fractions to the weighted Bollobas inequality.  The
separate `q = 10` gap remains `45` versus `40`.  No P-versus-NP conclusion follows.

### The exact favorable relative-order event is now kernel checked

The preceding factorial count proved the size of the prefix family and only the implication from
prefix rankings to the `AllBefore` event.  That was not yet enough to identify the event's exact
size.  The missing converse is now proved by
`numbering_isPrefix_leftBlock_iff_allBefore`: after casting a numbering of `A ∪ B` to
`Fin (|A| + |B|)`, the already-verified unique favorable rank pattern forces `A` to be precisely
the initial prefix.  This works unchanged when either block is empty.

The new finite event `allBeforeNumberings A B` is therefore exactly
`Numbering.prefixed (leftBlock A B)`.  Its cardinality is

```text
|A|! * |B|!
```

and its `ℚ≥0` density is exactly

```text
1 / choose(|A| + |B|, |A|).
```

Thus the relative favorable-event fraction, rather than merely a favorable subfamily count, is
now established.  The precise next frontier remains the genuinely ambient step: construct the
relative-order restriction from a common numbering of the full coordinate type and prove that
its fibers are uniform (or directly prove preservation of the density above).  Pairwise
exclusivity can then sum these exact weights to weighted Bollobas.  The separate `q = 10` gap
remains `45` versus `40`.  No P-versus-NP conclusion follows.

### Ambient numberings now restrict canonically to relative order

The structural half of the ambient transport is now kernel checked.  For an ambient numbering
`e : Numbering alpha` and finite set `S`, `relativeRanks e S` records the occupied ambient ranks.
`ambientRelativeNumbering e S` sorts those ranks and replaces each element of `S` by its position
in the sorted list.  The theorem `ambientRelativeNumbering_lt_iff` proves the exact comparison
interface

```text
ambientRelativeNumbering e S x < ambientRelativeNumbering e S y
  <-> e x < e y.
```

Consequently `allBefore_ambientRelativeNumbering_iff` transports every two-block `AllBefore`
event between the common ambient numbering and the induced numbering on `A union B`, without a
disjointness assumption and including empty unions.  This closes the subtype and order-preservation
plumbing; it does not yet establish that every relative numbering has equally many ambient
extensions.

The precise next frontier is now only the counting half of ambient transport: prove that every
fiber of `fun e => ambientRelativeNumbering e S` has cardinality

```text
choose(|alpha|, |S|) * (|alpha| - |S|)!
```

or directly prove that preimages preserve the density of `allBeforeNumberings`.  Combining that
with the already-proved event transport and pairwise exclusivity yields weighted Bollobas.  The
separate `q = 10` gap remains `45` versus `40`.  No P-versus-NP conclusion follows.

### Ambient relative-order fibers now have the exact extension count

The counting half of ambient transport is now kernel checked.  For a finite ambient type `alpha`,
a finite subset `S`, and any relative numbering `r : Numbering S`, the new theorem
`card_ambientRelativeFiber` proves

```text
|{e : Numbering alpha | ambientRelativeNumbering e S = r}|
  = choose(|alpha|, |S|) * (|alpha| - |S|)!.
```

The proof first constructs an ambient relabeling that transports any relative numbering to any
other.  Precomposition by this permutation gives an explicit bijection between arbitrary fibers,
so all fibers have equal cardinality.  Summing those fibers over all `|S|!` relative numberings
and using the exact `|alpha|!` ambient numbering count yields the displayed formula.  Empty and
full subsets require no separate cases.

This closes the last stated ambient-counting gap.  The precise next frontier is to package the
fiber formula and `allBefore_ambientRelativeNumbering_iff` into an exact ambient-event density
theorem, then sum the already pairwise-exclusive events to obtain the weighted Bollobas
inequality.  That inequality can then feed the verified reciprocal interval aggregation into the
local Meshulam occupancy cap.  The separate `q = 10` gap remains `45` versus `40`.
No P-versus-NP conclusion follows.

### The weighted Bollobás inequality is now kernel checked

The exact ambient fiber count has now been converted into the common-permutation statement
needed by the local Meshulam argument.  For finite disjoint blocks `A,B`, the new ambient event

```text
ambientAllBeforeNumberings A B
```

consists of the numberings of the full coordinate type that place every element of `A` before
every element of `B`.  Its membership is exactly the preimage of `allBeforeNumberings A B` under
`ambientRelativeNumbering`.  Summing the already-uniform fibers proves its exact cardinality and
density; the coordinates outside `A ∪ B` cancel, leaving

```text
dens(ambientAllBeforeNumberings A B)
  = 1 / choose(|A| + |B|, |A|).
```

The capstone `weighted_bollobas` then combines this density formula with the previously proved
pairwise exclusivity of the ambient order events.  For every finite family satisfying

```text
Disjoint (A i) (B j)  <->  i = j,
```

it proves

```text
sum_i 1 / choose(|A i| + |B i|, |A i|) <= 1.
```

This closes the permutation-counting and summation gap, including empty-block cases.  The precise
next frontier is to specialize `weighted_bollobas` to the private-point pairs
`(fixedTrueVars (c i), x \ trueSupport (w i))`, rewrite the second-block cardinality, and feed
that pointwise reciprocal bound into `finite_reciprocal_cover_card_le`.  That will establish the
local occupancy cap required by `meshulam_global_of_local_ball_bound`; only then should the
`q = 8,9,10` consequences be reassessed.  The previously recorded `q = 10` arithmetic gap remains
`45` versus `40`.  No P-versus-NP conclusion follows.

### The local Bollobás occupancy cap is now kernel checked

The private-point specialization and reciprocal aggregation are now complete.  For each ambient
`k`-set `x`, `privateToEndSlice_local_reciprocal_le` restricts to the subcubes whose
private-point-to-end intervals contain `x` and applies `weighted_bollobas` to

```text
A_i = fixedTrueVars(c_i),
B_i = x \ trueSupport(w_i).
```

The existing private-point lemma supplies the exact diagonal disjointness condition.  Exact slice
enumeration and `|x| = k` identify the Bollobás denominator with the interval-slice cardinality,
including varying values of `|trueSupport(w_i)|`.

The slices are then embedded losslessly into the finite type of all ambient `k`-sets.
`privatePoint_family_card_le_choose` feeds the pointwise reciprocal inequality into
`finite_reciprocal_cover_card_le` and proves

```text
|I| <= choose(|alpha|, k)
```

for a homogeneous irredundant family of dimension `k` whenever every displayed private point has
support at most `k`.  This support premise is exactly the local Hamming-ball condition after a
coordinatewise translation sending the chosen ball center to zero.

The precise next frontier is to formalize that coordinatewise Boolean translation for subcubes,
show that it preserves dimension and private points while converting Hamming distance from an
arbitrary center into true-support size, and thereby discharge the `hlocal` premise of
`meshulam_global_fin_of_local_ball_bound`.  Only after that composition should the `q = 8,9,10`
consequences be reassessed.  The separate `q = 10` gap remains `45` versus `40`.
No P-versus-NP conclusion follows.

### The arbitrary-center Meshulam bridge is now kernel checked

Coordinatewise Boolean translation now closes the remaining local-to-global interface.
`translatePoint center a` records whether `a` disagrees with `center`, while
`translateSubcube center c` applies the same involution to every fixed value.  The proved
translation lemmas show that:

```text
fixedVars (translateSubcube center c) = fixedVars c
Contains (translateSubcube center c) (translatePoint center a) <-> Contains c a
trueSupport (translatePoint center a) = {i | a i != center i}.
```

For a fixed center, `privatePoint_hammingBall_occupancy_le_choose` restricts to precisely the
members whose private points lie in its radius-`k` Hamming ball, translates that restricted
family to the all-false vertex, and invokes `privatePoint_family_card_le_choose`.  It proves the
previously assumed pointwise occupancy cap

```text
|{i | center in booleanHammingBall (w i) k}| <= choose(|alpha|, k).
```

The capstone `BooleanSubcube.meshulam_global_fin` feeds this result directly into
`meshulam_global_fin_of_local_ball_bound`.  Thus every homogeneous irredundant family of
dimension `k` subcubes on `Fin n` now satisfies

```text
|I| * sum_{j=0}^k choose(n,j) <= 2^n * choose(n,k)
```

without an external local premise.

The precise next frontier is to compose this unconditional global theorem with
`exists_subfamily_codimensionTwo_refinement` and the existing arithmetic specializations.  That
should remove the explicit `hmeshulam` premises from the eight- and nine-coordinate Hall
exclusions, while the ten-coordinate arithmetic remains a genuine `45` versus `40` gap requiring
additional structure.  No P-versus-NP conclusion follows.

### Eight- and nine-coordinate Hall exclusions are now unconditional

The unconditional Meshulam theorem now composes with the localized codimension-two refinement.
The reusable theorem `BooleanSubcube.meshulam_global` extends the `Fin n` formulation to every
finite coordinate type; its Hamming-ball volume is proved directly by counting finite subsets.
This lets the Hall argument work on the exact subtype of coordinates touched by the selected
subfamily, without choosing or transporting an external numbering.

For an inclusion-minimal outside-competitor core whose selected clauses have width at most two,
the new theorems

```text
InclusionMinimalUnsatisfiableCore.not_widthTwo_subfamily_density_failure_eight
InclusionMinimalUnsatisfiableCore.not_widthTwo_subfamily_density_failure_nine
```

construct the selected family's private-point subcubes, refine every member to codimension two,
apply the arbitrary-finite-coordinate Meshulam inequality, and discharge the existing exact
arithmetic.  Consequently no selected Hall subfamily on exactly eight or nine incident queried
coordinates can exceed the load-four budget.  There is no longer an explicit `hmeshulam` premise
at either support size.

The precise next frontier is the ten-coordinate structural gap.  Homogeneous Meshulam alone
gives `|s| <= 45`, whereas load four requires `|s| <= 40`; the verified compatibility of 45 means
that merely replaying the same global inequality cannot close this case.  The next high-value
step is to identify and formalize an additional constraint satisfied by localized firing fibers
but absent from arbitrary irredundant codimension-two subcubes, then test whether it removes at
least five members at `q = 10`.  No P-versus-NP conclusion follows.

### Ten-coordinate failures are narrow and deletion-redundant

The first structural reduction beyond the raw Meshulam count is now kernel checked.  The theorem
`widthTwo_tenSupport_card_window_of_density_failure` composes the unconditional localized
codimension-two refinement with Meshulam at ten coordinates and proves that every actual
load-four Hall failure lies in the exact window

```text
41 <= |s| <= 45.
```

More importantly, `biUnion_erase_eq_of_loadFour_deletionMinimalFailure` isolates a property that
the global cardinality inequality does not see.  For any deletion-minimal load-four Hall failure,
deleting one member preserves the entire incident union.  The circuit-specialized capstone
`widthTwo_tenSupport_deletionMinimalFailure_structure` packages both conclusions: a minimal
ten-coordinate obstruction has 41--45 members, and every one-member deletion still touches all
ten coordinates.  Equivalently, no retained competitor is the unique carrier of any incident
queried coordinate.

This does not close the five-member gap: incidence redundancy alone has not yet been combined
with the private-point set-pairs argument.  The precise next frontier is to minimize an arbitrary
Hall-failing subfamily under deletion (and transport the already-proved exclusions for support at
most nine to show that its union remains ten), then strengthen the local Bollobas/Meshulam count
using the resulting no-private-incidence condition.  A useful target is a local occupancy deficit
of at least five relative to the generic 45-member extremum.  No P-versus-NP conclusion follows.

### Arbitrary ten-coordinate failures now reduce to minimal ten-coordinate obstructions

The deletion-minimization step and its support-retention interface are now kernel checked.
The generic theorem `exists_subset_loadFour_deletionMinimalFailure` extracts from any finite
load-four Hall failure a failing subfamily `t` such that every one-member deletion satisfies the
Hall bound.  It uses well-founded strict inclusion on finite sets and makes no circuit-specific
assumptions.

The circuit capstone

```text
InclusionMinimalUnsatisfiableCore.exists_tenSupport_deletionMinimalFailure_structure
```

starts with an arbitrary width-two failure on ten incident queried coordinates.  Under the
explicit hypothesis that every core member has a nonempty incident queried set, it proves the
existence of `t` contained in the original family with all of the following properties:

```text
|union(t)| = 10,
41 <= |t| <= 45,
deleting any p in t preserves union(t).
```

Support retention is not assumed.  The small-support cutoff first gives `|union(t)| >= 5`; the
unconditional exclusions at support sizes 5, 6, 7, 8, and 9 then force equality with ten.  This
also records why the nonempty-incidence premise is material: without it, the existing cutoff
does not exclude a degenerate failure below support five.

Thus deletion minimality is no longer an external premise at the ten-coordinate frontier.  The
remaining five-member gap is genuinely structural.  The precise next frontier is to transport
the no-private-incidence conclusion through the localized codimension-two refinement and
identify its set-pair consequence inside the weighted Bollobas/Meshulam argument.  The target is
an occupancy or global deficit of at least five from the generic cap of 45; a first useful audit
is whether no-private incidence forbids equality in one or more local reciprocal inequalities.
No P-versus-NP conclusion follows.

### No-private incidence does not make the local bound strict

The proposed first strictness route has now been audited and ruled out by a kernel-checked
extremal stress test.  The family `positivePairSupportsTen` consists of all 45 unordered
coordinate pairs on ten coordinates.  Each pair indexes the positive codimension-two subcube
fixing precisely those two coordinates to true, and the point supported exactly on that pair is
private to its member.

This family already has the deletion-redundancy property extracted from a minimal Hall failure:

```text
union(s \ {p}) = all ten coordinates   for every p in s.
```

Nevertheless the local occupancy inequality is sharp.  At the all-false center, all 45 pair
private points lie in the radius-eight Hamming ball, and

```text
local occupancy = 45 = choose(10, 8).
```

Thus no-private incidence, even together with exact codimension two, injective indexing, and
displayed private points, cannot force strictness in the local Bollobas/Meshulam cap.  The failed
route is preserved explicitly rather than hidden: the missing five-member deficit must use a
property of localized circuit firing fibers that excludes the complete positive-pair family,
not merely incidence redundancy after homogenization.

The precise next frontier is to compare the complete positive-pair stress test against the
pre-refinement localized fibers.  In particular, audit whether deletion-witness assignments,
literal polarities, protected target support, or the fact that refinement may add fixed
coordinates imposes a compatibility constraint absent from arbitrary positive pair cubes.  The
next useful theorem should isolate one such circuit-specific invariant before attempting any
new counting inequality.  No P-versus-NP conclusion follows.

### Full-core firing fibers cover, but Hall subfamilies need not

The first pre-refinement distinction is now kernel checked.
`InclusionMinimalUnsatisfiableCore.localizedOutsideTermFires_cover` proves that the original
localized firing fibers of the entire unsatisfiable competitor core cover every Boolean
assignment on any chosen queried support.  The proof extends the queried assignment by false
off-support; if every competitor failed to fire, that extension would hit every retained
outside clause, contradicting core unsatisfiability.  This statement is deliberately made before
codimension-two homogenization, since refinement shrinks fibers and need not preserve a cover.

The sharp stress test fails this invariant in the simplest possible way:
`positivePairSupportsTen_not_cover` proves that the all-false point belongs to none of the 45
positive-pair fibers.  Thus the complete positive-pair family cannot itself be the full
pre-refinement firing family of an unsatisfiable core.  This is a genuine circuit-origin
constraint absent from arbitrary irredundant subcubes.

The distinction does not yet close the ten-coordinate gap.  The 41--45 member object extracted
by the Hall reduction is a subfamily of the ambient minimal core, and an arbitrary subfamily need
not cover.  Therefore a direct cover count would silently strengthen the hypotheses and is not a
sound next step.

The resulting precise frontier is the local sparsity consequence of *ambient* minimal
unsatisfiability.  The verified SCC development already provides the 2-SAT implication relation
and satisfiability criterion.  The classical two-path proof for minimally unsatisfiable 2-CNF
(Choongbum Lee, *Electronic Journal of Combinatorics* 16 (2009), N3,
doi:10.37236/241) charges every indispensable clause to one of two simple contradiction paths.
Restricted to a Hall subfamily supported on `q` variables, each path has at most `2q - 1`
internal edges, suggesting exactly `|s| <= 4q - 2`, stronger than the required `4q`.
The next concrete step is to bridge semantic outside-literal signatures to the existing
`TwoSATFastSAT.Edge` representation and kernel-check simple contradiction-path extraction plus
the local internal-edge count.  No P-versus-NP conclusion follows.

### Width-two outside cores now enter the verified implication graph

The syntax and basic path boundary is now kernel checked in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  The polarity map
`outsideLiteralToTwoSAT` sends an outside occurrence to `(litVar ell, falValue ell)`, exactly the
literal made true by a competitor-hitting assignment.  Every nonempty semantic signature of
cardinality at most two is presented as one pair clause; singleton signatures repeat their one
literal, so unit clauses require no separate graph syntax.  `edge_singleton_outsidePairClause_iff`
proves that these clauses contribute exactly the two edges of the existing
`TwoSATFastSAT.Edge` relation.

At formula level, `outsideCoreTwoSATClauses` retains one pair clause per indexed core member, and
`hitsOutsideCompetitorCore_iff_twoSATClauses` proves exact assignment-by-assignment semantic
agreement.  Consequently `twoSat_outsideCore_iff` identifies the existing `TwoSat` predicate
with satisfiability of the original outside competitor core.  No graph model is duplicated.

For an inclusion-minimal unsatisfiable nonempty width-two core, the capstones

```text
exists_twoSAT_contradiction_reaches
exists_twoSAT_simple_contradiction_walks
```

extract a literal with reaches in both directions to its negation, erase cycles in both reaches,
and prove that the two simple walks have individual lengths at most `2n-1` and combined length at
most `4n-2`.  This establishes the graph-theoretic numerical budget in the ambient literal
universe.

The bound does not yet apply to an arbitrary Hall subfamily: two arbitrary contradiction walks
need not contain an edge from every indispensable clause, and the ambient `n` count must be
replaced by the subfamily's `q` incident variables for internal edges.  The precise next frontier
is therefore the minimality charging lemma from deletion witnesses: prove that every retained
pair clause is forced onto one of a suitably chosen pair of contradiction paths (or inject it into
their directed edge occurrences), then separate clauses of a queried Hall subfamily as internal
edges on its `2q` literal vertices.  That step would make the verified `4q-2` budget relevant to
the ten-coordinate obstruction.  No P-versus-NP conclusion follows.

### Deletion satisfiability now forces path coverage

The graph-theoretic charging step has now been isolated and kernel checked at the pair-clause
list level.  `TwoSATPathCharge.EdgeWalk.usedEdges` records the directed edge occurrences actually
traversed by an explicit walk; `usedEdges_length` proves that this list has exactly the walk
length; and `exists_of_usedEdges_subset` transports a walk whenever all of its used occurrences
survive in a second edge list.

`mem_implicationEdges_erase_of_ne` proves the exact deletion fact: an implication edge of `cls`
remains in `cls.erase c` unless it is one of the two directed edges contributed by `c`.  The new
capstone `clause_edge_used_of_twoSat_erase` then fixes any forward/backward contradiction walks
and proves that, if `cls.erase c` is satisfiable, at least one of `c`'s two directed edges occurs
on one of those walks.  Otherwise both walks transport through the erased formula and contradict
its satisfiability.  This matches the logical step in Lee's Proposition 1; the paths do not need
to be chosen specially.

This theorem deliberately assumes deletion satisfiability for the concrete pair-clause list.
The semantic competitor core supplies a deletion witness indexed by a core member, while
`outsideCoreTwoSATClauses` is currently a mapped attached list.  Applying the new charge therefore
still requires a representation lemma proving that the translated list is duplicate-free and
that erasing the clause translated from `p` has exactly the hitting semantics of `core.erase p`.
That interface must use the existing injectivity of semantic outside-literal signatures; silently
erasing a possibly duplicated pair clause would be unsound.

The precise next frontier is this indexed-deletion transport.  Prove pair-clause injectivity on
the attached minimal core, derive `TwoSat (outsideCoreTwoSATClauses ... |>.erase c_p)` from the
deletion witness for `p`, and instantiate `clause_edge_used_of_twoSat_erase` on the two verified
simple walks.  After that, count only charged edges whose two endpoints lie over the Hall
subfamily's `q` variables; simplicity should give the intended combined `4q-2` occurrence budget.
No P-versus-NP conclusion follows.

### Indexed core deletion now transports to concrete path coverage

The semantic-to-list deletion interface is now kernel checked.  The polarity encoding
`outsideLiteralToTwoSAT` is injective: variable and falsifying value recover the original
`Rung4Literal`.  Combining this with the existing minimal-core injectivity of unordered outside
signatures proves `coreOutsideClause_injective`, even though each two-element signature is
presented by a classically chosen order.  Consequently
`outsideCoreTwoSATClauses_nodup` establishes that the translated attached list contains exactly
one distinct pair clause per core member.

`twoSat_erase_coreOutsideClause` then transports the semantic deletion witness for every attached
member `p` directly to

```text
TwoSat ((outsideCoreTwoSATClauses ...).erase (coreOutsideClause ... p)).
```

The proof audits membership in the erased list rather than assuming a finset/list erasure
identity: list `Nodup` ensures that any surviving translated clause comes from a different
attached member, which the original deletion assignment hits.  The capstone
`coreOutsideClause_edge_used` composes this result with `clause_edge_used_of_twoSat_erase` and
proves that every retained core member contributes one of its two directed edges to either fixed
contradiction walk.  Thus the classical path-coverage statement now applies to the actual
semantic outside core, with no special path choice.

The precise next frontier is the localized counting injection.  For a Hall subfamily supported
on `q` queried variables, turn each covered member into a distinct directed used-edge occurrence,
prove its endpoints lie over those `q` variables, and use simplicity of the two walks to bound
their internal occurrences by at most `(2q-1) + (2q-1) = 4q-2`.  The key audit is that choosing
among a clause's two orientations and the two walks preserves injectivity at the occurrence
level.  No P-versus-NP conclusion follows.

### The two-walk charge is injective

The orientation-collision audit is now kernel checked.  A directed implication edge determines
its source literal after applying `neg` and its destination literal, hence remembers the
underlying pair clause up to swapping.  The theorem
`eq_of_shared_coreOutsideClause_edge` combines this observation with injectivity of the semantic
outside signatures: if two attached core members can both be charged to the same directed edge,
they are the same member, even if the two charges selected opposite clause orientations.

`TwoWalkUsedEdgeSlot` is the disjoint union of the directed edge values used by the fixed forward
and backward contradiction walks.  `coreOutsideEdgeCharge` chooses a covered slot for every core
member, and `coreOutsideEdgeCharge_injective` proves this choice injective.  The sum tag separates
the two walks; no orientation tag is needed.  Counting the finite slot type gives

```text
core.card <= forward.length + backward.length.
```

Repeated occurrences of the same directed edge only shrink the slot type, so this counting step
does not itself require walk simplicity.  Composing it with the previously extracted simple
contradiction walks proves the ambient semantic capstone

```text
InclusionMinimalUnsatisfiableCore.card_le_four_mul_sub_two:
  core.card <= 4*n - 2.
```

Thus the feared loss from choosing among two orientations and two paths does not occur, and the
classical minimally-unsatisfiable 2-CNF bound has now been transported end to end into the actual
outside-core representation.  This ambient theorem still counts all `2n` literals, however; it
does not by itself bound an arbitrary Hall subfamily by its smaller incident support.

The precise next frontier is endpoint localization.  For a Hall subfamily `s`, prove that the
edge charged from each `p in s` has both endpoint variables in
`s.biUnion (incidentQueriedVars target queried)`.  Then restrict the two injective charge images
to internal used-edge slots and prove that a simple walk has at most `2q-1` such slots over `q`
variables.  That composition would give `s.card <= 4q-2`, closing the remaining ten-coordinate
load-four obstruction.  No P-versus-NP conclusion follows.

### Hall-subfamily charges are now endpoint-localized

The semantic localization boundary is now kernel checked.  `TwoWalkUsedEdgeSlot.edge` forgets
only the forward/backward tag and membership proof of a charged slot.  The theorem
`CoreOutsideEdgeChargeValid.endpoints_mem_incidentQueriedVars` proves that both endpoint
variables of any valid charge lie in the charged member's `incidentQueriedVars`, under the
existing support premise that all of that member's outside variables are queried.  Its proof
recovers the two semantic outside literals from `coreOutsidePair_spec`; implication-source
negation changes polarity but not the variable.

The subfamily capstone

```text
coreOutsideEdgeCharge_endpoints_mem_incidentUnion
```

instantiates this fact for the chosen injective charge and places both endpoints in
`s.biUnion (incidentQueriedVars target queried)` for every `p : s`.  Thus no charged Hall member
can consume an edge slot whose source or destination variable lies outside its `q` incident
variables.  The global support hypothesis is material: without it, `incidentQueriedVars` is an
intersection with `queried`, and the claimed localization would not follow merely from clause
membership.

The precise next frontier is now purely the internal simple-walk count.  Define the finite set of
used directed edges whose two endpoint variables lie in a fixed nonempty `q`-variable set, prove
that a vertex-simple walk contributes at most `2q-1` such edge values, and restrict the already
injective subfamily charge into the sum of the forward and backward internal-edge sets.  This
would yield `s.card <= 4q-2` (with the empty-support case discharged separately) and close the
remaining ten-coordinate load-four obstruction.  No P-versus-NP conclusion follows.

### The load-four Hall obstruction is closed by localized simple-walk counting

The internal walk count and its Hall composition are now kernel checked.  Rather than first
formalizing the stronger but unnecessary `2q-1` estimate, `EdgeWalk.internalUsedEdges` filters
the distinct directed edge values of a walk to those whose two endpoint variables lie in a fixed
support.  On a vertex-simple walk, destination literals identify traversed edges injectively.
Since a `q`-variable support has exactly `2q` polarized literals,
`internalUsedEdges_card_le_two_mul` proves the sufficient bound

```text
internalUsedEdges.card <= 2 * support.card.
```

`coreOutsideInternalEdgeCharge` restricts the previously chosen subfamily charge to the sum of
the forward and backward internal-edge sets.  Forgetting the internal-support proofs recovers the
original charge, so injectivity is preserved.  Combining the two simple-walk bounds proves

```text
subfamily_card_le_four_mul_incidentUnion_twoSAT:
  s.card <= 4 * incidentUnion(s).card.
```

The empty-support case is automatic; no nonempty-support subtraction is needed.  A short bridge
derives the translated outside-signature nonemptiness from the existing nonempty-incidence
premise.  Consequently `exists_incidentCoordinateOwner_load_le_four` discharges the complete
capacitated Hall interface and produces an incident-coordinate owner whose every fiber has size
at most four.  Thus the former five-through-ten-coordinate case analysis is superseded for
width-two inclusion-minimal cores; the stronger `4q-2` refinement is no longer on the critical
path.

The precise next frontier is to thread this unconditional load-four owner into the canonical
multi-switching encoder that previously stopped at the ownership premise, then recompute the
realized-prefix key count and survivor-shell recurrence with owner multiplicity four.  The audit
must check whether the owner is used only extensionally (so the noncomputable Hall choice is
acceptable) or whether the encoder needs executable owner data.  No P-versus-NP conclusion
follows.

### Load four now has an exact extensional key alphabet

The Hall output has now been strengthened from a bare owner/fiber statement to the finite code
interface needed by counting.  `WidthTwoOwnedKey queried` is the product of an actually queried
coordinate with `Fin 4`.  Its cardinality is exactly

```text
4 * queried.card.
```

`InclusionMinimalUnsatisfiableCore.exists_incidentWidthTwoOwnedKeyEmbedding` constructs, for every
qualifying width-two minimal core, an injective map from its attached members into this alphabet;
the coordinate component is proved to lie in that member's genuine outside-target support.  The
proof extracts the injective capacitated-Hall slot assignment directly.  It is existential and
noncomputable, but all present uses are extensional (injectivity, incidence, and cardinality), so
no executable owner data is required for this local compression.

The exact length-`d` multiset alphabet is now recorded as `WidthTwoOwnedPrefixCode`, with

```text
card = choose(4*q + d - 1, d).
```

`widthTwoOwnedPrefix_balance` recomputes the conditional survivor-shell arithmetic: replacing the
old key count `A` by `4*q` requires density base

```text
4 * (w+1) * (4*q+1).
```

This does **not** yet re-encode the canonical prefix.  The current decoder compares globally
stable `(gate,term-position)` keys across two roots.  The Hall code is chosen for a
restriction-dependent minimal competitor core, and two roots need not expose definitionally the
same core or the same Hall matching.  Equality of their owned multisets therefore does not yet
recover equality of the original term keys.  This coherence gap, rather than executability or
the stars-and-bars arithmetic, is the remaining obstruction.

The precise next frontier is to construct a root-independent core/slot assignment for every
canonical witness position, or prove a transport theorem showing that equal prefix endpoints and
owned labels identify the two restriction-dependent cores and Hall codes.  Only after that
coherence theorem may `widthTwoOwnedPrefix_balance` replace the existing `(gate,term-position)`
factor in `commonShallowBad`; absent such a theorem, the load-four alphabet is a local cardinal
compression rather than a sound canonical encoder.  No P-versus-NP conclusion follows.

### Core and Hall choices are now canonical in their semantic inputs

The two apparent choice-level coherence problems have been removed.  In
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`,
`canonicalMinimalUnsatisfiableCore` chooses an inclusion-minimal subcore as a fixed function of
the target and full finite competitor pool.  Its subset and minimality specifications are proved,
and `canonicalMinimalUnsatisfiableCore_proof_irrel` shows that changing the proof of full-core
unsatisfiability cannot change the selected core.

Likewise, `incidentWidthTwoOwnedKeyEmbedding` chooses the load-four Hall embedding as a fixed
function of the exact target, core, queried set, and their verified structural premises.  The
new injectivity and incidence theorems expose its complete decoder-facing contract, while
`incidentWidthTwoOwnedKeyEmbedding_proof_irrel` proves that different minimality, support,
incidence, or width proofs yield exactly the same function.  Therefore Hall-matching
nonuniqueness is not an independent obstruction: once two roots transport to equal semantic
target/full-pool/queried data, they definitionally reuse the same canonical core and embedding
(up to proof irrelevance).

This does not yet prove that equal canonical-prefix endpoints produce equal semantic inputs.
The full competitor pool depends on the selected targets and their source gates, and the current
realized-prefix decoder still compares stable `(gate,term-position)` keys before those data have
been reconstructed.  The precise next frontier is now narrower: define the target/full-pool data
attached to a realized prefix and prove that endpoint plus the position component of the label
transports those data across roots.  If that is impossible, preserve a counterexample identifying
which of target identity, source-gate identity, or competitor-pool equality fails.  Only after
this transport may the canonical owned multiset replace the current global term keys in
`commonShallowBad`.  No P-versus-NP conclusion follows.

### Endpoint plus literal position does not transport target data

The proposed semantic-input transport is false at the current label interface.  The definition
`realizedPrefixTargetData` records, for each of the first `d` fresh witnesses, the selected target
clause together with its source-gate index.  The kernel-checked two-singleton counterexample

```text
endpoint_position_do_not_transport_realizedPrefixTargetData
```

uses two roots with one different free coordinate.  Both canonical one-query prefixes reach the
same all-false endpoint, and both have the identical width-one literal-position word (position
zero).  Nevertheless one witness originates in gate zero and the other in gate one, so their
source-gate/target-clause data differ.  The companion theorem
`endpoint_position_do_not_transport_realizedPrefixKeys` confirms that their stable
`(gate,term-position)` keys differ as well.

Thus proof irrelevance successfully canonicalizes the minimal core and Hall matching only *after*
the semantic inputs are known, but endpoint plus literal positions cannot supply those inputs.
The failure already occurs before any competitor pool or unsatisfiable core is formed; source-gate
identity is the first missing datum, and target identity fails with it.  Consequently the current
owned-key proposal is circular if it needs root-dependent Hall data to reconstruct the global key
that would identify that Hall data.

The precise next frontier is to test a hybrid coherent label that retains just enough stable
source identity to select a root-independent semantic problem while compressing only the remaining
competitor multiplicity into load-four owned slots.  Its decoder must be proved injective and its
alphabet recomputed; if the retained source component restores the full `G` factor, the Hall
compression gives no asymptotic improvement and this route should be recorded as quantitatively
closed.  No P-versus-NP conclusion follows.

### Stable source identity still does not select the semantic target

The proposed source-owned hybrid fails one interface earlier than its Hall-slot arithmetic.  The
new one-gate family `sameGateTwoTargetGates` contains the two singleton terms `x₀` and `x₁`.
Two roots free one coordinate each and fix the other false.  Their one-query prefixes have the
same all-false endpoint, the same unique source-gate word, and the same literal-position word
(position zero), but select different target clauses.  The kernel-checked capstones

```text
endpoint_sourceGate_position_do_not_transport_realizedPrefixTargetData
endpoint_sourceGate_position_do_not_transport_realizedPrefixKeys
```

show respectively that target data and the existing stable keys differ.  Thus retaining `Fin G`
does not make the semantic core or Hall embedding root-independent: term position is also needed
before either can be selected.

The abstract counting theorem `stableTermKey_card_le_of_leftInverse` records the quantitative
consequence.  Any finite label admitting a decoder that is a left inverse on all stable
`Fin G × Fin m` keys has cardinality at least `G*m`.  Therefore a hybrid compatible with the
current decoder cannot replace the original key alphabet by `Fin G × (queried × Fin 4)`:
the stable `(gate,term-position)` datum already incurs the complete rectangular factor, and an
owned Hall slot can only add information.  The load-four theorem remains a valid local
compression of a fixed semantic core, but this particular route for turning it into a coherent
realized-prefix encoder is quantitatively closed.

The precise next frontier is to change the decoder interface rather than add another component to
the label.  A viable route must reconstruct the prefix from a root-independent semantic quotient
that does not first decode syntactic term identity, while preserving exact canonical-tree order;
the existing subsumption and permutation counterexamples must be respected.  Failing such a
quotient, return to the verified realized-prefix encoder and audit whether its exact ragged
alphabet and survivor schedule suffice under a structural bottom-occurrence bound.  No
P-versus-NP conclusion follows.

### Distinct semantic targets retain the full stable-key lower bound

Changing the decoder's codomain from syntactic keys to a root-independent semantic type does not
give a uniform compression.  The abstract kernel-checked theorem
`stableTargetMeaning_card_le_of_decoder` assumes only that each stable `(gate,term-position)` key
has a semantic meaning, those meanings are pairwise distinct, and decoding an encoded label
recovers that meaning.  It concludes

```text
G*m <= card(label alphabet).
```

This strictly weakens the earlier left-inverse premise: the decoder need not reconstruct the
syntactic key at all.  Consequently the lower bound is not an artifact of the current decoder
interface.  A semantic quotient can reduce the alphabet only to the extent that the concrete
family contains provable semantic collisions; families of pairwise distinct targets still pay the
entire ragged occurrence count (and a rectangular family can still realize `G*m` distinct
targets).  The permutation examples show that useful semantic collisions do occur, while the
subsumption examples show that exploiting them requires changing the canonical walk rather than
merely relabeling its existing witnesses.

The precise next frontier is therefore family-structural rather than another abstract quotient:
either prove a roundwise bound on the number of distinct canonical target meanings below the live
dimension and rebuild the walk over that normal form, or change the shell injection so that it
does not encode one independently decodable target per prefix witness.  Without one of those new
ingredients, the verified ragged occurrence obstruction remains sharp on distinct-target
families.  No P-versus-NP conclusion follows.

### Width one already realizes the full distinct-meaning obstruction

The pairwise-distinct premise in `stableTargetMeaning_card_le_of_decoder` is now realized by a
concrete canonical gate family, rather than left as an abstract worst case.
`rectangularDistinctSingletonGates G m` has `G` gates, exactly `m` positive singleton clauses in
each gate, and ambient dimension `G*m`.  The product equivalence assigns a separate coordinate to
every stable `(gate,term-position)` key.  The membership theorem
`rectangularDistinctSingletonGates_width_one` proves that every target has bottom width one.

More importantly, `rectangularDistinctSingletonSemantics_injective` proves that the resulting
`G*m` clauses compute pairwise distinct Boolean functions: evaluating at the assignment supported
on one key's coordinate separates it from every other key.  Therefore
`rectangularDistinctSingleton_card_le_of_semanticDecoder` specializes the semantic decoder lower
bound to this actual family:

```text
G*m <= card(label alphabet).
```

Thus no uniform sub-live bound on distinct target meanings follows from bounded width,
duplicate-freeness, or semantic quotienting alone; width-one families can already attain one
distinct meaning per live coordinate and one per syntactic occurrence.  Any useful roundwise
collision theorem must exploit an additional circuit invariant that excludes this independent
singleton family.

The precise next frontier is to identify such an invariant in the outputs of the layered
`collapseRound` recurrence and prove that it forces a sub-occurrence target-meaning bound, or to
abandon independently decodable per-witness targets and construct a joint shell injection.  The
verified singleton family should remain as the regression obstruction for any proposed uniform
normal-form compression.  No P-versus-NP conclusion follows.

### The singleton obstruction is produced by an actual collapse round

The range of `collapseRound` alone does not exclude the width-one distinct-meaning obstruction.
For positive `G,m`, `rectangularDistinctSingletonPredecessor G m` is a genuine `AltO 4` circuit:
an outer `gOr`, one `gAnd` per row, and one positive singleton DNF per rectangular key.  The
kernel-checked theorem `rectangularDistinctSingletonPredecessor_altO` proves this alternation
invariant explicitly, including the nonempty-gate requirements.

At fuel one and the all-live restriction,
`collapseRound_rectangularDistinctSingletonPredecessor` computes the round exactly:

```text
collapseRound 1 allLive predecessor = rectangularDistinctSingletonRoundOutput G m.
```

The local theorem `collapseRound_positiveSingletonDnf` proves the basic switch from a singleton
DNF to the corresponding singleton CNF.  The inner `gAnd` merge concatenates the `m` singleton
CNFs in each row; the outer `gOr` does not merge those CNF children.  Finally,
`bottomGates_rectangularDistinctSingletonRoundOutput` identifies the output bottom-gate list
definitionally with `List.ofFn (rectangularDistinctSingletonGates G m)`.

Combining that exact range witness with the preceding semantic injection shows that even the
positive-polarity half of a bona fide round output can contain `G*m` pairwise distinct width-one
target meanings.  Therefore no collision theorem can follow merely from being an `AltO` circuit
produced by one `collapseRound`, nor from the already tracked width, duplicate, and semantic
normalization invariants.  Any useful extra invariant must depend on narrower global history—for
example the survivor schedule, the relation between the live dimension and the original circuit's
occurrence budget, or a multi-round conservation law—not just the syntactic range of the round
operator.

The precise next frontier is to audit those genuinely global recurrence invariants against this
new exact range counterexample.  If none forces a sub-live occurrence bound, the remaining viable
route is a joint shell injection that encodes the prefix without independently decoding one target
meaning per witness.  The exact collapse-output family should remain as a regression test.  No
P-versus-NP conclusion follows.

### Original occurrence conservation and live dimension are both saturated

The first global-invariant audit is now exact.  In
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`, the predecessor and its one-round output
satisfy

```text
bottomClauseCount predecessor = G*m,
bottomClauseCount output      = G*m,
bottomGates output            = G,
stars allLive                 = G*m.
```

The combined theorem
`rectangularDistinctSingletonRoundOutput_saturates_global_budgets` records that the output's
occurrence count is simultaneously equal to the original predecessor occurrence count and to the
current live dimension.  Hence neither bare conservation of bottom-clause occurrences nor the
non-strict invariant `occurrences <= live` forces any collision or sub-live encoder alphabet:
both bounds can be tight on a genuine `collapseRound` output whose width-one targets have pairwise
distinct meanings.

This does not yet rule out a recurrence invariant with quantitative slack.  In particular, the
verified shell schedule operates after extending restrictions and may enforce a strict gap between
the current live shell and the inherited occurrence budget.  The precise next frontier is to pad
the construction with already-fixed ambient coordinates and realize the same saturation at a
non-root extending restriction, or prove that the intended survivor schedule excludes that padded
state.  If saturation remains realizable inside the actual schedule, scalar occurrence/live
history is exhausted and the next route is a genuinely joint prefix injection.  No P-versus-NP
conclusion follows.

### Non-root restriction extension still saturates both scalar budgets

Padding does not create the hoped-for quantitative slack.  For arbitrary `pad`, `G`, and `m`, the
new restriction `paddedRectangularRestriction pad G m` fixes the first `pad` ambient coordinates
to false and leaves the right-hand `G*m` coordinates live.  It extends the all-live root, and for
`pad > 0` the extension is strict.  The corresponding predecessor places the independent positive
singletons only on those surviving coordinates.

The local theorem `collapseRound_positiveSingletonDnf_of_free` first removes the artificial
all-live premise from the singleton computation: any still-free positive singleton switches to
its singleton CNF at fuel one.  The capstone
`paddedRectangularRoundOutput_saturates_global_budgets` then proves, for positive `pad`, `G`, and
`m`, all of the following together:

```text
allLive < paddedRectangularRestriction,
AltO 4 predecessor,
collapseRound 1 paddedRestriction predecessor = output,
bottomClauseCount output = bottomClauseCount predecessor = G*m,
stars paddedRestriction = G*m.
```

Thus saturation is not a root-shell artifact.  It survives after an arbitrary positive number of
ambient coordinates have already been fixed, on an actual `collapseRound` state.  Bare scalar
history consisting of inherited bottom-occurrence budget and current live dimension is therefore
exhausted: neither conservation nor passage to a non-root survivor shell forces a strict gap.

The precise next frontier is to compare this padded state with the *specific probabilistic shell
schedule* used by the iteration, including its required live-density relation to the original
ambient dimension.  Either prove that schedule assigns the padded saturated states negligible
weight for a reason stronger than scalar occurrence/live totals, or proceed to a joint prefix
injection that does not decode an independent target for every witness.  The padded construction
must remain as the regression obstruction.  No P-versus-NP conclusion follows.

### The exact survivor schedule admits a saturated padded state

The live-density comparison is now kernel-checked at an exact schedule point.  In
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`, the theorem
`paddedRectangularRoundOutput_realizes_actual_schedule` instantiates the linear ragged-alphabet
schedule at

```text
M = 10,  s = 0,  r = 1,  j = 0,
live dimension = 164000,
survivor shell = 20,
two-polarity key cap = 40.
```

Taking `pad = 163980`, `G = 1`, and `m = 20` gives a strict extension of the all-live root whose
twenty surviving coordinates carry twenty independent singleton clauses.  Its genuine
`collapseRound` output still satisfies

```text
bottomClauseCount output = stars restriction = 20,
stars restriction = layeredRoundActualShell 10 0 1 0,
normalized two-polarity total length <= layeredRoundActualKeyCap 10 0.
```

The new helper `paddedRectangularSingletonRoundOutput_bottomWidth_one` verifies the schedule's
residual width hypothesis, and the capstone additionally applies
`normalizedLayered_commonShallowBad_scaled_le_actual_schedule` to this exact circuit family.
Thus the density relation and the global half-shell contraction theorem are both compatible with
the saturated state; the intended schedule does not exclude it merely by ambient dimension,
shell membership, width, occurrence count, or normalized alphabet cap.

This theorem does not show that the particular restriction is itself in `commonShallowBad`, nor
does existence of one shell point refute the global contraction bound.  It isolates the remaining
question correctly: any negligibility proof for saturated states must use a finer structural
statistic that correlates with badness, rather than the audited scalar schedule interfaces.
Absent such a statistic, the precise next frontier is a joint prefix injection that reconstructs
the canonical prefix without independently decoding one target meaning per witness.  The exact
scheduled state should remain as the regression test.  No P-versus-NP conclusion follows.

### The exact scheduled saturated state is genuinely bad

The compatibility gap in the preceding audit is now closed for the concrete regression family.
The theorem `paddedRectangularRoundOutput_schedule_restriction_mem_bad` proves that the same
restriction used by `paddedRectangularRoundOutput_realizes_actual_schedule` is an actual member of

```text
commonShallowBad (normalizedLayeredBottomFamily C) 20 20 10 0.
```

The proof is semantic and does not reduce a large canonical tree.  Follow an alleged depth-ten
common trunk on the all-false assignment.  Its query path contains at most ten coordinates, so it
misses one of the twenty surviving singleton coordinates.  Flipping that unqueried coordinate
reaches the same trunk leaf.  The positive packed singleton DNF is false on the first assignment
and true on the second, whereas residual canonical depth zero would make its tree constant.
Canonical-tree correctness applies because restriction extension preserves the twenty-unit fuel
bound.

Consequently saturation is not merely compatible with the scheduled bad-set estimate: at least
one exact scheduled saturated state is bad.  This rules out any proposed negligibility argument
whose only mechanism is to show that saturated states are automatically good.  It still does not
show that saturated bad states have large shell mass; the verified global contraction theorem is
fully consistent with this individual bad point.

The precise next frontier is therefore quantitative: characterize and count the shell family of
saturated bad states (the natural next test is to generalize the packed-singleton argument across
support sets and polarities), or construct the joint prefix injection that avoids independently
decoding one target meaning per witness.  Any finer structural statistic must distinguish a
negligible saturated-bad class, not merely separate saturation from badness.  No P-versus-NP
conclusion follows.

### The scheduled obstruction fills its entire fixed-support polarity fiber

The single bad schedule point is not isolated in the Boolean values assigned off its live
support.  In `ComputationalDepthMultiSwitchingTwoSATBridge.lean`, the support-local theorem
`scheduledSingletonSupport_not_commonShallow` now takes an arbitrary restriction `sigma` with

```text
freeVars sigma = scheduledSingletonSupport
```

and rules out a depth-ten common trunk with residual depth zero.  The proof reuses the semantic
missed-coordinate argument, but its base assignment is now derived from `sigma`; no value of any
of the other 163980 coordinates is inspected.  The finset wrapper
`scheduledSingletonSupport_fiber_mem_bad` puts every such restriction in the exact scheduled bad
event, while the previous concrete restriction is recovered as a corollary.

The capstone `scheduledSingletonSupport_bad_card_lower_bound` counts this fiber.  The standard
fixed-free-set equivalence gives exactly two choices for each of the 163980 fixed coordinates, and
the support-local inclusion therefore proves

```text
2^163980 <= |scheduledSingletonBad|.
```

Thus arbitrary padding polarities do not suppress the obstruction at all.  Relative to the whole
20-star shell, this particular fixed-support fiber accounts for one of the `choose(164000,20)`
possible live supports, so the result does not show a nonnegligible shell density.  It identifies
the remaining quantitative question sharply: all possible saving must come from how rarely the
circuit's packed singleton support occurs among shell supports, not from assignments on its fixed
complement.

The precise next frontier is to move the packed singleton construction across a large family of
20-element live supports while keeping one fixed scheduled circuit, and count how many such
supports retain a gate with more than ten live independent singleton coordinates.  Equivalently,
compute the support-overlap tail for the circuit's singleton blocks and compare it with the
verified half-shell contraction.  If circuit-fixed support variation remains negligible, return
to the joint prefix injection.  No P-versus-NP conclusion follows.

### The support-overlap criterion is polarity-sensitive

The packed-singleton argument now moves beyond one fixed live support.  The theorem
`scheduledSingletonSupport_not_commonShallow_of_live_false` proves that an arbitrary scheduled
20-star restriction is bad whenever more than ten of the circuit's twenty singleton coordinates
remain live and every other singleton coordinate is fixed false.  The wrapper
`scheduledSingletonSupport_mem_bad_of_live_false` places every such restriction in the exact
scheduled bad finset.  Values on all coordinates outside the packed gate remain irrelevant.

This is the correct support-overlap statement for the positive singleton DNF.  A raw overlap count
alone would be false: fixing even one nonlive singleton coordinate true makes that positive OR
constant.  Thus the remaining count must retain the polarity condition.  For an overlap of `q`,
the support multiplicity is `choose(20,q) * choose(163980,20-q)`, but only the assignment fibers
whose other `20-q` packed coordinates are false are certified by this theorem.

The precise next frontier is to formalize that hypergeometric sum for `q = 11,...,20`, multiply
each support class by its exact admissible fixed-assignment fiber, and compare the resulting mass
with both the full 20-star shell and the verified half-shell contraction.  If this certified tail
is negligible, the packed circuit is only a regression test and the joint prefix injection again
becomes the main route.  No P-versus-NP conclusion follows.

### The polarity-sensitive tail now has an exact overlap-class partition

The countable event itself is now formalized in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  The finset
`scheduledSingletonCertifiedTail` contains exactly the scheduled restrictions with more than ten
live packed singleton coordinates and with every remaining packed coordinate fixed false.
Together with `scheduledSingletonSupport_mem_bad_of_live_false`, its membership theorem gives a
pointwise kernel-checked inclusion in the scheduled bad event.

For every natural `q`, `scheduledSingletonCertifiedOverlap q` fixes the packed live-overlap to
exactly `q`.  The theorem `scheduledSingletonCertifiedTail_eq_biUnion_overlap` proves the exact
partition

```text
scheduledSingletonCertifiedTail
  = biUnion q in Icc 11 20, scheduledSingletonCertifiedOverlap q.
```

This removes ambiguity about the range and polarity event before the cardinality calculation.
An independent exact-integer audit of the intended summands

```text
choose(20,q) * choose(163980,20-q) * 2^(163960+q)
```

shows that their sum is approximately `2^-139.5908` of the full twenty-star shell.  Multiplying
by the verified `2^10` contraction factor leaves approximately `9.75623e-40` of the shell.  This
numeric audit is not yet a Lean theorem: the new Lean result establishes the exact finite
partition to which the count must be applied.

The evidence therefore strongly indicates that the packed singleton obstruction is negligible
at the audited schedule and should remain a regression test rather than the main route.  The
precise next frontier is to prove the per-class cardinality formula above and a kernel-checked
comparison with `choose(164000,20) * 2^163980`.  Once that closes, return to the joint prefix
injection (or find a different bad family with materially larger shell mass).  No P-versus-NP
conclusion follows.

### The certified tail now has an exact kernel-checked cardinality

The per-class stars-and-bars calculation is now proved in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  The theorem
`scheduledSingletonCertifiedOverlap_card` gives, for every `q ≤ 20`,

```text
|scheduledSingletonCertifiedOverlap q|
  = choose(20,q) * choose(163980,20-q) * 2^(163960+q).
```

The proof reuses two existing exact bijective counts rather than introducing a second restriction
encoding.  `scheduledSingletonOverlapFreeSets_card` counts the live packed and padding coordinates
through the generic occupancy fiber, while `scheduledSingletonFalseRoot_fiber_card` counts the
fixed-value fiber as extensions of the root that forces the `20-q` nonlive packed coordinates
false.  The overlap classes are proved disjoint, and `scheduledSingletonCertifiedTail_card` sums
the formula exactly over `q = 11,...,20`.

The normalized coefficient comparison is also kernel checked:

```text
sum q=11..20,
  choose(20,q) * choose(163980,20-q) * 2^(q-10)
    < choose(164000,20).
```

This is `scheduledSingletonCertifiedTail_coefficient_lt`.  Its proof avoids evaluating
`choose(164000,20)` recursively: it bounds the smaller binomials by powers, multiplies by `20!`,
and compares against the 20-factor descending factorial.  A direct theorem restating the result
with the common factor `2^163980` was attempted, but Lean's kernel recursion limit was reached
while checking the enormous power expression; that failed presentation route is intentionally
not treated as a theorem.  The exact tail count and normalized inequality already isolate the
remaining step as power-factor bookkeeping, not combinatorial uncertainty.

The precise next frontier is to package the common-power cancellation as a small generic lemma
with a symbolic exponent and instantiate it without forcing kernel reduction of `2^163980`.
After that presentation-level bridge closes, the packed singleton family should return to its
role as a regression test and work should resume on the joint-prefix injection.  No P-versus-NP
conclusion follows.

### Symbolic cancellation closes the certified-tail regression audit

The large-power presentation is now kernel checked in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  The generic theorem
`finset_sum_mul_two_pow_add_lt_mul_two_pow` restores an opaque common factor `2^k` to a strict
finite-sum inequality.  Its proof uses positivity and distributivity only, so the kernel never
evaluates the common power.

Instantiating it at `k = 163970`, with the overlap exponent written as `q - 10`, proves

```text
|scheduledSingletonCertifiedTail| < choose(164000,20) * 2^163970.
```

The theorem `scheduledSingletonCertifiedTail_mul_two_pow_ten_lt_shell` then gives the exact
requested contraction comparison

```text
|scheduledSingletonCertifiedTail| * 2^10
  < choose(164000,20) * 2^163980.
```

Thus the polarity-sensitive packed-singleton bad family is rigorously negligible relative to the
verified half-shell target: even after paying the full `2^10` contraction factor, its certified
mass remains strictly below the complete twenty-star shell.  This closes the presentation-level
gap left by the normalized coefficient theorem and confirms that this construction is a useful
regression test, not the current quantitative obstruction.

The precise next frontier returns to the joint-prefix injection.  The highest-value next step is
to formulate a decoder for the whole canonical realized prefix from one shared structural code,
without assigning an independently decodable target meaning to every witness; the existing
endpoint/source-gate non-transport theorems and the saturated scheduled state remain mandatory
regression tests.  No P-versus-NP conclusion follows.

### A shared whole-prefix decoder still pays the complete independent-subset fiber

The proposed joint-prefix route now has an exact information-theoretic regression test in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  The theorem
`independentRealizedPrefix_sharedDecoder_card_lower_bound` allows an arbitrary finite label type,
one arbitrary shared code per root, and one arbitrary decoder returning the selected-variable set
of the entire prefix.  It does not assume a product label or independently decoded target meaning
at each witness.

On the independent singleton family, every `d`-subset is realized by a root whose full fresh
prefix selects exactly that subset, while every such root reaches the same all-false endpoint.
The decoder therefore makes its encoder injective on a fiber of exact size `choose(n,d)`, proving

```text
choose(n,d) <= |shared code alphabet|.
```

Consequently, merely replacing per-witness meanings by one opaque whole-prefix code cannot beat
the compatible-subset multiplicity in the worst case; the endpoint supplies no extra information
on this family.  This does not refute a decoder whose smallness is proved only on the actual bad
event: the packed-singleton audit already showed that the explicit saturated bad family can be
negligible in the scheduled shell.

The precise next frontier is to make the decoder bad-event-sensitive.  Formulate a shared code
only for roots in `commonShallowBad` and prove either (a) a structural bound on the number of
independent selected subsets that remain bad for one fixed circuit and endpoint, or (b) an
injective reconstruction whose alphabet is charged to a statistic of that bad fiber rather than
the full realized prefix.  The endpoint/source-gate examples and the scheduled saturated state
remain regression tests.  No P-versus-NP conclusion follows.

### Bad-event sensitivity alone does not shrink the independent-subset fiber

The shared-decoder regression test is now restricted to the actual semantic bad event in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  For `d > 0`,
`independentRealizedRoots_subset_commonShallowBad` proves that every root freeing exactly `d`
independent singleton coordinates belongs to

```text
commonShallowBad (independentLiteralGates n) 1 d (d-1) 0.
```

Consequently `independentRealizedRoots_inter_commonShallowBad` identifies the bad slice with the
entire realized common-endpoint fiber.  The capstone
`independentBadRealizedPrefix_sharedDecoder_card_lower_bound` allows an arbitrary shared finite
code and decoder whose correctness is assumed only on that intersection, yet still proves

```text
choose(n,d) <= |shared code alphabet|.
```

Thus merely restricting the whole-prefix decoder to `commonShallowBad` gives no worst-case
information saving: an actual bad event can retain every independent selected subset over the
same endpoint.  This does not contradict the shell contraction theorem, because the independent
family has one indexed gate per ambient coordinate and need not satisfy its small-alphabet density
premise.

The precise next frontier is therefore to make bad sensitivity *density-aware*.  For one fixed
circuit and endpoint satisfying the verified actual-alphabet density premise, bound the number of
distinct realized prefix-variable sets in the bad fiber by a statistic controlled by the
normalized clause-occurrence alphabet; alternatively construct a density-admissible family that
still attains the independent-subset lower bound.  The independent family and the scheduled
saturated singleton state remain mandatory regression tests.  No P-versus-NP conclusion follows.

### The independent-subset obstruction is outside the actual-density regime

The first density-aware regression boundary is now kernel checked in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  The theorem
`independentLiteralGates_actualAlphabet_eq` proves that the independent-singleton family has exact
ragged clause-occurrence alphabet

```text
∑ g, |independentLiteralGates n g| = n.
```

Thus its full `choose(n,d)` bad common-endpoint fiber is bought by one genuine key for every
ambient coordinate; it is not a small-alphabet example hidden by rectangular padding.  The
capstone `independentLiteralGates_not_actualDensity` proves that for every positive shell `K` and
every declared width bound `w`, this family falsifies the exact premise used by the verified
actual-alphabet contraction:

```text
¬(4*(w+1)*(n+1)*K + K ≤ n+1).
```

Consequently the current independent-subset lower bound is not a density-admissible
counterexample.  Bad-event sensitivity alone remains insufficient, but the verified density
premise genuinely removes this particular saturated fiber rather than merely changing its
presentation.

The precise next frontier is to prove a structural bad-fiber bound under the strict
occurrence-versus-live gap forced by actual density.  The first candidate is to bound the union of
coordinates occurring in the normalized family by width times the ragged alphabet and count
realized `d`-prefix variable sets inside that support; then compare that support code with the
existing occurrence-multiset-plus-position encoder.  A density-admissible counterexample would
instead have to retain full compatible-subset multiplicity while using strictly fewer than one
clause occurrence per ambient live coordinate.  No P-versus-NP conclusion follows.

### The density-aware realized-prefix support alphabet is now bounded

The proposed support statistic is now kernel checked in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  The definitions
`clauseVariableSupport`, `gateVariableSupport`, and `familyVariableSupport` retain exactly the
coordinates occurring in the indexed DNF family.  The theorem `familyVariableSupport_card_le`
proves, for width bound `w` and exact ragged clause-occurrence alphabet

```text
A = ∑ g, |gates g|,
```

that the complete coordinate support has size at most `w*A`.  This bound permits arbitrary
coordinate reuse and duplicate literals, so it does not depend on a hidden cleanliness premise.

`freshTaggedPrefixVars_subset_familyVariableSupport` then proves directly from successful witness
decoding that every selected canonical-prefix coordinate lies in this support.  Consequently
`realizedPrefixVariableSets_card_le_choose_actualAlphabet` gives, for any collection of roots whose
fresh prefixes really have length `d`,

```text
|distinct realized prefix-variable sets| ≤ choose(w*A,d).
```

The semantic specialization
`commonShallowBad_realizedPrefixVariableSets_card_le` applies this bound to the actual
`commonShallowBad` event under the same long-trace premise already consumed by the verified
prefix encoders.  Thus density-aware bad-event sensitivity now has a concrete finite alphabet: the
independent-singleton regression reaches `choose(n,d)` only because there `w*A = n`, while a
small-occurrence family cannot realize arbitrary ambient `d`-subsets.

This theorem counts distinct selected-variable sets rather than roots.  The precise next frontier
is to pair this alphabet with the existing prefix-endpoint injection to obtain a complete bad-root
count, then compare its factor `choose(w*A,d)` against the existing
`(w+1)^d * (choose(A+d-1,d)+1)` occurrence-multiset-plus-position factor.  That comparison will
decide whether coordinate support yields a genuine quantitative improvement or only an alternate
presentation of the same information.  Existing endpoint/source-gate counterexamples and the
scheduled saturated singleton audit remain mandatory regression tests.  No P-versus-NP
conclusion follows.

### The support alphabet now gives a complete bad-root count

The density-aware support statistic is now paired with the existing endpoint reconstruction in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  The theorem
`commonShallowBadEndpointFiber_card_le_realizedPrefixVariableSets` proves that, at a fixed
budget-`d` endpoint, the map sending a bad root to its selected prefix-variable set is injective:
endpoint equality and selected-set equality recover the root restriction.

Summing this fiber bound over the exact residual shell gives the capstone
`commonShallowBad_card_le_shell_mul_choose_actualAlphabet`:

```text
|commonShallowBad|
  ≤ |{ τ : Restriction n // stars τ = K-d }|
      * choose(w * (∑g, |gates g|), d).
```

This is a complete bad-root estimate rather than only a count of distinct prefix sets.  It needs
no duplicate-clause hypothesis and works for any extending long-path assignment.  The comparison
is genuinely favorable in at least one fully symbolic regime:
`support_factor_strict_lt_realizedPrefix_factor_depth_one` proves for every `w,A` that at `d=1`,

```text
choose(w*A,1) < (w+1) * (choose(A,1)+1).
```

Thus the support code is not merely an alternate presentation of the old
occurrence-multiset-plus-position factor.  The exact comparison for arbitrary `d` remains open;
in the intended multi-round schedule `d` grows, so the depth-one separation alone does not yet
improve the verified contraction recurrence.

The precise next frontier is to prove or refute the general factor comparison

```text
choose(w*A,d) ≤ (w+1)^d * (choose(A+d-1,d)+1),
```

preferably by an explicit injection from support subsets to occurrence multisets plus literal
positions.  Then instantiate the smaller certified factor in the circuit-level normalized shell
contraction and re-audit the multi-round schedule.  Existing endpoint/source-gate counterexamples,
the independent-subset lower bound, and the scheduled saturated singleton audit remain mandatory
regression tests.  No P-versus-NP conclusion follows.

### The support factor is uniformly no larger, and is wired into the circuit interface

The open general comparison is now kernel checked in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  In fact
`choose_mul_le_pow_mul_multichoose` proves the stronger inequality

```text
choose(w*A,d) <= w^d * choose(A+d-1,d).
```

The proof multiplies by `d!`: `d! * choose(w*A,d)` is the falling factorial of `w*A`, bounded by
`(w*A)^d`; meanwhile `A^d` is bounded by the rising factorial
`d! * choose(A+d-1,d)`.  Positivity of `d!` then cancels the common factor.  Thus no bespoke
subset-to-multiset injection, optional-code symbol, or duplicate-clause premise is required.
The requested comparison with

```text
(w+1)^d * (choose(A+d-1,d)+1)
```

follows immediately as `support_factor_le_realizedPrefix_factor`.  Combined with the already
proved strict depth-one separation, the support factor is uniformly no worse and sometimes
strictly better than the realized-prefix factor.

The smaller count is also inserted into the normalized circuit layer.
`commonShallowBad_card_le_shell_mul_choose_actualAlphabet_of_le_fuel` discharges the extension and
long-trace premises using the canonical semantic bad assignment and ample fuel.
`normalizedLayered_commonShallowBad_card_le_shell_mul_choose_actualAlphabet` specializes this to
the exact normalized two-polarity bottom family, and
`normalizedLayered_commonShallowBad_scaled_le_of_support_balance` exposes the exact shell-balance
interface needed by schedule arithmetic.  These theorems require `BottomWidth` but no clause-list
`Nodup` hypothesis.

The precise next frontier is to prove the support-specific binomial shell balance at the intended
multi-round parameters, using `A <= layeredRoundActualKeyCap M s`, and compare the resulting live
scale against `layeredRoundActualScale`.  This will determine whether the removed optional and
position overhead merely improves constants or weakens the gate-bound/live-dimension
self-reference identified by the current recurrence audit.  Existing endpoint/source-gate
counterexamples, the independent-subset lower bound, and the scheduled saturated singleton audit
remain mandatory regression tests.  No P-versus-NP conclusion follows.

### The support-specific shell balance improves constants but not the self-reference

The exact binomial balance is now kernel checked in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  The theorem
`supportSubset_factor_le_pow` bounds the downward-shell factor, the support-subset label, and any
requested saving `e <= d` by

```text
2^d * choose(w*A,d) * 2^e <= (4*w*A)^d.
```

Consequently `supportSubset_balance_of_density` needs only

```text
(4*w*A)*K + K <= n+1,
```

instead of the realized-prefix premise with coefficient `4*(w+1)*(A+1)`.  The circuit theorem
`normalizedLayered_commonShallowBad_scaled_le_of_support_density` consumes this sharper premise
without a duplicate-clause hypothesis.

At `w=s+1` and `A <= layeredRoundActualKeyCap M s`, the new definitions
`layeredRoundSupportScale`, `layeredRoundSupportLive`, and `layeredRoundSupportShell` give a
half-shell schedule whose backward scale is

```text
5 * ((s+1) * layeredRoundActualKeyCap M s + 1).
```

`twenty_mul_layeredRoundSupportScale_le_actualScale` proves that the previous verified scale is at
least twenty times this one, and
`normalizedLayered_commonShallowBad_scaled_le_support_schedule` proves the corresponding
roundwise contraction.

The qualitative obstruction remains.  Theorems
`not_layeredRoundSupport_worstCase_density_of_live_le_gateBound` and
`layeredRoundSupport_gateBound_lt_live_of_density` prove that every nonempty support-density round
still requires `M < N`: a class-level gate cap that already dominates the current live dimension
cannot satisfy the sharper premise.  Thus the support code yields a real constant improvement,
but it does not weaken the recurrence's gate-bound/live-dimension self-reference.

The precise next frontier is structural rather than another shell constant: prove a roundwise
sublinear bound on the current circuit-owned support or bottom-slot measure after restriction and
collapse, or exhibit a density-admissible survivor family showing that no such bound follows from
the present invariants.  The existing saturated singleton construction is the first regression
case for either route.  No P-versus-NP conclusion follows.

### Current round invariants do not force sublinear circuit-owned support

The first structural regression test is now kernel checked in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  The theorem
`familyVariableSupport_rectangularDistinctSingletonGates` proves that the positive width-one
bottom family of the existing rectangular singleton construction owns every coordinate:

```text
familyVariableSupport (rectangularDistinctSingletonGates G m) = univ.
```

More importantly, `normalizedLayeredBottomFamily_rectangularRoundOutput_support` proves the same
statement for the exact duplicate-normalized two-polarity family consumed by the circuit shell
theorem.  Normalization cannot remove these distinct singleton clauses, and the positive half of
the circuit indexing already covers all `G*m` coordinates.  Combining this with the previously
verified exact collapse computation gives
`rectangularDistinctSingletonRoundOutput_support_saturates_live`:

```text
|familyVariableSupport (normalizedLayeredBottomFamily output)|
  = stars allLive
  = G*m.
```

Thus no pointwise sublinear support bound follows merely from width one, duplicate normalization,
the two-polarity circuit interface, alternating shape, being in the range of `collapseRound`, or
the tracked occurrence/live conservation laws.  This preserves the counterexample rather than
assuming the desired structural gap.

The precise next frontier is to seek a distributional or multi-round-history statement: prove
that large-support survivor states have sufficiently small shell mass after conditioning on the
actual restriction process, or construct a schedule-admissible family showing that even such an
average support bound fails.  A pointwise support-shrink lemma under the current invariants is now
ruled out.  The padded scheduled singleton state remains the mandatory first regression test.  No
P-versus-NP conclusion follows.

### The padded singleton obstruction survives the smaller support schedule

The mandatory regression test is now instantiated at the support-specific schedule rather than
only at the older stars-and-bars schedule.  In
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`,
`paddedRectangular_liveSupport_subset_familyVariableSupport` proves for arbitrary padding that
every live rectangular coordinate occurs in the exact duplicate-normalized two-polarity family.
Consequently
`stars_paddedRectangularRestriction_le_familyVariableSupport_card` gives

```text
stars paddedRestriction <= |familyVariableSupport normalizedRoundOutput|.
```

The capstone `paddedRectangularRoundOutput_realizes_support_schedule` specializes this at
`M = 10`, `s = 0`, `r = 1`, and `j = 0`.  The improved schedule has ambient dimension `4100`,
shell size `20`, and normalized key cap `40`.  One row of twenty independent singleton clauses,
padded by `4080` fixed coordinates, is a genuine non-root `collapseRound` output; it preserves
the bottom-occurrence/live equality, owns at least all twenty survivors, lies on the exact
support-specific shell, and still satisfies the verified global `2^10` bad-set contraction.

Thus the twenty-fold scale improvement does not itself create pointwise support shrink.  It is
consistent with full survivor support because its contraction is distributional.  The existing
hard-coded polarity-sensitive tail audit applies to the older `164000`-coordinate schedule, so it
does not yet quantify this smaller `4100`-coordinate regression case.

The precise next frontier is to parameterize the packed-singleton missed-coordinate and overlap
count by the padding size, instantiate it at `pad = 4080`, and compare its certified bad mass with
the `4100`-coordinate support shell.  This will decide whether the smaller schedule keeps the
same singleton family negligible or makes it a genuine average-support obstruction.  No
P-versus-NP conclusion follows.

### The padding-parametric overlap mass remains negligible at the smaller schedule

The packed-singleton overlap arithmetic is now parameterized by the number of fixed padding
coordinates in `ComputationalDepthMultiSwitchingTwoSATBridge.lean`:

```text
paddedSingletonCertifiedMass pad
  = sum_{q=11}^{20} choose(20,q) * choose(pad,20-q) * 2^(pad-20+q).
```

`scheduledSingletonCertifiedTail_card_eq_paddedMass` verifies that the previously certified bad
tail at ambient size `164000` is exactly the `pad = 163980` instance, so this is a genuine
generalization of the counted overlap mass rather than a disconnected estimate.

At the improved support schedule, `paddedSingletonCertifiedCoefficient_4080_lt` proves the exact
normalized coefficient inequality

```text
sum_{q=11}^{20} choose(20,q) * choose(4080,20-q) * 2^(q-10)
  < choose(4100,20).
```

After restoring the common power of two,
`paddedSingletonCertifiedMass_mul_two_pow_ten_lt_shell_4080` proves

```text
paddedSingletonCertifiedMass 4080 * 2^10
  < choose(4100,20) * 2^4080.
```

Thus shrinking the padding by a factor of forty does not turn this polarity-sensitive
packed-singleton tail into an average-support obstruction: its full parameterized overlap mass
still fits strictly below the shell after the same `2^10` saving.  The pointwise saturated state
remains real, but this particular tail is globally negligible at the new schedule.

The precise next frontier is to parameterize the *semantic membership bridge* itself (currently
the `scheduledSingletonSupport_not_commonShallow_of_live_false` theorem is specialized to
`pad = 163980`) and identify the exact bad set, not just this certified sufficient tail, at
`pad = 4080`.  If the sufficient criterion is also necessary, the singleton regression is fully
discharged distributionally; otherwise the missing bad profiles must be counted.  No
P-versus-NP conclusion follows.

### The semantic bad-set bridge is now padding-parametric

The packed support and semantic obstruction are now parameterized in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  For every `pad`,
`paddedSingletonSupport pad` is the set of the twenty packed singleton coordinates and has
cardinality exactly twenty.  The theorem
`paddedSingletonSupport_not_commonShallow_of_live_false` proves that any shell restriction with
twenty live coordinates is not common-shallow at trunk depth ten and residual depth zero whenever
more than ten packed coordinates remain live and every other packed coordinate is fixed false.
Its proof is semantic: a trunk path misses one live packed coordinate, and toggling that coordinate
changes the positive singleton DNF while leaving the reached trunk leaf unchanged.

`paddedSingletonBad pad` exposes the exact bad finset at ambient dimension `pad + 20`, and
`paddedSingletonSupport_mem_bad_of_live_false` turns the same criterion into membership in that
finset.  Thus the criterion now applies directly at `pad = 4080`; it is no longer connected to the
new coefficient calculation merely by a hard-coded semantic theorem.  The matching numerical
profile mass satisfies `paddedSingletonCertifiedMass_mul_two_pow_ten_lt_shell_4080`, strictly below
the `4100`-coordinate shell after the requested `2^10` saving.  A padding-parametric overlap
finset/cardinality theorem is still needed before identifying that numerical mass with the
cardinality of a concrete `pad = 4080` certified subset inside Lean.

This step proves sufficiency only.  It does not silently identify the certified subset with the
whole bad event: restrictions with a fixed-true packed coordinate, or with at most ten live packed
coordinates, have not yet been shown common-shallow.  Those profiles are preserved as the exact
unresolved converse rather than discarded.

The precise next frontier is to prove or refute the converse characterization at arbitrary
padding: construct a depth-ten common trunk with residual depth zero whenever the polarity-sensitive
criterion fails.  In parallel, parameterize the certified-overlap finset/cardinality bridge.  If
the converse succeeds, these two facts give the exact bad-set cardinality; if it fails, extract and
count the first additional bad profile at `pad = 4080`.  No P-versus-NP conclusion follows.

### The one-sided converse is false; the opposite monochromatic profile is also bad

The converse audit produced a concrete additional bad profile in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  The static support lemmas
`canonicalDT_queriedVars_subset_gateVariableSupport` and
`canonicalFamily_trace_length_le_live_support` show that a normalized common-family path charges
only coordinates that are both live and syntactically owned by the family.  The resulting generic
bridge `commonShallowAt_zero_of_live_support_le` proves residual depth zero whenever that live
support fits inside the trunk budget, even if many irrelevant ambient coordinates remain live.

For the padded singleton circuit, `normalizedPaddedSingleton_familyVariableSupport` identifies the
owned support exactly with `paddedSingletonSupport pad`.  Hence
`paddedSingletonSupport_commonShallow_of_live_le` proves the valid half of the converse: at most ten
live packed coordinates always admit the depth-ten common trunk.

The remaining proposed converse is false because the indexed circuit family contains both
polarities.  `paddedSingletonSupport_not_commonShallow_of_live_true` proves that more than ten live
packed coordinates are also bad when every other packed coordinate is fixed **true**.  The missed
coordinate toggles the negative singleton DNF, exactly symmetrically to the earlier positive-DNF
argument for fixed false coordinates.  `paddedSingletonSupport_mem_bad_of_live_true` inserts this
additional profile into the exact padding-parametric bad finset, including at `pad = 4080`.

Thus the earlier certified mass is not the whole bad event.  The evidence now suggests the exact
classification: a shell point is bad precisely when more than ten packed coordinates are live and
the fixed packed coordinates are monochromatic (all false or all true, with the all-live case
vacuously in both descriptions).  Mixed fixed polarities should be good because the positive and
negative singleton DNFs are already terminal at the root, but that final sufficiency statement is
not yet kernel checked.

The precise next frontier is to prove the mixed-polarity root-terminal certificate, combine it with
the live-support theorem and the two monochromatic obstructions into an iff characterization, and
then parameterize/count the union of the all-false and all-true overlap finsets at `pad = 4080`
(taking care of their all-live intersection).  No P-versus-NP conclusion follows.

### The padded singleton bad event is exactly the monochromatic union

The missing converse is now kernel checked in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  The theorem
`paddedSingletonSupport_commonShallow_of_mixed_fixed` constructs a zero-query common trunk as soon
as the fixed packed coordinates include both Boolean values: a fixed-true singleton makes the
positive indexed DNF terminal at the root, while a fixed-false singleton does the same for the
negative indexed DNF.  Duplicate normalization is transferred through the previously proved
canonical-tree equivalence.

Combining this root-terminal certificate with the live-support certificate and the two symmetric
semantic obstructions gives `mem_paddedSingletonBad_iff`.  For every padding size and every
restriction, membership in the exact bad finset is equivalent to

```text
stars sigma = 20
and more than 10 packed coordinates are live
and the fixed packed coordinates are all false or all true.
```

This closes the semantic classification without discarding the all-live corner: when all twenty
packed coordinates are live, both monochromatic conditions hold vacuously, so it is exactly the
intersection that must be subtracted when the two profile families are counted.

The precise next frontier is now purely combinatorial: define padding-parametric all-false and
all-true overlap finsets, prove that each has cardinality `paddedSingletonCertifiedMass pad`, prove
their intersection has cardinality `2^pad` (the all-packed-live profile), and derive

```text
|paddedSingletonBad pad| = 2 * paddedSingletonCertifiedMass pad - 2^pad.
```

Then instantiate `pad = 4080` and test the exact union, rather than a one-sided subset, against the
requested `2^10` shell contraction.  No P-versus-NP conclusion follows.

### The exact padded singleton union still contracts at the support schedule

The padding-parametric combinatorial audit is now complete in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  The concrete finsets
`paddedSingletonFalseTail pad` and `paddedSingletonTrueTail pad` record the two monochromatic
profiles from the semantic iff.  For every `20 <= pad`, fiberwise counting proves

```text
|paddedSingletonFalseTail pad| = paddedSingletonCertifiedMass pad,
|paddedSingletonTrueTail pad|  = paddedSingletonCertifiedMass pad.
```

The second equality is transported by the fixed-value complementation involution.  The theorem
`paddedSingletonFalseTail_inter_trueTail` identifies their intersection exactly with the fiber
whose free-variable set is the twenty packed coordinates, and
`paddedSingletonAllLiveFiber_card` counts that fiber as `2^pad`.  Combining this with the semantic
classification gives the exact formula

```text
|paddedSingletonBad pad|
  = 2 * paddedSingletonCertifiedMass pad - 2^pad.
```

The inclusion-exclusion correction is quantitatively decisive but does not break the desired
schedule.  At `pad = 4080`, `paddedSingletonExactCoefficient_4080_lt` verifies the normalized
integer inequality

```text
2 * paddedSingletonCertifiedCoefficient 4080 - 2^10 < choose(4100,20),
```

and `paddedSingletonBad_mul_two_pow_ten_lt_shell_4080` restores the common power to prove the exact
semantic bad union satisfies

```text
|paddedSingletonBad 4080| * 2^10 < choose(4100,20) * 2^4080.
```

Thus the mandatory padded-singleton regression is fully discharged distributionally at the
support-specific schedule: the pointwise saturated state exists, but the entire exact bad event,
including both polarities, remains below the required half-shell mass.

The precise next frontier is to lift this exact distributional lesson beyond singleton rows:
identify a structural class of normalized round outputs for which the support-shell bad event
admits a comparable polarity/profile decomposition, or construct the smallest width-two output
whose exact bad mass violates the `2^(10*r)` contraction.  The first regression target should be
two-literal disjoint blocks at `M = 10`, where residual depth and polarity interactions are
nontrivial but the support is still small enough for an exact shell count.  No P-versus-NP
conclusion follows.

### One disjoint width-two block per gate has no bad shell at all

The first width-two regression target is now kernel checked in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  The reusable tree
`queryRestrictionList` queries a prescribed coordinate list and records the resulting restriction
at each leaf; `queryRestrictionList_spec` proves that every reached leaf extends the root and agrees
with the followed total assignment.

For ten pairwise-disjoint two-literal blocks, `paddedDisjointPairFamily pad` is the exact
twenty-index family consisting of the ten positive blocks and their termwise-negated polarities.
The explicit trunk queries the first coordinate of each pair.  The local lemmas
`positiveOrderedPair_depth_le_one_of_first_fixed` and
`negativeOrderedPair_depth_le_one_of_first_fixed` prove that fixing that coordinate leaves the
corresponding canonical tree with depth at most one, for arbitrary root restrictions and fuel.
Consequently `paddedDisjointPairFamily_commonShallow` proves

```text
CommonShallowAt (paddedDisjointPairFamily pad) fuel sigma 10 1
```

for every `pad`, `fuel`, and `sigma`.  Thus `paddedDisjointPairBad_eq_empty` identifies the entire
twenty-live-coordinate bad event with the empty finset, and the padding-parametric theorem
`paddedDisjointPairBad_mul_two_pow_ten_lt_shell` gives the requested `2^10` contraction with zero
left side, including at `pad = 4080`.

This rules out the simplest width-two counterexample more strongly than an exact profile count:
one width-two clause per bottom gate can spend one trunk query per gate and reduce both indexed
polarities to residual depth one.  Disjointness is retained in the regression construction, but
the mechanism shows that overlap is not the source of difficulty at this clause count.

The precise next frontier is the first clause-rich width-two circuit-owned family for which the
number of clauses exceeds the ten-query transversal budget.  At `M = 10`, audit ten disjoint
bottom gates with two disjoint width-two clauses each (twenty clauses total), using the exact
normalized positive/termwise-negative family.  Either find a smaller shared transversal/common
trunk, or classify and count its first genuinely bad support-shell profiles against the `2^10`
contraction.  No P-versus-NP conclusion follows.

### The first clause-rich width-two family has a certified forty-query baseline

The two-clause local interface is now kernel checked in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  The definitions `positiveTwoPairGate` and
`negativeTwoPairGate` describe the two termwise polarities of a gate containing two disjoint
width-two clauses.  The lemmas `positiveTwoPair_depth_eq_zero_of_four_fixed` and
`negativeTwoPair_depth_eq_zero_of_four_fixed` prove the baseline polarity-symmetric certificate:
fixing all four owned coordinates makes either indexed gate terminal, for arbitrary ambient
dimension, restriction, and fuel.

This local cost is genuine for the obvious static transversal.  The exact finite computation
`positiveTwoPair_first_coordinates_true_depth_eq_two` shows that fixing only the first coordinate
of each clause true leaves positive canonical depth exactly two.  Thus the earlier one-query-per-
clause idea does not itself meet residual threshold one.

`paddedTwoPairFamily pad` is the requested exact twenty-index family of ten disjoint gates, two
clauses per gate, and both termwise polarities on forty owned coordinates.  Querying all four
coordinates per gate gives

```text
CommonShallowAt (paddedTwoPairFamily pad) fuel sigma 40 1
```

for every padding, fuel, and root restriction.  Consequently
`paddedTwoPairBad_forty_eq_empty` proves that its forty-live-coordinate support-shell bad event is
empty when the trunk allowance is forty.  This is only a baseline upper bound: it does not replace the
target allowance ten and does not assert optimality against adaptive common trunks.

The precise next frontier is to obtain the first lower bound for adaptive trunks on this family.
Start with the four-coordinate, one-gate gadget: prove that trunk depth two cannot make both
polarities residual-depth one (the static all-true witness is not enough for arbitrary adaptive
trees).  Then tensor or charge that local obstruction across ten disjoint gates to classify the
depth-ten bad profiles and count them against the `2^10` contraction.  No P-versus-NP conclusion
follows.

### Exact shallow-leaf classification refutes the naive local invariant

The next proposed strengthening was tested exhaustively and is false.  It is not true that every
restriction leaving two of the four gadget coordinates live keeps one polarity at residual depth
at least two.  For example, fixing one coordinate of the first clause true and one coordinate of
the second clause false leaves a single live singleton in each polarity, so both canonical depths
are at most one.  This failed route is retained because it rules out a direct argument from live
coordinate count alone.

The replacement theorem `twoPair_both_depth_le_one_iff_opposite_cross_fixed` in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean` checks every restriction with at least two live
coordinates.  It proves an exact iff: both polarities are residual-depth one precisely when the
restriction fixes a coordinate in each clause and the two fixed values are opposite.  The earlier
all-true witness is one of the excluded equal-value profiles.

This sharpens the adaptive target.  A depth-two trunk would have to make every reached leaf certify
an opposite-valued cross-clause pair.  The precise next frontier is to prove that no binary
depth-two `CommonTree` agreeing with every total assignment can enforce that certificate on every
leaf of the all-live four-coordinate cube.  A generic path-information lemma plus the constant
all-true (or all-false) assignment should force an equal-valued queried profile; the exact iff then
supplies the residual-depth contradiction.  Only after kernel-checking this adaptive one-gate
lower bound should the obstruction be tensored or charged across ten disjoint gates.  No
P-versus-NP conclusion follows.

### The adaptive one-gate depth-two obstruction is kernel checked

The missing adaptive lower bound now follows from the exact leaf classification.  The definition
`twoPairPolarityFamily` packages the positive and termwise-negative forms of the four-coordinate,
two-clause gadget as the exact `Fin 2` family.  The theorem
`twoPairPolarities_not_commonShallowAt_two` proves

```text
¬ CommonShallowAt twoPairPolarityFamily 4 allFree 2 1.
```

The proof applies to an arbitrary common trunk, not merely a static query set.  It follows the
all-true assignment and records the coordinates queried on that path.  Trunk depth two bounds the
queried set by two.  Leaf agreement under single-coordinate flips proves every unqueried
coordinate remains live, so at least two coordinates are live at the reached restriction.
Agreement with the all-true assignment also proves that no fixed coordinate is false.  But
`twoPair_both_depth_le_one_iff_opposite_cross_fixed` says simultaneous residual depth at most one
requires a fixed false coordinate in one clause and a fixed true coordinate in the other.  This is
the desired contradiction.  The corollary `allFreeFour_mem_twoPairPolarityBad_two` places the
fully live restriction in the actual four-live semantic bad event.

This closes the first adaptive lower bound while preserving the earlier counterexample: arbitrary
two-live restrictions can make both polarities shallow when they already contain an
opposite-valued cross-clause certificate.  The argument succeeds specifically because a
monochromatic branch of an agreeing adaptive trunk cannot manufacture that certificate.

The precise next frontier is the disjoint-product charging lemma.  For ten four-coordinate
gadgets and a depth-ten trunk, follow a monochromatic assignment and relate the ten queried
coordinates to per-gadget costs: any gadget made residual-depth one must consume enough path
information to create its required cross-clause certificate.  Determine the sharp per-gadget
cost (the local theorem rules out cost at most two from the fully live root), then prove that the
global ten-query budget leaves a deep gadget or identify the smallest adaptive sharing pattern
that defeats this direct tensoring.  Only after that structural theorem should the corresponding
forty-live bad profiles be counted against the `2^10` shell contraction.  No P-versus-NP
conclusion follows.

### Paired-polarity disjoint-product charging is now structural

The reusable product step is now kernel checked in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  The definition `pairedPolarityFamily`
flattens two polarities of each of `G` gadgets into the exact `Fin (2*G)` family expected by
`CommonShallowAt`.  The theorem
`pairedPolarity_not_commonShallowAt_of_compatible_sum_deficit` charges query-path information to
the `G` underlying supports, rather than incorrectly treating the two same-support polarities as
disjoint.

Along the root-compatible all-true path, the existing weighted disjoint-support pigeonhole lemma
selects a gadget whose live-coordinate deficit exceeds the queries charged to it.  Leaf agreement
shows that unqueried root-live coordinates remain free and that no selected support coordinate is
fixed false.  A local semantic premise may then choose whichever of the two polarities remains
deep; the flattened family supplies the contradictory shallow bound for that exact polarity.

This establishes the general tensor/charging interface without assuming a static query set or
double-counting shared polarity supports.  For the fully live four-coordinate gadgets at residual
threshold one, the intended local deficit is three per gadget, so ten gadgets carry total charge
thirty against a depth-ten trunk.

The precise next frontier is to instantiate the paired theorem for `paddedTwoPairFamily`.  Prove
the ambient four-coordinate local lemma: if no owned coordinate is fixed false and at least two
owned coordinates remain live, then one of `positiveTwoPairGate` and `negativeTwoPairGate` has
canonical depth greater than one.  The `Fin 4` exact classification already proves its semantic
content; the remaining work is a restriction/reindexing bridge to arbitrary disjoint padded
coordinates.  Then compute the fully live deficit sum as thirty, derive that the exact forty-live
root is bad for trunk depth ten, and only afterward count a sufficiently large bad-profile class
against the `2^10` contraction.  No P-versus-NP conclusion follows.

### The fully live ten-gadget root is now in the depth-ten bad event

The padded product instantiation is kernel checked in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  The coordinate map is injective, each gadget
support has cardinality four, and the ten underlying supports are pairwise disjoint.

The charging theorem is generalized to separate its live-coordinate threshold from the residual
canonical-depth target.  This avoids overcommitting to the delicate two-live classification:
`positiveTwoPair_depth_ge_two_of_three_free` proves directly, by a two-step canonical replay, that
three free owned coordinates and no fixed-false owned coordinate force positive-polarity depth at
least two.  Each fully live gadget therefore contributes deficit `4 - 2 = 2`; ten gadgets give
total charge twenty against a depth-ten trunk.

Consequently `paddedTwoPairRestriction_not_commonShallow_ten` proves that the restriction fixing
the padding and leaving exactly the forty gadget coordinates live is not common-shallow at trunk
depth ten and residual depth one.  `paddedTwoPairRestriction_mem_bad_ten` places that exact root in
the semantic fixed-shell bad event.  The earlier two-live opposite-cross counterexample remains
preserved: this proof deliberately uses the sound three-live threshold rather than claiming it
away.

The precise next frontier is counting.  Define a substantial padding-parametric class of
forty-live profiles whose compatible threshold-two deficits still exceed ten, embed that class in
the bad event with the new theorem, and compare its exact cardinality with the ambient shell after
the required `2^10` saving.  The fully live root alone has negligible mass and does not challenge
the verified contraction.  No P-versus-NP conclusion follows.

### The fully-live profile fiber is exact but quantitatively insufficient

The first padding-parametric profile class is now kernel checked in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  The theorem
`paddedTwoPair_not_commonShallow_ten_of_support_free` strengthens the single-root result: the
padding may be fixed to arbitrary Boolean values, and every restriction leaving all forty gadget
coordinates live is still not common-shallow at trunk depth ten and residual depth one.

`paddedTwoPairFullyLiveFiber pad` packages exactly those roots.  The subset theorem embeds the
whole fiber in the semantic forty-live bad event, and the exact count is

```text
|paddedTwoPairFullyLiveFiber pad| = 2^pad.
```

This is a genuine exponential bad class, but its normalized mass is still too small.  For
`pad >= 3`, `paddedTwoPairFullyLiveFiber_scaled_lt_shell` proves

```text
|paddedTwoPairFullyLiveFiber pad| * 2^10
  < choose(pad + 40, 40) * 2^pad.
```

Thus arbitrary padding assignments supply no additional shell fraction: after cancelling the
common `2^pad`, the certified class contributes coefficient one, while the ambient choice of the
forty live coordinates contributes `choose(pad+40,40)`.  The current class therefore cannot
violate the desired contraction.

The precise next frontier is to admit partially consumed gadget supports.  Define and count the
profiles for which the sum over ten gadgets of the threshold-two compatible deficits remains
strictly above ten.  This requires tracking, per gadget, both its number of live coordinates and
whether every fixed owned coordinate is true; profiles killed by a fixed false coordinate
contribute zero.  The decisive comparison is the resulting finite coefficient sum against
`choose(pad+40,40)/2^10`.  If that sum remains below the shell, the next structural move is to add
the symmetric all-false charge and perform inclusion-exclusion; if it exceeds the shell, embed the
full class in the bad event.  No P-versus-NP conclusion follows.

### The exact partially-consumed deficit class is semantically certified

The counting target is now connected to the semantic bad event without a fully-live assumption.
`paddedTwoPair_not_commonShallow_ten_of_compatible_sum_deficit` proves that every restriction
`sigma` satisfying

```text
10 < sum_g compatibleResidualQueryDeficit(paddedTwoPairSupport pad, sigma, 2, g)
```

defeats every depth-ten common trunk at residual threshold one.  This is the exact statistic used
by the paired-polarity charging proof: a partially consumed gadget contributes `live - 2` only
when none of its fixed owned coordinates is false, and otherwise contributes zero.

`paddedTwoPairCompatibleDeficitProfiles pad` packages the forty-live shell points satisfying that
predicate.  The theorem `paddedTwoPairCompatibleDeficitProfiles_subset_bad` embeds the entire
class in `commonShallowBad`; hence the next finite coefficient calculation will not rely on a
surrogate event or require a later semantic repair.  The fully-live theorem is now a specialization
of this general profile criterion.

The precise next frontier is the exact cardinality of this certified class.  Partition each
four-coordinate gadget by live count and compatibility, convolve the resulting six local states
across ten gadgets, and attach the padding factor `choose(pad, 40-q) * 2^pad` at total owned-live
count `q`.  Compare the sum over total deficit at least eleven with
`choose(pad+40,40) * 2^pad / 2^10`.  If it is insufficient at the support-schedule padding, add the
symmetric all-false class and use inclusion-exclusion.  No P-versus-NP conclusion follows.

### The six local profile states are exact and exhaustive

The first counting layer is now kernel checked in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  The definition
`twoPairLocalCompatibleDeficit` is the canonical four-coordinate version of the threshold-two
compatible deficit: it is `stars - 2` when no owned coordinate is fixed false, and zero otherwise.
The corresponding profile classes have the exact table

```text
(owned live, deficit, multiplicity)
  (0, 0, 16), (1, 0, 32), (2, 0, 24),
  (3, 0,  4), (3, 1,  4), (4, 2,  1).
```

`twoPairLocalProfileMultiplicity_exact` proves all six cardinalities, while
`twoPairLocalProfileClass_partition` proves their union is the full restriction space.  Thus the
rows are exhaustive, and their multiplicities sum to `81 = 3^4`; no seventh local profile is
being silently omitted.

An exact-arithmetic audit of the ten-fold convolution gives nonzero deficit-at-least-eleven
coefficients only for owned-live totals `q = 23,...,40`.  At the support-schedule padding
`pad = 4080`, the resulting one-sided class, after the requested `2^10` scaling, is approximately
`4.52e-44` of the ambient forty-live shell.  This numerical audit is not yet the Lean cardinality
theorem, but it decisively indicates that the one-sided compatible class will be insufficient at
the intended schedule and preserves that failed quantitative route.

The precise next frontier is to formalize the ten-fold convolution and the transport from each
padded support to the canonical six-state table, proving the exact cardinality formula

```text
sum_q A(q) * choose(pad, 40-q) * 2^(pad-40+q),
```

where `A(q)` is the convolved deficit-at-least-eleven coefficient.  Then kernel-check the strict
insufficiency at `pad = 4080` and add the symmetric all-false class with inclusion-exclusion; the
one-sided class alone cannot approach the required contraction.  No P-versus-NP conclusion
follows.

### The aggregated ten-fold deficit convolution is exact and already insufficient

The arithmetic half of the convolution audit is now kernel checked in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  Aggregating the six exact local rows by
deficit gives the three-state distribution

```text
deficit 0: 76 states, deficit 1: 4 states, deficit 2: 1 state.
```

`twoPairDeficitConvolution` is the coefficient recurrence for
`(76 + 4*y + y^2)^g`.  The theorem `twoPairTenFoldDeficitTail_exact` proves that exactly
`333840111649` of the `81^10` ten-gadget local profiles have total compatible deficit at least
eleven.

The earlier exact-arithmetic audit observed that every contributing profile has at least 23 owned
live coordinates.  Even before formalizing that support statement, the final numerical comparison
has been isolated and kernel checked:

```text
333840111649 * choose(4080,17) * 2^40 * 2^10
  < choose(4120,40) * 2^40.
```

This deliberately overcharges every deficit-tail profile by the largest padding-choice factor
available once at most 17 padding coordinates are live.  Thus the exact bivariate coefficient
vector is no longer needed to decide the one-sided route: after the remaining semantic/support
transport is proved, this coarse bound already certifies strict insufficiency at `pad = 4080`.
The failed one-sided quantitative route is retained.

The precise next frontier is to prove the transport-and-support lemma: decompose an ambient
restriction into its ten padded four-coordinate states plus padding, show the six-state local
weights add to the ambient star count and compatible deficit, and prove deficit at least eleven
forces at least 23 owned-live coordinates.  That lemma will turn the coarse arithmetic certificate
into a cardinality upper bound for `paddedTwoPairCompatibleDeficitProfiles 4080`.  Then add the
symmetric all-false class and audit its union by inclusion-exclusion.  No P-versus-NP conclusion
follows.

### The ambient product decomposition is injective, and the 23-live proof is repaired

The transport layer is now kernel checked in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  `paddedTwoPairRestrictionCode` splits an
ambient restriction into its ten ordered `Restriction 4` gadget states and its ordered
`Restriction pad` padding state.  `paddedTwoPairRestrictionCode_injective` proves that this loses
no information.  The local pullback theorems identify, exactly, each gadget's live count,
all-true compatibility condition, and compatible deficit with the corresponding canonical local
profile statistics.

This audit also found and preserved a failed arithmetic route.  The pointwise inequality

```text
2 * local deficit <= local owned-live
```

only implies 22 owned-live coordinates when total deficit is eleven; it does **not** imply 23.
The defensible coarse consequence is now named
`paddedTwoPair_twentyTwo_le_ownedLive_of_ten_lt_deficit`.  The repaired
`paddedTwoPair_twentyThree_le_ownedLive_of_ten_lt_deficit` genuinely uses the transported local
state: a deficit-one gadget has three live coordinates.  If total deficit is at least twelve,
doubling gives 24; if it is exactly eleven, parity forces a deficit-one gadget, supplying the
missing coordinate.  Hence the needed statement is now valid:

```text
10 < sum_g compatible deficit(g)  ->  23 <= |owned-live|.
```

The decomposition also corrects the proposed cardinality factor.  A padding state with `r` live
coordinates has `choose(4080,r) * 2^(4080-r)` realizations, so a coarse upper bound carries
`2^4080`, not `2^40`.  The latter was safe only as a cancellable common factor inside the existing
arithmetic inequality.  `twoPairTenFoldDeficitTail_4080_padding_scaled_insufficient` now records
the same strict numerical comparison with the actual `2^4080` factor on both sides.

The precise next frontier is the filtered product count.  Map
`paddedTwoPairCompatibleDeficitProfiles 4080` through the proved injective code, bound the ten-local
projection by `twoPairTenFoldDeficitTail`, and count padding states with at most 17 live
coordinates (including their fixed Boolean values) to prove the corrected coarse bound

```text
|paddedTwoPairCompatibleDeficitProfiles 4080|
  <= twoPairTenFoldDeficitTail * choose(4080,17) * 2^4080.
```

Only after checking that padding factor exactly should it be combined with the arithmetic
insufficiency certificate.  Then add the symmetric all-false class and audit the union by
inclusion-exclusion.  No P-versus-NP conclusion follows.

### The ambient forty-star shell now transports exactly to at most seventeen padding stars

The remaining support-to-padding interface is now kernel checked in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  The theorem
`stars_paddedTwoPairRestrictionCode` proves the exact additive decomposition

```text
stars(σ) = stars(padding(σ)) + sum_g stars(local_g(σ)).
```

This is stronger than an inequality and matches the already proved injective product code: no
live coordinate is omitted or counted twice.  Combining it with the repaired 23-owned-live lemma
gives `paddedTwoPair_padding_stars_le_seventeen`: every member of the forty-star compatible
deficit tail has at most seventeen live padding coordinates.

An attempted direct wrapper around the existing cumulative-shell theorem for the concrete
4,080-coordinate padding count was not retained: elaborating the concrete restriction finset
exhausted recursion depth, and raising it far enough caused an OS stack overflow.  This is a Lean
resource failure, not a counterexample to the proposed numerical factor.  The semantic bridge and
the numerical scaling certificate remain valid independently.

The precise next frontier is now sharply separated into two finite counts.  First prove that the
ten-local filtered product has cardinality `twoPairTenFoldDeficitTail`, preferably through a
deficit-vector fiber equivalence rather than enumeration of `81^10` states.  Then count the
at-most-seventeen-star padding subtype in a small generic lemma (avoiding concrete `Fin 4080`
reduction during elaboration) and combine the two injections to obtain

```text
|paddedTwoPairCompatibleDeficitProfiles 4080|
  <= twoPairTenFoldDeficitTail * choose(4080,17) * 2^4080.
```

After that, apply the existing scaled insufficiency certificate and audit the symmetric all-false
union by inclusion-exclusion.  No P-versus-NP conclusion follows.

### The ten-local filtered product is now counted exactly

The local-to-arithmetic counting bridge is now kernel checked in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  The finset
`twoPairTenLocalDeficitTailProfiles` is the actual filtered product of ten canonical four-coordinate
restriction spaces, not a surrogate coefficient set.  `twoPairDeficitVector` maps each tuple to
its pointwise deficit vector in `Fin 3`.  Fiberwise counting over the `3^10` possible vectors then
factors each fiber as the product of ten local deficit classes.

The local class sizes are proved to be exactly `76`, `4`, and `1`, and the remaining weighted
`3^10` vector sum is kernel reduced to `333840111649`.  Consequently
`twoPairTenLocalDeficitTailProfiles_card` proves the desired semantic identification

```text
|{rho : Fin 10 -> Restriction 4 | 10 < sum_g localDeficit(rho_g)}|
  = twoPairTenFoldDeficitTail.
```

This route never enumerates the infeasible `81^10` tuple space.  It also confirms that the
previous recurrence has neither omitted nor overcounted any local restriction tuple.

The precise next frontier is the generic padding count.  Prove, without specializing the finite
type to `Fin 4080` during elaboration, that the restrictions on `pad` coordinates with at most
seventeen stars have cardinality at most `choose pad 17 * 2^pad` (for the needed monotonic range).
Then combine that bound, the injective ambient product code, the exact ten-local count, and
`paddedTwoPair_padding_stars_le_seventeen` to obtain the corrected coarse cardinality bound for
`paddedTwoPairCompatibleDeficitProfiles 4080`.  After applying the existing scaled insufficiency
certificate, audit the symmetric all-false union by inclusion-exclusion.  No P-versus-NP
conclusion follows.

### The generic at-most-seventeen-star padding bound is proved; the direct `3^10` reduction is not

The padding shell no longer requires elaborating a concrete `Restriction 4080` finset.
`paddingRestrictionsAtMostSeventeen_card` partitions the parametric restriction space into its
eighteen exact star layers:

```text
sum_{k < 18} choose(pad,k) * 2^(pad-k).
```

For `pad >= 50`, `two_pow_seventeen_sub_mul_choose_le_choose_seventeen` proves

```text
2^(17-k) * choose(pad,k) <= choose(pad,17)    (k <= 17).
```

Summing those eighteen estimates and using `18 <= 2^17` yields the requested sharp generic bound

```text
|{rho : Restriction pad | stars(rho) <= 17}| <= choose(pad,17) * 2^pad.
```

This proof is symbolic in `pad`, so the required `pad = 4080` instance does not trigger the prior
large-finite-type reduction failure.

The same compile audit found that the preceding claimed exact `3^10` weighted-vector reduction
had not in fact elaborated.  Its fiber factorization theorem remains kernel checked, but the final
plain `decide` exceeds recursion depth; increasing limits reaches a deterministic heartbeat limit
and then an OS stack overflow.  The unverified equality and its dependent exact-cardinality
capstone were therefore removed rather than leaving hidden `sorryAx`.  The failed direct-reduction
route is preserved here.  `twoPairTenLocalDeficitTailProfiles_card_le_full` records the safe
fallback bound by the complete `81^10` tuple space.

The precise next frontier is to prove the weighted `3^10` vector sum from the already verified
deficit-convolution recurrence structurally, rather than by enumeration.  In parallel, the weaker
`81^10` fallback may already suffice numerically: combine the injective ambient product code,
`paddedTwoPair_padding_stars_le_seventeen`, and the generic padding bound to obtain a resource-safe
coarse bound for `paddedTwoPairCompatibleDeficitProfiles 4080`, then test its scaled shell ratio.
Only after one of those routes is kernel checked should the symmetric all-false union be audited by
inclusion-exclusion.  No P-versus-NP conclusion follows.

### The full `81^10` fallback already closes the one-sided quantitative audit

The ambient filtered-product count is now kernel checked without enumerating either the ambient
restriction space or the weighted `3^10` deficit vectors.  The theorem
`paddedTwoPairCompatibleDeficitProfiles_card_le_product` maps every certified forty-star ambient
restriction through the proved injective product code.  Its local projection lies in
`twoPairTenLocalDeficitTailProfiles`, while its padding projection lies in
`paddingRestrictionsAtMostSeventeen`.  Consequently

```text
|paddedTwoPairCompatibleDeficitProfiles pad|
  <= |twoPairTenLocalDeficitTailProfiles|
       * |paddingRestrictionsAtMostSeventeen pad|.
```

Combining this bridge with the resource-safe full-space bound and the generic padding theorem gives,
for `pad >= 50`,

```text
|paddedTwoPairCompatibleDeficitProfiles pad|
  <= 81^10 * choose(pad,17) * 2^pad.
```

At `pad = 4080`, even this deliberately much larger charge is strictly below the required tenth-bit
shell fraction:

```text
|paddedTwoPairCompatibleDeficitProfiles 4080| * 2^10
  < choose(4120,40) * 2^4080.
```

Thus the failed direct `3^10` reduction and its possible structural recurrence repair are no longer
on the critical path for this one-sided construction.  The stronger exact coefficient would only
tighten a bound that already misses by a very large margin.

The precise next frontier is to construct the symmetric all-false compatible-deficit profile class,
prove its analogous product bound, and identify the intersection of the all-true and all-false
classes.  Inclusion-exclusion will then decide whether their union is still quantitatively
insufficient.  Preserve the failed direct weighted-vector reduction as a resource counterexample;
it need not be repaired unless a later parameter regime needs its sharper constant.  No
P-versus-NP conclusion follows.

### Even the doubled full-local-space charge is insufficient

The proposed inclusion-exclusion audit can now be decided without computing the intersection.
`two_mul_twoPairFullLocalSpace_4080_padding_scaled_insufficient` kernel checks the deliberately
strong overcharge

```text
2 * (81^10 * choose(4080,17) * 2^4080) * 2^10
  < choose(4120,40) * 2^4080.
```

`twoPair_two_coarse_profile_classes_union_scaled_insufficient` packages the consequence for any
two restriction classes satisfying the already proved one-sided product bound.  It uses only
`card(A union B) <= card(A) + card(B)`, so it assumes neither disjointness nor an intersection
formula.  Hence, if the symmetric all-false compatible-deficit class receives the analogous
resource-safe `81^10` product bound, its union with the all-true class is automatically too small;
subtracting their intersection can only strengthen the failure.

This changes the next frontier.  Construct the all-false semantic certificate and prove its
coarse product bound, but do not spend effort on exact inclusion-exclusion unless it is needed for
a different parameter regime.  Once the symmetric bound is connected to the semantic bad event,
the entire two-one-sided-profile strategy is quantitatively closed at the support schedule.  The
failed direct weighted-vector reduction remains preserved and off the critical path.  No
P-versus-NP conclusion follows.

### The symmetric all-false certificate closes the two-one-sided-profile route

The all-false class is now kernel connected to the semantic bad event.  The local theorem
`negativeTwoPair_depth_ge_two_of_three_free` proves the negative two-clause gate remains depth at
least two when three owned coordinates are live and no owned coordinate is fixed true.  The
generic theorem
`pairedPolarity_not_commonShallowAt_of_false_compatible_sum_deficit_threshold` follows the
all-false common-tree branch and reads its numerical charge from the complemented root
restriction.  Specializing it gives
`paddedTwoPairFalseCompatibleDeficitProfiles_subset_bad`.

Restriction complementation preserves the free set and is involutive.  Therefore
`paddedTwoPairFalseCompatibleDeficitProfiles_card` identifies the all-false class cardinality
exactly with the already counted all-true class; no duplicate local convolution or padding proof
is required.  In particular, both classes satisfy the same coarse bound

```text
81^10 * choose(4080,17) * 2^4080.
```

The actual union, not merely two abstract classes, is now certified both semantically and
quantitatively:

```text
true-compatible profiles union false-compatible profiles
  subset commonShallowBad(paddedTwoPairFamily 4080, shell 40, trunk 10, residual 1),

|true-compatible profiles union false-compatible profiles| * 2^10
  < choose(4120,40) * 2^4080.
```

Thus exact inclusion-exclusion cannot rescue this two-one-sided-profile strategy at the support
schedule.  Its overlap may still be computed for another parameter regime, but it is off the
critical path here.  The failed direct weighted `3^10` reduction also remains preserved as a Lean
resource counterexample.

The precise next frontier is to characterize bad restrictions not captured by either
monochromatic compatible-deficit class.  The highest-information test is a mixed-branch semantic
certificate or counterexample at one two-pair gadget, followed by a product charge only if that
local class survives.  This will decide whether genuinely adaptive mixed Boolean branches add
enough mass beyond the quantitatively closed all-true/all-false union.  No P-versus-NP conclusion
follows.

### A same-clause mixed profile survives, with exact local cost one

The first mixed-branch test is now kernel checked in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  The restriction
`twoPairSameClauseMixedRestriction` fixes the first clause to opposite Boolean values and leaves
the second clause live.  It lies outside both monochromatic compatibility conditions.  At its
root, both indexed polarities have canonical depth exactly two, so it is not common-shallow at
residual depth one with a zero-query trunk.

This lower bound is semantic rather than construction-specific:
`CommonShallowAt.root_shallow_of_trunkDepth_zero` proves generally that a depth-zero common trunk
cannot strengthen its root restriction.  Conversely,
`twoPairSameClauseMixedRestriction_commonShallowAt_one` explicitly queries one coordinate of the
live clause and proves both Boolean leaves make both polarities residual-depth at most one.
Therefore this previously uncharged local state has exact adaptive trunk cost one.

The result rules out the simplest mixed-profile counterexample: mixed fixed values do not make
every discarded gadget free.  It also shows that the monochromatic deficit `stars - 2` is not the
full local cost function; this two-live mixed state contributes one query despite contributing
zero to both existing one-sided charges.

The precise next frontier is to classify all 81 one-gadget restrictions by their minimum common
trunk cost in `{0,1,2}` and extract the exact multiplicities, preserving the already proved
opposite-cross zero-cost classification and this same-clause cost-one witness.  Only then should
that local distribution be convolved across ten disjoint gadgets and tested against the
forty-star padded shell.  No P-versus-NP conclusion follows.

### The fully live profile has exact local cost three

The proposed `{0,1,2}` classification range was incomplete.  The existing theorem
`twoPairPolarities_not_commonShallowAt_two` already rules out every common trunk of depth at most
two for the fully live four-coordinate restriction.  The new theorem
`twoPairPolarities_commonShallowAt_three` supplies the matching upper certificate: it queries both
coordinates of the first clause and one coordinate of the second, after which every Boolean leaf
makes both indexed polarities have residual canonical depth at most one.

Thus `twoPairPolarities_exact_trunk_cost_three` proves

```text
not CommonShallowAt(twoPairPolarityFamily, all-free, trunkDepth 2, residualDepth 1),
CommonShallowAt(twoPairPolarityFamily, all-free, trunkDepth 3, residualDepth 1).
```

By monotonicity, the minimum local trunk depth is exactly three.  This is a structural correction,
not just another isolated mixed state: any enumeration forced into `{0,1,2}` would necessarily
misclassify the unique all-free restriction and could undercharge a ten-gadget convolution.

The precise next frontier is to classify all 81 local restrictions by minimum trunk cost in
`{0,1,2,3}` and prove the exact multiplicities.  The classification should reuse the opposite-cross
zero-cost theorem, the same-clause mixed cost-one certificate, and the fully live cost-three
certificate; only the remaining profiles need a cost-two analysis.  Then convolve the corrected
four-level distribution across ten disjoint gadgets and test it against the forty-star padded
shell.  No P-versus-NP conclusion follows.

### The finite local query game has histogram 56, 16, 8, 1

The 81-state audit now has a kernel-checked executable presentation.  A local state wins at budget
zero exactly when both indexed polarities already have canonical depth at most one.  At budget
`k+1`, it additionally wins if some live coordinate has winning false and true children at budget
`k`.  Base-three decoding enumerates every four-coordinate restriction exactly once.

`twoPairLocalQueryWin_sound` proves structurally that every game win produces a genuine
`CommonShallowAt` certificate of the same depth.  The proof recursively assembles the two child
trunks under the selected query and verifies extension and assignment agreement on both branches.
Thus this is not an external simulation of common trunks.

Direct kernel reduction proves the game-cost multiplicities

```text
cost 0: 56
cost 1: 16
cost 2:  8
cost 3:  1
```

The singleton cost-three class agrees with the already proved fully free obstruction and matching
three-query certificate.  The eight cost-two candidates isolate exactly the previously unresolved
part of the local frontier.  Soundness already supplies upper bounds for all 81 states, but calling
the histogram the exact minimum-`CommonShallowAt` distribution still requires the converse: every
arbitrary common trunk of depth `k` must induce a win in the read-once game at budget `k`.

The precise next frontier is to prove that completeness/normalization lemma, using assignment
agreement to eliminate queries of already fixed coordinates and to prevent leaf payloads from
fixing unqueried live coordinates.  Once that bridge is checked, convolve the exact polynomial
`56 + 16 z + 8 z^2 + z^3` across ten gadgets and compare its cost tail, together with padding,
against the forty-star shell.  No P-versus-NP conclusion follows.

### Direct leaf completion fails, but the exact arbitrary-leaf audit has the same histogram

The proposed normalization cannot insert every queried branch value into an arbitrary leaf.
Canonical residual depth is genuinely nonmonotone under such an extension, even in this four-bit
gadget.  `twoPairRootShallow_not_monotone_fixVar` kernel checks the concrete state with base-three
code `11`: both polarities have residual depth at most one at that state, while additionally fixing
coordinate zero to false makes the root-shallow test fail.  The attempted monotonic completion
route is therefore rejected and preserved as a counterexample rather than hidden inside a false
converse proof.

The replacement finite audit models the actual freedom of an arbitrary `CommonShallowAt` leaf.
Given an immutable root and the restriction accumulated by the query path,
`twoPairFlexibleLeafWin` permits any payload among all 81 restrictions that extends the root,
fixes only values compatible with the path, and makes both polarities shallow.  The recursive
`twoPairFlexibleQueryWin` then searches fresh queries while allowing a leaf to omit any earlier
queried values.

Direct kernel reduction proves that this more permissive game still has histogram

```text
cost 0: 56
cost 1: 16
cost 2:  8
cost 3:  1
```

Moreover, `twoPairFlexibleQueryCost_eq_readOnceCost` proves pointwise on all 81 roots that its
first winning budget agrees with the earlier stricter read-once cost.  Thus the nonmonotonicity is
real but does not change this gadget's finite cost distribution through depth three.

The precise next frontier is to prove the structural equivalence between arbitrary
`CommonShallowAt` trunks and `twoPairFlexibleQueryWin`.  Its leaf case must derive that a fixed
payload lies between the immutable root and accumulated path; its query case must skip coordinates
already fixed on the path and consume one unit only for a fresh coordinate.  Once this bridge is
kernel checked, the polynomial `56 + 16 z + 8 z^2 + z^3` is the exact semantic local distribution
and can be convolved across ten gadgets with padding against the forty-star shell.  No
P-versus-NP conclusion follows.

### Arbitrary common trunks are exactly the flexible local query game

The missing semantic bridge is now kernel checked.  The key leaf lemma
`restrictionExtends_path_of_agrees_everywhere` varies one live path coordinate against a proposed
fixed payload value.  It proves that a constant leaf which agrees with every assignment extending
the accumulated path cannot fix an unqueried coordinate.  This avoids the false residual-depth
monotonicity route preserved above.

`twoPairFlexibleQueryWin_of_tree` then normalizes an arbitrary common trunk structurally.  A query
of an already fixed coordinate is resolved without consuming a fresh game move; a live coordinate
becomes one legal Boolean move; and a leaf payload is certified to lie between the immutable root
and accumulated path.  The reverse theorem `twoPairFlexibleQueryWin_sound_aux` recursively
assembles every flexible-game win into a genuine common trunk.  Consequently
`twoPairFlexibleQueryWin_iff_commonShallowAt` proves pointwise, for every four-coordinate root and
every budget `k`,

```text
twoPairFlexibleQueryWin root k root = true
  iff CommonShallowAt(twoPairPolarityFamily, root, k, residualDepth 1).
```

Together with the previously checked exhaustive computation, the polynomial

```text
56 + 16 z + 8 z^2 + z^3
```

is therefore the exact semantic minimum-trunk-cost distribution for one gadget, not merely the
histogram of an executable surrogate.  The nonmonotonicity counterexample remains valid and
preserved; it explains why the flexible leaf relation is necessary even though the final costs
happen to agree with the stricter read-once game.

The precise next frontier is to derive the product/composition theorem for ten disjoint gadgets:
relate a global common trunk of depth ten to the sum of the ten exact local costs (including
adaptive interleaving of gadget queries), then convolve `(56 + 16z + 8z^2 + z^3)^10` and combine
the resulting cost tail with the exact forty-star padding shell.  The convolution alone is not
enough until this direct-sum semantic bridge is proved.  No P-versus-NP conclusion follows.

### The exact local cost supports an additive adversary potential

The first structural ingredient of the ten-gadget direct-sum bridge is now kernel checked.
`twoPairFlexibleQueryCost_fixVar_adversary_code` exhausts all 81 local roots and four possible
fresh coordinates and proves that, after any fresh query, at least one Boolean child retains all
but at most one unit of the exact flexible-game cost.  The presentation-free theorem
`twoPairFlexibleQueryCost_fixVar_adversary` transports this property from the base-three decoder
to every four-coordinate restriction.

Define `twoPairTenFlexibleCost` to be the sum of these exact costs over ten local restrictions.
The theorem `twoPairTenFlexibleCost_update_adversary` proves that updating any one fresh
coordinate in any one gadget has a Boolean branch on which this total potential decreases by at
most one.  The other nine summands are unchanged.  This is precisely the local inequality needed
to neutralize arbitrary adaptive interleaving: a depth-`k` global query path cannot force a loss
of more than `k` units if its branches are chosen by this adversary.

This is not yet the full direct-sum theorem.  The remaining semantic step is to recurse through
an arbitrary ambient `CommonTree`, map every queried padded coordinate either to its unique
`Fin 10 × Fin 4` gadget key or to padding, choose the cost-preserving branch at gadget queries,
and use global leaf agreement to show that every local leaf payload is a legal flexible-game
leaf.  That will prove that global `CommonShallowAt` depth is at least
`twoPairTenFlexibleCost`; only then is it sound to convolve
`(56 + 16z + 8z^2 + z^3)^10` and test its tail against the forty-star padded shell.
No P-versus-NP conclusion follows.

### The arbitrary-leaf direct-sum potential is now one-step stable

The root-only potential from the preceding audit was not yet the correct invariant for an
arbitrary `CommonShallowAt` trunk.  A legal leaf payload may omit values queried on its path, and
the preserved `twoPairRootShallow_not_monotone_fixVar` counterexample shows that replacing such a
payload by the fully accumulated path is unsound.

`twoPairFlexibleConditionalCost root path` now keeps the immutable local root separate from the
accumulated query path and measures the least remaining flexible-game budget.  On the diagonal it
is definitionally the already audited exact local cost, so its initial distribution remains

```text
56 + 16 z + 8 z^2 + z^3.
```

The exhaustive theorem `twoPairFlexibleConditionalCost_fixVar_adversary_code` checks every legal
pair of the 81 roots and 81 paths and every fresh coordinate.  Its presentation-free form proves
that one Boolean child loses at most one unit of conditional cost.  Summing over ten gadgets gives
`twoPairTenFlexibleConditionalCost_update_adversary`; the other nine root/path pairs are unchanged.
Thus the additive adversary survives precisely the arbitrary-leaf freedom that invalidated the
naive accumulated-restriction argument.

This still stops one structural step short of the global depth lower bound.  The precise next
frontier is to recurse the conditional potential through an arbitrary padded ambient
`CommonTree`: ignore padding queries, decode each owned query into its unique `Fin 10 × Fin 4`
coordinate, and at a leaf use global extension/agreement plus the two padded polarity depth bounds
to certify conditional cost zero in every gadget.  That will prove
`twoPairTenFlexibleCost(initial locals) <= trunk.depth`; only then should the exact ten-fold
polynomial be convolved against the forty-star padding shell.  No P-versus-NP conclusion follows.

### The conditional potential now recurses through arbitrary padded common trees

The adaptive-interleaving part of the direct-sum bridge is now kernel checked.
`paddedTwoPairLocalRestriction_fixVar` proves that fixing an owned ambient coordinate is exactly a
point update of the unique `Fin 10 × Fin 4` local state, while
`paddedTwoPairLocalRestriction_fixVar_padding` proves that fixing any of the first `pad`
coordinates changes no local state.

`twoPairTenFlexibleConditionalCost_tree_adversary` recursively follows an arbitrary padded
`CommonTree`.  A query already fixed by the accumulated path is resolved for free; a fresh padding
query is assigned false for free; and a fresh owned query takes the Boolean branch supplied by the
conditional one-step adversary.  It returns an endpoint restriction and a payload such that every
assignment extending the endpoint reaches that payload, and proves

```text
conditionalCost(roots, initial path)
  <= conditionalCost(roots, endpoint) + trunk.depth.
```

Thus padding queries, repeated queries, and arbitrary adaptive interleaving can no longer obstruct
the additive lower bound.  During verification the exhaustive local theorem was also restated
using the executable extension predicate and transported back through
`twoPairRestrictionExtendsB_eq_true`; this preserves the same proposition while avoiding an
unsupported higher-order `Decidable` synthesis route.

The remaining step is now isolated entirely at the returned leaf.  The precise next frontier is
to use the constant-on-endpoint property together with the global leaf extension/agreement and
the two padded polarity depth bounds to prove that every gadget's flexible conditional leaf test
wins, hence that the terminal summed cost is zero.  This requires a padded-to-local canonical-depth
transport lemma.  Composing it with the tree adversary will yield the global semantic depth lower
bound; only afterward should `(56 + 16z + 8z^2 + z^3)^10` be convolved against the forty-star
padding shell.  No P-versus-NP conclusion follows.

### The terminal conditional potential is now discharged locally

The semantic half of the returned-leaf obligation is now kernel checked.  The agreement lemma
`restrictionExtends_path_of_agrees_everywhere` has been generalized from the four-coordinate
gadget to an arbitrary finite ambient cube: if one payload agrees with every assignment extending
an endpoint, it cannot fix a coordinate left live by that endpoint.  The owned-coordinate update
identity is also packaged pointwise as `paddedTwoPairLocalRestriction_fixVar_self`.

`twoPairFlexibleConditionalCost_eq_zero_of_leaf` proves that a payload lying between the immutable
local root and the accumulated local path, and satisfying `twoPairRootShallow`, has conditional
cost exactly zero.  Its direct-sum form
`twoPairTenFlexibleConditionalCost_eq_zero_of_leaf` proves that the entire returned ten-gadget
potential vanishes once these three local facts hold for every gadget.  Thus no further finite-game
or additive-potential argument remains at the endpoint.

A direct padded/local canonical-depth equality was tested and rejected in its naive form.  The
attempt exposed two independent transports that must not be conflated: relabelling the four owned
coordinates, and comparing local fuel `4` with ambient fuel `pad + 40`.  Unfolding the concrete
gates after case splitting destroyed the induction hypothesis's syntactic gate form, so that route
is preserved as a failed proof strategy rather than asserted.

The precise next frontier is now only the canonical-depth bridge: prove fuel monotonicity (or
saturation above the four local variables) and a relabelling theorem that preserves the concrete
positive and negative two-pair gate depths under `paddedTwoPairCoord`.  Then global leaf agreement,
the generalized endpoint lemma, and the new zero-potential capstone compose directly with
`twoPairTenFlexibleConditionalCost_tree_adversary` to yield the semantic global depth lower bound.
Only after that bridge is checked should `(56 + 16z + 8z^2 + z^3)^10` be convolved against the
forty-star padding shell.  No P-versus-NP conclusion follows.

### The padded ten-gadget semantic direct sum is now complete

The coordinate and fuel transports are now kernel checked in the exact form needed by the
two-pair gadget.  `positiveTwoPair_local_depth_le_one_of_padded` and
`negativeTwoPair_local_depth_le_one_of_padded` prove that, for every ambient restriction and every
fuel at least four, an ambient residual-depth-one bound transfers to the four-coordinate pullback
at local fuel four.  The proof audits all 81 local restriction states, uses
`paddedTwoPairCoord_injective` to keep the embedded coordinates distinct, and exposes the four
successor fuel layers explicitly.  This is deliberately the needed one-way shallow transport:
the stronger exact tree-depth equality route leaves symbolic post-saturation fuel branches and is
not asserted.  Thus relabeling and sufficient fuel exposure are discharged together rather than
inferred from an unproved general monotonicity principle.

`twoPairRootShallow_of_padded_depths` packages the two polarity transports into the executable
local shallow predicate.  The capstone
`twoPairTenFlexibleCost_le_of_padded_commonShallow` then composes the arbitrary-tree conditional
adversary with global leaf agreement, the generalized endpoint lemma, padded-to-local restriction
extension, the new depth transport, and terminal zero potential.  It proves

```text
twoPairTenFlexibleCost(local pullbacks of sigma) <= trunkDepth
```

for every `CommonShallowAt (paddedTwoPairFamily pad) fuel sigma trunkDepth 1` with `fuel >= 4`.
This includes arbitrary adaptive interleaving, repeated queries, and padding queries; the full
semantic direct-sum lower bound no longer has an outstanding structural step.

The earlier naive unfolding route remains recorded as a failed strategy: it conflated relabeling
with fuel transport and destroyed the induction hypothesis's gate syntax.  The successful finite
specialization avoids that failure without asserting a general theorem that has not been proved.

The precise next frontier is quantitative.  Convolve the already verified exact local cost
polynomial `(56 + 16z + 8z^2 + z^3)^10`, identify the coefficient tail with the padded restrictions
whose summed local cost exceeds trunk depth ten, and combine that tail with the exact forty-star
padding shell.  This will test whether the semantic obstruction has enough mass to refute the
claimed half-shell contraction at the concrete schedule.  No P-versus-NP conclusion follows.

### The complete semantic cost tail is quantitatively insufficient

The joint live-coordinate/cost audit is now kernel checked, rather than inferred from the
univariate cost histogram.  Its bivariate generating polynomial is exactly

```text
16 + 32*x + (8 + 16*z)*x^2 + 8*z^2*x^3 + z^3*x^4.
```

Thus every local semantic cost is at most the number of live owned coordinates.  The new finite
set `paddedTwoPairFlexibleCostTail pad` contains exactly the ambient restrictions with forty stars
whose sum of the ten local semantic costs exceeds ten.  The completed direct-sum theorem proves
that this entire set, not merely a selected profile class, is contained in
`commonShallowBad (paddedTwoPairFamily pad) (pad + 40) 40 10 1`.

The joint grading also gives a decisive shortcut around an expensive exact ten-fold convolution.
Every tail point owns at least eleven live gadget coordinates, so it has at most twenty-nine live
padding coordinates.  Injecting the full tail into all `81^10` local states paired with a padding
restriction of at most twenty-nine stars yields

```text
|cost tail at pad 4080| * 2^10
  < choose(4120,40) * 2^4080.
```

This deliberately overcounts every possible local vector.  Therefore the exact bivariate
convolution, which can only shrink the left side, cannot make this ten-gadget witness refute the
requested shell contraction at the audited schedule.  The route is preserved as a genuine
semantic bad subset with inadequate mass, not discarded as a merely numerical experiment.

The precise next frontier is structural rather than a finer convolution: search for a gadget
family whose semantic common-trunk cost grows faster relative to its owned live-coordinate
support, or change the schedule so that padding does not dilute every cost unit.  A useful next
local target is a proved ratio obstruction or construction with `cost > stars` under the relevant
residual-depth notion; the present gadget satisfies the opposite inequality pointwise.  No
P-versus-NP conclusion follows.

### A universal live-support ceiling closes the super-unit gadget-ratio route

The proposed local discriminator is now settled in the negative, uniformly over every finite gate
family and every residual-depth threshold.  The new theorem
`trunkDepth_lt_stars_of_not_commonShallowAt` states that, whenever the root's live-variable count
fits within the canonical-tree fuel budget,

```text
¬ CommonShallowAt gates fuel sigma trunkDepth residualDepth
  → trunkDepth < stars sigma.
```

This is the contrapositive form needed by semantic gadget lower bounds.  The proof uses the
already verified canonical prefix that queries all live root coordinates: once the trunk budget
reaches `stars sigma`, every reached restriction is terminal for every indexed gate, so all
residual canonical depths are zero.  Monotonicity then covers any requested residual threshold.

Consequently no sound gadget potential that certifies failure of `CommonShallowAt` can have
semantic common-trunk cost strictly larger than its live-coordinate support.  The ten-gadget
identity `twoPairFlexibleQueryCost ≤ stars` was not an accidental weakness of that construction;
ratio greater than one is impossible for the current event definition under ample fuel.

The precise next frontier is therefore quantitative and distributional: redesign the survivor
schedule or the shell encoding so that a near-unit semantic cost/live-support ratio is not diluted
by padding, or prove a stronger bad-set count using correlations across gadgets.  Searching for a
single gadget with `cost > stars` is now a closed route.  No P-versus-NP conclusion follows.

### Zero padding isolates dilution as the decisive failure mode

The same exact ten-gadget semantic witness has now been checked at the opposite endpoint of the
padding schedule.  `twoPairFlexibleQueryCost_allFree` computes that every fully live local gadget
has cost three.  Consequently, with `pad = 0`, the unique restriction on forty coordinates with
forty stars has total semantic cost thirty and lies in
`paddedTwoPairFlexibleCostTail 0`.  The theorem
`paddedTwoPairFlexibleCostTail_card_zeroPadding` proves that this tail is the entire one-point
forty-live shell.

Combining that exact tail cardinality with the already proved semantic direct-sum inclusion gives
`not_paddedTwoPair_scaled_contraction_zeroPadding`:

```text
¬ |commonShallowBad (paddedTwoPairFamily 0) 40 40 10 1| * 2^10
    ≤ |{sigma : Restriction 40 | stars sigma = 40}|.
```

Thus the gadget is strong enough to refute the requested contraction when all shell mass is
concentrated on its owned coordinates, while its complete semantic tail is insufficient at
`pad = 4080`.  This formally separates padding dilution from the semantic direct-sum strength;
removing padding fixes the witness but does not by itself supply the ambient-variable regime
needed by the layered circuit schedule.

The precise next frontier is to locate the padding transition rather than search for a forbidden
super-unit gadget: derive the exact bivariate tail-cardinality formula as a function of `pad`, then
find the largest padding compatible with the `2^-10` contraction failure and compare it to the
minimum ambient slack required by the realized-prefix encoder.  If those ranges do not overlap,
the shell encoding or survivor schedule must change.  No P-versus-NP conclusion follows.

### The bivariate arithmetic isolates the candidate padding boundary at 86/87

The local joint profile has now been promoted to the explicit recurrence
`twoPairCostLiveConvolution`: its coefficient at `(q,c)` is the coefficient of `x^q z^c` in

```text
(16 + 32*x + 8*x^2 + 16*x^2*z + 8*x^3*z^2 + x^4*z^3)^g.
```

Summing the ten-fold cost columns `c > 10` gives a resource-safe table indexed by owned live
support `q`.  `paddedTwoPairFlexibleCostTabulatedMass pad` combines that table with the exact
padding layer `choose(pad,40-q) * 2^(pad-(40-q))`.  The two boundary comparisons are kernel
checked:

```text
not (tabulatedMass 86 * 2^10 <= choose(126,40) * 2^86)
tabulatedMass 87 * 2^10 <= choose(127,40) * 2^87.
```

Thus the exact bivariate arithmetic candidate changes side between these two adjacent test points:
padding 86 still supplies enough semantic tail mass to defeat the requested saving, whereas
padding 87 does not.  Monotonicity away from these points is not yet asserted.  Both values are far
below the audited schedule padding 4080 and sharply confirm the dilution diagnosis.

The coefficient table is intentionally not yet asserted to equal the cardinality of
`paddedTwoPairFlexibleCostTail`: direct reduction of the naive recurrence exceeded the module's
resource budget, and the current dirty two-pair audit already contains unrelated unfinished
compile errors.  The precise next frontier is a structural finite-product proof that the tabulated
coefficients are the ten-fold local fibers and that the product restriction equivalence turns
their weighted sum into the actual tail cardinality.  That bridge will upgrade the 86/87 arithmetic
boundary to a theorem about `commonShallowBad`; until then it is a kernel-checked arithmetic
discriminator, not a claimed semantic threshold.  No P-versus-NP conclusion follows.

### The bivariate recurrence now has its exact semantic base fiber

The first structural layer of the cardinality bridge is now explicit.  The finite set
`twoPairLocalCostLiveFiber q c` consists of the actual four-coordinate restrictions with live
support `q` and flexible common-trunk cost `c`.
`twoPairLocalCostLiveFiber_card_eq_convolution_one` identifies its cardinality with
`twoPairCostLiveConvolution 1 q c` for every pair of natural indices.  The proof checks the twenty
feasible `(q,c)` cells against the executable local semantics and proves all cells outside the
`q <= 4`, `c <= 3` rectangle empty from the live-support and cost bounds.  Thus the polynomial's
one-gadget coefficients are no longer merely a displayed or manually transferred table.

The exact ambient product decomposition was also repaired at its previously unfinished point.
`paddedTwoPairRestrictionCode_surjective` now reconstructs each gadget coordinate by an explicit
use of the inverse law for `finProdFinEquiv`, and `paddedTwoPairRestrictionEquiv` is correctly
marked noncomputable because `Equiv.ofBijective` uses classical choice.  This supplies the actual
bijection needed by the final weighted-cardinality transport.

The precise next frontier is to iterate the new one-gadget fiber theorem: partition
`Fin (g+1) -> Restriction 4` by the last gadget's six possible `(stars,cost)` cells and prove that
the resulting cardinalities satisfy `twoPairCostLiveConvolution`.  Specializing at `g = 10`,
summing the columns `c > 10`, and transporting through `paddedTwoPairRestrictionEquiv` should then
identify `paddedTwoPairFlexibleCostTabulatedMass pad` with the actual semantic tail cardinality.
Only after that equality is proved can the arithmetic 86/87 comparison be promoted to semantic
bad-set statements.  No P-versus-NP conclusion follows.

### The exact semantic product fiber now satisfies the full convolution

The one-gadget audit has now been lifted structurally to every finite product.  The generic lemma
`twoPairLocalCostLive_weighted_sum` proves that any weight depending only on a local restriction's
`(stars,cost)` profile sums with the six verified multiplicities

```text
(0,0):16, (1,0):32, (2,0):8, (2,1):16, (3,2):8, (4,3):1.
```

Together with the already present last-coordinate decomposition
`twoPairProductCostLiveFiber_card_succ`, this yields the induction capstone
`twoPairProductCostLiveFiber_card_eq_convolution`:

```text
|twoPairProductCostLiveFiber g q c| = twoPairCostLiveConvolution g q c
```

for all natural `g,q,c`.  The proof never evaluates the `81^g` product space: it partitions one
local factor into its twenty bounded profile cells, eliminates the fourteen empty cells using the
proved base fiber theorem, and applies the induction hypothesis to the remaining product fiber.
Thus the displayed bivariate polynomial is now the exact semantic enumerator at every gadget
count, not merely at one gadget or as an arithmetic recurrence.

The precise next frontier is the final weighted-cardinality transport.  Specialize the new theorem
to `g = 10`, prove that summing all fibers with `q <= 40` and `c > 10` gives
`twoPairTenFlexibleCostTailCoefficient q`, and combine this with `card_stars_eq` on the padding
factor through `paddedTwoPairRestrictionEquiv`.  This should identify
`paddedTwoPairFlexibleCostTabulatedMass pad` with the actual semantic tail cardinality and promote
the padding-86 arithmetic failure to a genuine `commonShallowBad` lower bound.  The padding-87
comparison will remain only an upper bound on this particular semantic witness, not a monotonicity
or exact bad-set threshold claim.  No P-versus-NP conclusion follows.

### The bivariate table is now the exact ambient semantic tail

The final weighted-cardinality transport is complete.  On the attainable range `q <= 40`,
`twoPairTenFlexibleCostTailCoefficient_eq_sum` verifies that the explicit coefficient table is
the sum of recurrence columns `11 <= c <= 30`.  Fiberwise decomposition plus
`twoPairProductCostLiveFiber_card_eq_convolution` then proves

```text
|twoPairProductFlexibleCostTailFiber q|
  = twoPairTenFlexibleCostTailCoefficient q.
```

The ambient transport is also exact.  `paddedTwoPairFlexibleCostTail_card_eq_codeTail` maps the
semantic tail through `paddedTwoPairRestrictionCode`, preserving both the split star count and the
ten-gadget flexible cost.  `paddedTwoPairFlexibleCostCodeTail_card` partitions the product-side
image by local live support and counts the complementary padding fiber with `card_stars_eq`.
Consequently `paddedTwoPairFlexibleCostTail_card` establishes, for every `pad`,

```text
|paddedTwoPairFlexibleCostTail pad|
  = paddedTwoPairFlexibleCostTabulatedMass pad.
```

This promotes the lower side of the arithmetic boundary to semantics:
`not_paddedTwoPair_scaled_contraction_86` proves that the actual
`commonShallowBad (paddedTwoPairFamily 86) 126 40 10 1` violates the requested `2^-10`
contraction.  The proof uses the already established inclusion of every exact-tail point in the
bad set.  At padding 87, the arithmetic theorem says only that this particular semantic tail fits
under the target mass; it gives no upper bound on the entire bad set and no threshold or
monotonicity theorem.

The precise next frontier is therefore no longer coefficient semantics.  It is to determine
whether bad restrictions outside this flexible-cost witness can remain quantitatively large at
padding 87 and, more importantly, along the actual multi-round schedule (whose audited padding is
4080).  The highest-information route is an exact completeness audit for
`twoPairFlexibleQueryCost`: either prove that cost `<= 10` characterizes existence of a depth-ten
common trunk for this disjoint family, turning the tail into the full bad set, or isolate and count
a concrete family of false negatives.  Existing coarse results already prove this tail alone is
insufficient at padding 4080, so merely refining its count further cannot close the scheduled
iteration.  No P-versus-NP conclusion follows.

### Local semantic shallowness now lifts exactly to the padded gadget

The completeness audit exposed a concrete missing direction before the ten-gadget trunks can be
composed.  The direct-sum adversary already pulled ambient shallow leaves back to the canonical
four-coordinate game, but the converse construction needs a locally shallow leaf payload to imply
that the corresponding ambient padded gate is shallow.  That converse is now kernel checked.

`positiveTwoPair_padded_depth_le_one_of_local` and
`negativeTwoPair_padded_depth_le_one_of_local` prove that, for every padding, gadget, ambient
restriction, and fuel at least four, a canonical local depth bound of one lifts to the matching
padded polarity.  The proof exhausts only the three states of the four owned coordinates; it does
not enumerate padding assignments.  Together with the previous pullback lemmas,
`twoPairRootShallow_iff_padded_depths` gives the exact equivalence

```text
twoPairRootShallow(local pullback) = true
  iff
both corresponding padded polarities have canonical depth at most one.
```

This removes a semantic gap in the proposed product-tree converse: after lifting a local
flexible-game leaf into the ambient restriction, its local terminal certificate is now sufficient
for the required ambient residual-depth bound.  It does not by itself prove that total flexible
cost at most ten supplies one ambient common trunk, because the remaining local trunks still have
to be relabelled onto their disjoint owned supports, their leaf payloads merged, and their depths
added under `CommonTree.bind`.

The precise next frontier is to implement that disjoint product-tree composition.  Prove a generic
depth bound for sequential `CommonTree.bind`, lift each local query coordinate through
`paddedTwoPairCoord`, merge its returned four-coordinate payload into the ambient restriction, and
iterate over `Fin 10`.  Combined with the existing adversary inequality, this would establish
that the semantic cost tail is exactly the full bad set at every padding, resolving padding 87 and
4080 by the already proved exact count.  No P-versus-NP conclusion follows.

### The product-tree calculus now has its depth and coordinate-lifting core

The first structural part of the constructive converse is now kernel checked in
`ComputationalDepthMultiSwitchingCommonTree.lean`.  `CommonTree.reindex` relabels every local query
through an arbitrary coordinate map while transforming its leaf payload;
`depth_reindex` proves that this costs exactly the original local depth, and `run_reindex` proves
that ambient execution is precisely execution on the pulled-back assignment.  Separately,
`depth_bind_le` proves the additive estimate

```text
depth (bind t f) <= depth t + d
```

whenever every replacement tree `f a` has depth at most `d`.  Consequently the intended
sequential construction can lift each local gadget tree through `paddedTwoPairCoord` and pay the
sum of the ten local budgets; no unproved depth algebra remains in that composition.

This does not yet prove the converse.  The precise next frontier is the payload layer: define the
ambient restriction obtained by overwriting one gadget's four owned coordinates with the local
leaf restriction, prove its pullback is exactly that leaf and every other gadget's pullback is
unchanged, and show it preserves both root extension and agreement with the ambient assignment.
Those laws will allow `reindex` trees to be chained with `bind`; induction over the ten gadgets can
then turn total flexible cost at most ten into `CommonShallowAt`.  Together with the existing
adversary direction this would identify the full bad set with the exact semantic cost tail.  No
P-versus-NP conclusion follows.

### The one-gadget ambient payload overwrite is now formalized

The payload layer needed by the constructive product-tree converse is now explicit in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  `paddedTwoPairOverwrite` replaces exactly
the four ambient coordinates owned by one gadget with a returned local restriction.  Its four
interface laws prove that:

* pulling the result back to the overwritten gadget returns the local payload exactly;
* pulling it back to any other gadget returns the previous ambient payload unchanged;
* if the previous ambient payload extends the immutable root and the local payload extends the
  root's local pullback, then the overwritten payload still extends the root; and
* if the previous ambient payload and local replacement agree with an ambient assignment, then
  the overwritten payload agrees with that assignment.

This closes the coordinate/payload bookkeeping identified in the preceding reassessment.  In
particular, sequential gadget updates can no longer corrupt certificates already installed on
disjoint gadgets, and the two semantic leaf obligations of `CommonShallowAt` are stable under one
update.

The precise next frontier is the actual ten-gadget fold: obtain each local tree from
`twoPairFlexibleQueryWin_iff_commonShallowAt`, lift it with `CommonTree.reindex` using
`paddedTwoPairCoord`, map its local leaves through `paddedTwoPairOverwrite`, and compose the ten
lifted trees with `CommonTree.bind`.  The induction must carry the local-pullback invariants for
processed and unprocessed gadgets and use `depth_bind_le` to bound total depth by the sum of local
costs.  Completing that fold would turn total flexible cost at most ten into the ambient
`CommonShallowAt` converse.  No P-versus-NP conclusion follows.

### The one-gadget lifted trunk now discharges the complete fold step

The local-to-ambient construction is now packaged as an actual tree rather than a collection of
coordinate identities.  `paddedTwoPairLiftTree` recursively relabels a four-coordinate local
common trunk onto one padded gadget and overwrites every returned local payload into the current
ambient restriction.  Its exact depth and run laws show that relabelling neither changes depth nor
alters the intended execution/overwrite semantics.

More importantly, `paddedTwoPairLiftTree_spec` proves the full induction interface from a local
`CommonShallowAt` witness.  Provided the current ambient payload extends the immutable root, every
reached lifted leaf:

* still extends the immutable ambient root;
* agrees with the followed ambient assignment;
* makes the processed gadget satisfy `twoPairRootShallow`; and
* leaves every other gadget pullback exactly unchanged.

Thus the remaining product construction no longer needs to reopen local semantic soundness or
coordinate bookkeeping.  It only needs a finite fold invariant saying that all already processed
gadgets retain their shallow certificates while unprocessed pullbacks still equal their roots,
together with the additive `CommonTree.depth_bind_le` estimate.

The precise next frontier is to define the `List.finRange 10` bind fold over these lifted trunks,
prove by list induction that its depth is at most the sum of the ten local flexible costs, and
instantiate `twoPairRootShallow_iff_padded_depths` at the final leaf.  That will decide whether
total flexible cost at most ten gives the ambient `CommonShallowAt` converse and hence whether the
exact semantic tail is the full bad set at padding 87 and 4080.  No P-versus-NP conclusion follows.

### The sequential product-tree fold and its additive depth law are now explicit

`paddedTwoPairLiftFold` now performs the promised product construction for an arbitrary explicit
list of gadget indices.  At each step it lifts that gadget's local tree at the current ambient
payload and uses `CommonTree.bind` to continue from every returned leaf.  This is the executable
tree skeleton that will be specialized to `List.finRange 10`.

Two structural laws are proved independently of the semantic invariant.  First,
`paddedTwoPairLiftFold_depth_le` bounds the ambient fold depth by the sum of the listed local tree
depths, using `CommonTree.depth_bind_le` at every step.  Second,
`paddedTwoPairLiftFold_run_cons` gives the exact head-then-tail execution recurrence.  Therefore
neither fold construction nor trunk-budget addition remains implicit.

The precise next frontier is the semantic list induction: for a duplicate-free order, show that
the fold preserves `RestrictionExtends` and assignment agreement, retains
`twoPairRootShallow` for every processed gadget via the other-coordinate overwrite law, and leaves
each unprocessed pullback equal to its initial root.  Specializing that invariant to
`List.finRange 10` and choosing each local witness at `twoPairFlexibleQueryCost` should produce the
ambient `CommonShallowAt` converse whenever the ten costs sum to at most ten.  No P-versus-NP
conclusion follows.

### The sequential fold now carries its complete semantic list invariant

The product-tree payload induction is now explicit in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  The theorem
`paddedTwoPairLiftFold_localRestriction_of_not_mem` proves that every gadget omitted from the
remaining order has exactly the same local pullback before and after the fold.  This is the
preservation law needed to keep an earlier shallow certificate valid while later disjoint gadgets
are processed.

`paddedTwoPairLiftFold_spec` then proves the full semantic invariant for every duplicate-free
order.  Assuming each listed local tree is a valid common-shallow witness at its immutable root
pullback, every reached final payload:

* extends the immutable ambient root;
* agrees with the followed ambient assignment; and
* satisfies `twoPairRootShallow` for every gadget in the processed order.

Thus the processed/unprocessed bookkeeping, root extension, assignment agreement, and persistence
of earlier shallow certificates are no longer implicit.  Together with the already proved
additive depth bound, the only remaining constructive interface is selecting a concrete local
tree at `twoPairFlexibleQueryCost` for every root, specializing the order to `List.finRange 10`,
and translating the ten Boolean local shallow facts through
`twoPairRootShallow_iff_padded_depths` into the `Fin 20` ambient family certificate.

The precise next frontier is that specialization capstone.  First prove that
`twoPairFlexibleQueryWin rho (twoPairFlexibleQueryCost rho) rho = true` (including the universal
depth-three fallback), choose the corresponding ten local `CommonShallowAt` witnesses, and combine
the fold depth and semantic theorems into
`CommonShallowAt (paddedTwoPairFamily pad) fuel sigma (twoPairTenFlexibleCost ...) 1` for
`4 <= fuel`.  This would establish the missing converse to
`twoPairTenFlexibleCost_le_of_padded_commonShallow` and identify the exact bad set with the cost
tail.  No P-versus-NP conclusion follows.

### The computed local flexible cost is now certified to win

The last branch of `twoPairFlexibleQueryCost` is no longer only an inferred histogram value.
`twoPairFlexibleQueryWin_three_code` exhausts the 81 base-three local restrictions and proves that
the flexible game wins at depth three for every one.  The decoder identity then removes the code
presentation.  Consequently `twoPairFlexibleQueryWin_cost` proves pointwise for every local root
`rho` that

```text
twoPairFlexibleQueryWin rho (twoPairFlexibleQueryCost rho) rho = true.
```

Thus all four branches of the computed minimum supply actual flexible-game certificates, and
`twoPairFlexibleQueryWin_iff_commonShallowAt` can now select a local common tree at exactly that
cost.  This closes the universal fallback issue; it does not yet assemble the ten selected trees
or prove the ambient converse.

The precise next frontier is to choose, for each `g : Fin 10`, the local `CommonTree` supplied by
`twoPairFlexibleQueryWin_iff_commonShallowAt` at the pullback
`paddedTwoPairLocalRestriction pad sigma g`.  Specialize `paddedTwoPairLiftFold_depth_le` and
`paddedTwoPairLiftFold_spec` to `List.finRange 10`, rewrite the depth sum as
`twoPairTenFlexibleCost`, and translate each final `twoPairRootShallow` fact through
`twoPairRootShallow_iff_padded_depths` and the `Fin 20` product index.  The intended capstone is
`CommonShallowAt (paddedTwoPairFamily pad) fuel sigma
  (twoPairTenFlexibleCost (fun g => paddedTwoPairLocalRestriction pad sigma g)) 1`
for `4 <= fuel`.  No P-versus-NP conclusion follows.

### The exact semantic cost characterization is now closed

`paddedTwoPairFamily_commonShallow_flexibleCost` performs the pending ten-gadget specialization.
For every padding, every ambient root restriction, and every fuel budget at least four, it chooses
the local `CommonTree` certified at `twoPairFlexibleQueryCost` for each gadget, binds their lifted
trees in `List.finRange 10` order, identifies the additive list depth with the `Fin 10` sum, and
translates the ten terminal `twoPairRootShallow` facts into all twenty ambient polarity bounds.
It proves the constructive certificate

```text
CommonShallowAt (paddedTwoPairFamily pad) fuel sigma
  (twoPairTenFlexibleCost
    (fun g => paddedTwoPairLocalRestriction pad sigma g)) 1.
```

Combining this upper bound with the previously proved interleaved-query adversary gives
`paddedTwoPairFamily_commonShallow_iff_flexibleCost_le`:

```text
CommonShallowAt (paddedTwoPairFamily pad) fuel sigma trunkDepth 1
  iff
twoPairTenFlexibleCost
  (fun g => paddedTwoPairLocalRestriction pad sigma g) <= trunkDepth.
```

Thus, for fuel at least four, the flexible-cost tail is not merely a semantic subset of the bad
set: it is exactly the full bad set for this padded disjoint family.  Padding queries, arbitrary
ambient interleaving, and local leaf forgetting introduce no false positives or false negatives.
In particular, the existing exact count resolves the earlier completeness uncertainty at padding
87.  `paddedTwoPairFlexibleCostTail_eq_bad` records the set equality, and the existing padding-4080
tail estimate now upgrades to `paddedTwoPair_scaled_contraction_4080`: the *entire* bad set for this
test family satisfies the requested depth-ten contraction on the audited 4120-variable,
forty-star shell.  This is the opposite behavior from padding 86, where the already proved theorem
shows failure of the same scaled contraction.

The precise next frontier is to transport this now-complete calibration back to the actual layered
round.  Duplicate normalization and the ragged alphabet recurrence are already formalized earlier
in this file, reducing the next-family key cap from `2*M^2*2^(s+1)` to
`2*M*2^(s+1)`.  The remaining decision is whether the normalized circuit family admits a comparable
direct-sum or bounded-overlap live-variable charge strong enough to meet the exact slot margin
across successive survivor shells.  No P-versus-NP conclusion follows.

### The exact semantic padding transition is now pinned down at 86/87

The constructive cost characterization also resolves the earlier one-coordinate boundary, not
only the far-padding schedule.  `paddedTwoPair_scaled_contraction_87` rewrites the *entire*
`commonShallowBad` set to the exact flexible-cost tail and applies the already verified bivariate
mass comparison.  Consequently the same disjoint ten-gadget family fails the requested
`2^-10` contraction at padding 86 but satisfies it at padding 87.  There is no remaining
subset-versus-full-bad-set ambiguity at either side of this tested transition.

The precise next frontier is structural rather than another padding computation: specialize the
already normalized ragged layered family to an explicit bottom-gate decomposition and determine
whether its common-trunk cost admits an additive or bounded-overlap charge to live variables.
Such a theorem would have to compose with the circuit-owned `bottomSlotCount` recurrence and meet
the verified margin
`8*(s+2)*bottomSlotCount(C)*2^(s+1) + 4*(s+2) <= N`; the two-pair threshold alone does not imply
that bound.  A counterexample to any proposed charge should be retained explicitly.  No
P-versus-NP conclusion follows.

### A universal slot-owned live-support charge is now explicit, but is not the shell theorem

The normalized ragged circuit family now has a deterministic circuit-owned trunk cap.
`normalizedLayeredBottomFamily_liveSupport_card_le_slotCharge` proves, at every root `sigma`,

```text
|(familyVariableSupport (normalizedLayeredBottomFamily C)) live at sigma|
  <= 2*w*bottomSlotCount(C).
```

The proof is fully additive: filtering to live coordinates cannot enlarge support, width charges
at most `w` variables per normalized clause occurrence, normalization contributes at most the two
polarity copies, and `bottomSlotCount` owns every original occurrence (including the empty-gate
edge case).  With ample fuel,
`normalizedLayeredBottomFamily_commonShallowAt_slotCharge` turns this into

```text
CommonShallowAt (normalizedLayeredBottomFamily C) fuel sigma
  (2*w*bottomSlotCount C) 0.
```

Thus an unconditional bounded-overlap live-variable charge does exist.  It does not by itself
close the intended half-shell survivor recurrence: it is a worst-case deterministic cap, pays for
both syntactic polarities, and leaves no probabilistic statement showing that the live charge is
at most the scheduled trunk budget on all but a `2^-d` fraction of a `K`-star shell.

The precise next frontier is to remove the artificial polarity factor at the support level by
proving that a clause and its `negDNF` image have identical variable support, then test the sharp
`w*bottomSlotCount(C)` live-support charge against the actual `K=20R`, `d=10R` survivor shell.
If even that sharp deterministic charge exceeds `d`, the next necessary theorem is a shell-tail
bound for the root-local live support (or a counterexample saturating it), not another global
padding calibration.  No P-versus-NP conclusion follows.

### Polarity is free at support level; the deterministic half-shell route still fails

The artificial factor two has now been removed.  `clauseVariableSupport_negClause` and
`gateVariableSupport_negDNF` prove that literal negation and `negDNF` preserve variable support
exactly.  `normalizedLayeredBottomFamily_support_subset_bottomSupport` then folds both normalized
polarities back into the unpolarized support of the circuit's original `bottomGates`.  Direct list
accounting gives

```text
|layeredBottomVariableSupport(C)| <= w*bottomClauseCount(C),
```

and hence `normalizedLayeredBottomFamily_liveSupport_card_le_sharpSlotCharge` proves at every root
`sigma`

```text
|(familyVariableSupport (normalizedLayeredBottomFamily C)) live at sigma|
  <= w*bottomSlotCount(C).
```

With ample fuel, `normalizedLayeredBottomFamily_commonShallowAt_sharpSlotCharge` constructs a
common trunk of that depth and residual depth zero.  Thus the old `2*w*bottomSlotCount(C)` cap was
indeed only a syntactic polarity loss.

The sharp deterministic cap still does not fit the universal half-shell budget.  At the first
tested schedule scale `R=1`, the existing padded singleton round output has width one, twenty
bottom slots, and exact live family support twenty on the fully live `K=20` root, while the trunk
budget is `d=10`.  The retained theorems
`paddedSingletonSupport_not_commonShallow_of_live_false` and
`paddedSingletonSupport_not_commonShallow_of_live_true` show that more than ten live support
coordinates with either monochromatic fixed profile are genuinely bad at residual depth zero;
this is not merely looseness in the new upper bound.  Mixed fixed polarities can instead make the
same family shallow at the root, so support cardinality alone also cannot characterize the bad
event.

The precise next frontier is therefore probabilistic and polarity-sensitive: bound, on the
`K=20R` shell, the mass of roots whose live support and fixed-value profile force common-trunk cost
above `10R` for the normalized circuit family.  A support-cardinality tail by itself is sufficient
but may be unnecessarily coarse; the singleton counterexample shows that any universal
deterministic `live support <= 10R` claim is false.  No P-versus-NP conclusion follows.

### Every bad normalized root is now reduced to the circuit-owned live-support tail

The necessary support-tail envelope is now formal rather than heuristic.
`commonShallowBad_subset_liveFamilySupportTail` proves, for ample fuel and every requested residual
depth, that

```text
commonShallowBad gates fuel K d residualDepth
  ⊆ {sigma | stars sigma = K and d < |live family support at sigma|}.
```

Indeed, if the live family support has size at most `d`, querying it gives a common trunk of depth
at most `d` and residual depth zero, which supplies any nonnegative requested residual bound.  The
circuit specialization `normalizedLayered_commonShallowBad_subset_liveBottomSupportTail`
strengthens the containing event to the live part of `layeredBottomVariableSupport C`, the original
unpolarized bottom-gate support.  Thus the reduction pays neither the duplicate-normalization
factor nor the two-polarity factor.

This theorem is only a necessary envelope.  The retained padded-singleton classification still
shows that roots with the same live-support cardinality may be shallow or bad depending on their
fixed-value profile.  Consequently a hypergeometric count of the support tail is a valid sufficient
route to contraction, but failure of that coarse count would not refute a sharper semantic bound.

The precise next frontier is to count `liveLayeredBottomSupportTail C (20*R) (10*R)` in terms of
`|(layeredBottomVariableSupport C)|` and the ambient dimension, test that hypergeometric upper bound
against the exact survivor-shell schedule, and retain the fixed-profile refinement as the fallback
if the support-only tail is too large.  No P-versus-NP conclusion follows.

### The circuit-owned support tail now has an exact hypergeometric formula

The support-only envelope has been counted exactly, without adding disjointness assumptions on
the bottom gates.  For an arbitrary fixed support `S`, `liveSupportOverlap_card` proves that the
class of `K`-star roots with exactly `q` live coordinates in `S` has cardinality

```text
choose |S| q * choose (n-|S|) (K-q) * 2^(n-K).
```

The proof first counts free-variable sets by treating `S` as a single occupancy block, then uses
the constant `2^(n-K)` fiber of Boolean assignments to the fixed coordinates.  The classes are
pairwise disjoint in `q`.  Consequently `liveLayeredBottomSupportTail_card` gives the exact
circuit-owned tail mass

```text
sum q=trunkDepth+1..K,
  choose |layeredBottomVariableSupport(C)| q
  * choose (n-|layeredBottomVariableSupport(C)|) (K-q)
  * 2^(n-K).
```

Together with `normalizedLayered_commonShallowBad_subset_liveBottomSupportTail`, this is now an
explicit numerical upper bound on the normalized-family bad set.  It is exact for the support
event, but remains only an envelope for semantic badness; the retained singleton examples still
show that fixed polarities can make equal-support roots behave differently.

The precise next frontier is quantitative: cancel the common `2^(n-20R)` factor against the
`20R`-star shell and prove (or refute at the recurrence boundary) that the resulting upper
hypergeometric tail, with
`|layeredBottomVariableSupport(C)| <= w*bottomSlotCount(C)`, is at most
`2^(-10R) * choose n (20R)` under the actual survivor-shell margin.  If that inequality fails at
an admissible parameter point, retain the point as a counterexample and move to the already
identified fixed-polarity refinement.  No P-versus-NP conclusion follows.
