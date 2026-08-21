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
