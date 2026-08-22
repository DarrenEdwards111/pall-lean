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
