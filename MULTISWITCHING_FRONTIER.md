# Multi-switching frontier (2026-08-21)

## Randomized/balanced selector audit (2026-08-27)

The proposed randomized-coordinate-order repair is now formally closed for the present parity
calibration.  The obstruction occurs before an order is chosen: for residual depth zero, the
fixed-live-set survivor atlas is wholly contained in the bad event.  Hence every seed sees the
same all-bad conditioned atlas.

The new capstones prove:

- `parity_fixedFreeSet_every_seed_all_bad`: for an arbitrary seed type, each seed's conditioned
  bad slice is exactly the full fixed-live-set atlas;
- `parity_fixedFreeSet_randomSeed_bad_pairs_eq_product`: for every finite seed set, the bad
  seed/root pairs are the whole Cartesian product;
- `parity_fixedFreeSet_randomSeed_bad_pairs_card`: the exact count is
  `|seeds| * 2^(n-K)`, so conditioned bad probability is one.

This covers arbitrary seed-dependent orders and prefixes because root badness precedes the seeded
selection.  Uniform randomness cannot help, rational nonuniform distributions reduce to repeated
seeds, and averaging cannot fix a good seed because no good seed exists.  There is therefore no
balancing cost to fit into the recurrence: the required saving is zero on this witness.

Together with the exact coherent-fiber lower bound already proved, this blocks both possible uses
of randomization in the current construction: hiding the conditioning gap by averaging, or using
a balanced order to shrink the first-round decoder alphabet.  Any viable continuation must alter
the bad event or the restriction distribution itself (rather than only the selector order), and
must still prove a switching lemma compatible with the layered recurrence.  This remains a
restricted-circuit obstruction, not a proof of `P ≠ NP`.

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

### The shell factor is cancelled and the recurrence margin gives 1/16 support density

The exact support count is now wired back into the normalized circuit bad-set theorem.
`normalizedLayered_commonShallowBad_scaled_le_of_hypergeometric_tail` proves that the sole
remaining numerical premise is

```text
(sum q=trunkDepth+1..K,
   choose |S| q * choose (n-|S|) (K-q)) * 2^savingExponent
  <= choose n K,
```

where `S = layeredBottomVariableSupport(C)`.  The common Boolean fiber `2^(n-K)` is cancelled
before the premise is exposed; no division in `Nat` and no fixed-value overcount remain.

The circuit-owned density regime is also now explicit.  Under bottom width `s+1`, the already
audited recurrence margin

```text
8*(s+2)*bottomSlotCount(C)*2^(s+1) + 4*(s+2) <= n
```

implies

```text
16 * |layeredBottomVariableSupport(C)| <= n.
```

This is proved by `sixteen_mul_layeredBottomVariableSupport_card_le_of_actual_margin`.  Thus the
old sufficient condition `n` on the order of `|S|*K` is confirmed to be an artifact of the
prefix encoder: the actual recurrence boundary supplies a dimension-free support fraction at
most `1/16`.  A finite audit at extremal support size for `s = 0,...,4`, `M = 1,...,30`, and the
first ten admissible shell scales found no counterexample; the largest sampled scaled ratio was
below `4.811e-10`.  This computation is diagnostic evidence only, not part of the Lean proof.

The precise next frontier is a generic without-replacement tail lemma: for `K = 2*d`, prove that
`16*|S| <= n` and `K <= n` imply

```text
(sum q=d+1..K, choose |S| q * choose (n-|S|) (K-q)) * 2^d <= choose n K.
```

A promising elementary route is to mark a canonical `d`-subset of the support in every upper-tail
set, then combine `choose K d <= 2^K` with the sixteenfold ambient gap.  Specializing that lemma at
`K=20R`, `d=10R` would close the support-only contraction under the actual margin; only if this
route fails should the fixed-polarity refinement return to the frontier.  No P-versus-NP
conclusion follows.

### The sixteen-density hypergeometric tail and actual-margin contraction are closed

The support-only probabilistic frontier is now kernel-checked.  The generic theorem
`hypergeometric_upper_tail_sixteen_density` proves, for all natural `n`, support sizes `a`, and
half-shell depths `d`, that

```text
16*a <= n
  =>
(sum q=d+1..2d, choose a q * choose (n-a) (2d-q)) * 2^d
  <= choose n (2d).
```

The proof is elementary and division-free.  `pow_mul_choose_le_choose_mul` first formalizes the
injection obtained by independently labelling selected coordinates.  Giving every selected
support coordinate one of 32 labels and applying Vandermonde embeds the weighted upper tail in
`choose (n+31a) (2d)`.  In the nonzero-tail case `d+1 <= a`; together with `16a <= n`, a
descending-factorial comparison bounds this enlarged row by

```text
choose (n+31a) (2d) <= 4^(2d) * choose n (2d).
```

The remaining powers cancel with slack because
`2^d * 4^(2d) <= 32^(d+1)`.  The zero-tail case `a <= d` is discharged exactly.  No asymptotics,
probability library, division in `Nat`, or hidden `2^(n-K)` fiber is used.

The circuit specialization
`normalizedLayered_commonShallowBad_scaled_le_of_actual_margin` composes this generic result with
the exact support-tail count and the audited recurrence margin.  For bottom width `s+1`,

```text
8*(s+2)*bottomSlotCount(C)*2^(s+1) + 4*(s+2) <= n
```

and `20R <= fuel` now imply the intended contraction directly:

```text
|commonShallowBad normalizedFamily fuel (20R) (10R) residualDepth| * 2^(10R)
  <= |{sigma : Restriction n | stars sigma = 20R}|.
```

Thus the support-only envelope is sufficient at the actual circuit-owned recurrence boundary;
the fixed-polarity refinement is not needed for this single-round estimate.  The old
`n`-versus-`|S|*K` obstruction was indeed an encoder artifact.

The precise next frontier is compositional: expose this new actual-margin capstone in the
quantitative-iteration module and prove one complete survivor round that combines (i) membership
outside `commonShallowBad`, (ii) the normalized common trunk, and (iii)
`CommonShallowAt.leaf_collapseRound_bottomSlotCount_bound`.  Then audit whether the restricted
leaf circuit and its `20R`-coordinate survivor cube re-establish the same actual-margin premise
for the next round.  The first failure point, if any, must be retained as the recurrence
counterexample; no P-versus-NP conclusion follows from the single-round contraction alone.

### The normalized survivor round is composed; the next-shell interface is now the gap

`actualMargin_normalizedSurvivorRound` packages the complete circuit-owned single-round
interface.  Under bottom width `s+1`, nonempty layered gates, ample fuel, and

```text
8*(s+2)*bottomSlotCount(C)*2^(s+1) + 4*(s+2) <= n,
```

it proves both the `2^(10R)` contraction of the normalized bad set on the `20R` shell and the
following pointwise consequence.  Every root outside that bad set has a common trunk of depth at
most `10R`; for every assignment reaching a trunk leaf `tau`, the existing collapse is legal and

```text
bottomSlotCount(collapseRound fuel tau C)
  <= bottomSlotCount(C) * (2^(residualDepth+1) + 1).
```

The quantitative-iteration module now imports the module containing this capstone, so the result
is available at the iteration boundary without duplicating the normalized-family construction.

This composition exposes a sharper gap than the slot recurrence alone.  `CommonShallowAt` permits
an arbitrary extending restriction as a leaf payload.  Its interface proves only
`stars(tau) <= fuel`; it does not prove that the leaf retains `10R` live coordinates, or even a
lower bound on `stars(tau)`.  Consequently the current theorem cannot yet instantiate the next
`20R` survivor shell, regardless of whether the displayed slot upper bound is arithmetically
small enough.  This is a genuine interface issue: the common tree's query depth does not by itself
bound extra coordinates fixed inside an arbitrary leaf payload.

The precise next frontier is to normalize common-trunk leaf payloads to the canonical path
endpoint (or prove a semantics-preserving replacement theorem) so that a depth-`<=10R` path from a
`20R` root retains at least `10R` live variables.  Then test the next actual-margin inequality
using the proved slot multiplier.  If canonicalization is impossible, preserve the first
`CommonShallowAt` certificate whose leaf over-fixes the survivor cube as the recurrence-interface
counterexample.  No P-versus-NP conclusion follows.

### Leaf agreement closes the over-fixing gap

The feared arbitrary-payload counterexample cannot exist under the actual `CommonShallowAt`
definition.  The definition requires every reached leaf restriction to agree with every total
assignment following that path.  If a coordinate was live at the root and absent from the
followed query path, flipping only that coordinate reaches the same leaf.  A fixed value in the
leaf payload would then have to agree with both Boolean values, a contradiction.

This argument is now kernel checked in generic form:

```text
CommonTree.stars_run_ge_sub_of_leaf_agreement:
  depth(trunk) <= d
  -> stars(root) - d <= stars(run trunk x).

CommonShallowAt.leaf_stars_ge_sub:
  CommonShallowAt gates fuel root d s
  -> exists trunk, depth(trunk) <= d
       and stars(root) - d <= stars(run trunk x)
       and every residual gate has depth <= s.
```

The same bound is threaded through `CommonShallowAt.leaf_shallows` and
`CommonShallowAt.leaf_collapseRound_bottomSlotCount_bound`.  Consequently the normalized
survivor-round capstone now proves, at each reached leaf `tau`, all three recurrence facts at once:

```text
10R <= stars(tau) <= fuel

bottomSlotCount(collapseRound fuel tau C)
  <= bottomSlotCount(C) * (2^(residualDepth+1) + 1).
```

Thus canonicalizing the leaf payload is unnecessary for live-count preservation.  The payload
need not be definitionally the path endpoint; its universal agreement property already prevents
it from fixing unqueried root-live coordinates.

Verification completed for the common-tree/common-shallow target (8,238 jobs) and for the full
layered-bridge source elaboration.  A separate small integration theorem reproducing the new
`20R -> 10R` leaf conclusion from the strengthened layered bridge also elaborated.  The expensive
TwoSAT bridge rebuild was externally terminated before producing a new object file, so no full
affected build is claimed for this checkpoint.  The new generic capstones report exactly
`propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was added.

The precise next frontier is now arithmetic and coordinate transport: choose an exact `10R`-live
subcube inside each leaf with `stars(tau) >= 10R`, reindex the collapsed circuit onto that cube,
and test the following round's actual-margin inequality using the proved slot multiplier.  The
first failure between subcube transport and the margin recurrence should be retained explicitly.
No P-versus-NP conclusion follows.

### Exact half-shell subcubes are selected and collapse equivalence descends to them

The first half of the coordinate-transport frontier is now kernel checked.  The generic theorem
`exists_restrictionExtends_stars_eq` proves that whenever `K <= stars(base)`, there is a genuine
restriction extension `rho` with exactly `K` live coordinates.  It selects a `K`-element subset of
`freeVars(base)` and uses the existing deterministic `keepFreeExtension`; hence it preserves every
value already fixed by `base` and introduces no coordinate outside the base-live set.

The circuit-owned capstone `actualMargin_normalizedSurvivorRound_exactSubcube` composes this with
the actual-margin survivor theorem.  At every reached good leaf `tau`, it now selects an ambient
restriction `kappa` satisfying

```text
RestrictionExtends tau kappa
stars(kappa) = 10R
stars(kappa) <= fuel
```

and proves

```text
EquivOn kappa C (collapseRound fuel tau C)

bottomSlotCount(collapseRound fuel tau C)
  <= bottomSlotCount(C) * (2^(residualDepth+1) + 1).
```

The equivalence transport is direct: every assignment agreeing with the finer `kappa` restriction
agrees with `tau`, so the already proved leaf collapse equivalence applies.  Thus exact survivor
selection itself is not an obstruction, and no arbitrary choice of values for the consumed live
coordinates invalidates the collapse semantics.

The layered-bridge target build completed successfully (8,348 jobs).  The new TwoSAT capstone
elaborated in the full source and reports only `propext`, `Classical.choice`, and `Quot.sound`.
The expensive remainder of that whole-file source pass was manually stopped after it had proceeded
well beyond the capstone without an error, so no full TwoSAT build is claimed.  No `sorry`, `admit`,
custom axiom, `unsafe`, or `native_decide` was introduced.

The precise next frontier is the remaining coordinate-type transport: build a canonical equivalence
between `Fin (10R)` and `freeVars(kappa)`, reindex literals and the collapsed `Layered n` circuit onto
that type while substituting the coordinates fixed by `kappa`, and prove evaluation, width, depth,
and bottom-slot-count preservation.  Only then can the next round's actual-margin premise be stated
on ambient dimension `10R` and tested against the proved slot multiplier.  The first failed
preservation law or arithmetic inequality should be retained explicitly.  No P-versus-NP conclusion
follows.

### Full layered evaluation and depth now transport to the exact survivor cube

The existing live-coordinate machinery has been lifted from indexed DNF families to the complete
`Layered` syntax.  `localizeLiveLayered kappa C` recursively substitutes every coordinate fixed by
`kappa`, relabels each remaining coordinate through the canonical `liveCoordEquiv`, and retains the
ordered internal `gAnd`/`gOr` tree.  CNF gates are localized through their De Morgan DNF dual; the new
kernel-checked involution `negDNF_negDNF` prevents a polarity mismatch at that boundary.

Two preservation laws are now proved:

```text
eval (localizeLiveLayered kappa C) x
  = eval C (liftLiveAssignment kappa x)

depth (localizeLiveLayered kappa C) = depth C.
```

Thus, for the exact subcube selected by
`actualMargin_normalizedSurvivorRound_exactSubcube`, rewriting by
`stars(kappa) = 10R` genuinely produces a semantically equivalent circuit over `Fin (10R)` with the
same layered depth.  No auxiliary circuit model or arbitrary coordinate bijection is required.

The focused quantitative-iteration source elaboration passed.  The new transport theorems use only
the standard logical axioms already present in the canonical live-coordinate equivalence; no
`sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was introduced.

The precise next frontier is to finish the two quantitative preservation laws for
`localizeLiveLayered`: `BottomWidth w` and `bottomSlotCount` must not increase under bottom-payload
filtering.  Then compose all four laws directly with the exact-subcube survivor capstone and test the
next actual-margin inequality at ambient dimension `10R`.  The first arithmetic failure must be
retained explicitly.  No P-versus-NP conclusion follows.

### Width and slot transport are closed; the next-margin schedule is now explicit

Live-coordinate transport now has all four required circuit laws.  In addition to evaluation and
exact layered-depth preservation, the kernel-checked theorems
`localizeLiveLayered_BottomWidth` and `localizeLiveLayered_bottomSlotCount_le` prove

```text
BottomWidth w C -> BottomWidth w (localizeLiveLayered kappa C)

bottomSlotCount (localizeLiveLayered kappa C) <= bottomSlotCount C.
```

The CNF case is not assumed by duality: `localizeLiveCnf_length_le` and
`localizeLiveCnf_width_le` explicitly use the fact that both surrounding `negDNF` maps preserve
clause count and literal-list length.  The internal `gAnd`/`gOr` cases retain their child lists;
the slot proof sums the pointwise bottom-payload inequalities, including the unit charge for an
empty constant gate.

Consequently coordinate transport itself introduces no quantitative loss.  Composing these laws
with the exact-subcube survivor bound gives the following worst-case next-round data on ambient
dimension `10R`: if the current slot count is `M` and the residual parameter is `r`, then

```text
width_next <= r + 1
slots_next <= M * (2^(r+1) + 1).
```

The next actual-margin premise is therefore reduced exactly to the schedule obligation

```text
8*(r+2)*M*(2^(r+1)+1)*2^(r+1) + 4*(r+2) <= 10R.
```

This obligation is not a consequence of the current single-round assumptions: those constrain
the old ambient dimension `n`, while the next ambient dimension is the independently selected
`10R`.  For example, at the abstract envelope values `r=0`, `M=1`, `R=1`, its left side is `104`
and its right side is `10`.  This is a failure of that parameter choice and worst-case recurrence
bound, not a circuit counterexample and not evidence that no larger schedule can work.

Focused elaboration of the quantitative-iteration source passed.  A dependency-aware target build
rebuilt the affected layered bridge and then spent several minutes rebuilding the very large
downstream TwoSAT object; it was manually stopped without an error, so no full affected build is
claimed.  The new capstones use only `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`,
`admit`, custom axiom, `unsafe`, or `native_decide` was introduced.

The precise next frontier is to package evaluation, depth, width, and slot preservation with
`actualMargin_normalizedSurvivorRound_exactSubcube`, then choose a multi-round sequence `R_i` and
residual widths satisfying both `20*R_(i+1) <= 10*R_i` and the displayed next-margin obligation at
every round.  If these inequalities fail for the intended depth schedule, retain the first failing
round and parameter tuple explicitly.  No P-versus-NP conclusion follows.

### The exact-subcube round now exports a localized next-round circuit

The coordinate laws and the exact survivor witness are now packaged by the kernel-checked theorem
`actualMargin_normalizedSurvivorRound_localized`.  It consumes the conclusion of
`actualMargin_normalizedSurvivorRound_exactSubcube`; for every good `20R`-shell root it reconstructs
the common-shallow leaf certificate, selects the same exact `10R`-live coordinate budget, and returns
the localized collapse

```text
D = localizeLiveLayered kappa (collapseRound fuel tau C)
```

with all four iteration interfaces in one witness:

```text
eval D z = eval C (liftLiveAssignment kappa z)
depth D = depth (collapseRound fuel tau C)
BottomWidth (residualDepth+1) D
bottomSlotCount D <= bottomSlotCount(C) * (2^(residualDepth+1)+1).
```

The evaluation statement composes exact-subcube collapse equivalence with the canonical assignment
lift.  Width and slot count are not inferred from semantics: they come respectively from the reached
leaf's `Shallows` certificate and the proved syntactic localization inequalities.  Thus the next
round is now represented by an actual `Layered (stars kappa)` circuit, and `stars kappa = 10R` is
carried alongside it; there is no remaining coordinate-transport interface gap.

Focused elaboration of the full quantitative-iteration source passed.  The capstone reports only
`propext`, `Classical.choice`, and `Quot.sound`.  A dependency-aware TwoSAT target replayed its
dependencies and entered the known long final compilation phase; it was manually stopped without
an error, so no full affected build is claimed.  `git diff --check` passed.  The earlier failing
abstract tuple `r=0, M=1, R=1` remains recorded and is not promoted to a circuit counterexample.

The precise next frontier is purely the finite-round schedule: define slot bounds
`M_(i+1) = M_i * (2^(r_i+1)+1)` and choose survivor parameters satisfying, for each transition,

```text
20*R_(i+1) <= 10*R_i
8*(r_(i+1)+2)*M_(i+1)*2^(r_(i+1)+1) + 4*(r_(i+1)+2) <= 10*R_i.
```

The next step should formalize a backward finite-horizon construction, then test whether its required
initial `R_0` is compatible with the original ambient shell and fuel bounds.  The first incompatible
round or initial-budget inequality must be retained explicitly.  No P-versus-NP conclusion follows.

### Finite backward schedules exist; initial-budget compatibility is isolated

The arithmetic part of the finite-horizon schedule is now kernel checked.  The quantitative-iteration
module defines the exact next-round demand

```text
nextRoundActualMargin(r,M) = 8*(r+2)*M*2^(r+1) + 4*(r+2)
```

and the forward slot envelope

```text
M_0 = M₀
M_(i+1) = M_i * (2^(r_i+1) + 1).
```

`FiniteBackwardSurvivorSchedule d M r R` records, at every `i < d`, both obligations exposed by
the localized exact-subcube round:

```text
20*R_(i+1) <= 10*R_i
nextRoundActualMargin(r_(i+1), M_(i+1)) <= 10*R_i.
```

The theorem `exists_finiteBackwardSurvivorSchedule` proves that such an `R` exists for every finite
horizon and every prescribed width/slot sequence.  Its induction is explicit: after constructing
the tail, it takes

```text
R_i = 2*R_(i+1) + nextRoundActualMargin(r_(i+1), M_(i+1)).
```

The specialization `exists_iteratedSlot_finiteBackwardSurvivorSchedule` feeds this construction the
actual forward slot recurrence.  Thus there is no finite-horizon inconsistency between survivor
nesting and the next-margin inequalities themselves.  This theorem intentionally supplies no upper
bound on `R_0`: making `R_0` large closes later transitions but simultaneously increases the initial
`20*R_0` shell and fuel requirement.

The earlier small failed choice is now preserved as a theorem rather than prose alone:

```text
not (nextRoundActualMargin 0 1 <= 10*1),
```

since its left side is `104`.  It refutes only that particular envelope choice, not the backward
construction.

Focused elaboration of the full quantitative-iteration source passed.  The three new arithmetic
capstones report only `propext`.  No `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide`
was added.  A dependency-aware target build replayed through the large layered-bridge dependency
without errors and was manually stopped during the known long final compilation phase, so no full
affected build is claimed for this checkpoint.  `git diff --check` passed.

The precise next frontier is to derive a usable upper bound on the constructed `R_0` (preferably for
the intended residual-depth sequence), then compare `20*R_0` simultaneously with the original fuel
and ambient-shell budgets and compare the initial circuit margin with `n`.  The first incompatible
initial inequality or concrete depth/slot tuple must remain recorded.  No P-versus-NP conclusion
follows.

### The backward construction now exposes an explicit initial budget

The finite schedule existential has been refined to retain the initial value chosen by the proof.
The new recursive quantity `initialBackwardSurvivorBudget d M r` is

```text
B(0; M, r) = 0
B(d+1; M, r) = 2*B(d; shift M, shift r) + nextRoundActualMargin(r_1, M_1).
```

`exists_finiteBackwardSurvivorSchedule_initial_eq` constructs a schedule satisfying the same two
roundwise inequalities as before and proves exactly `R_0 = B(d; M, r)`.  Thus the original shell and
fuel obligation is no longer hidden behind an existential: it is the concrete test

```text
20 * B(d; M, r) <= min(n, fuel).
```

The theorem `initialBackwardSurvivorBudget_le_geometric` supplies the closed bound

```text
B(d; M, r) <= (2^d - 1) * A
```

whenever every later-round actual margin is at most `A`.  This separates the unavoidable geometric
weight from the slot/depth-dependent maximum margin; it does not assert that the resulting bound is
compatible with a proposed circuit regime.

The smallest residual-depth calibration is already nontrivial.  With `r_i = 0` and the verified
slot recurrence, two rounds give

```text
M_1 = 3*M_0,
M_2 = 9*M_0,
B(2) = 672*M_0 + 24,
20*B(2) = 13440*M_0 + 480.
```

Both equalities are kernel checked.  In particular, even the shallowest two-round use of this
specific conservative construction requires `n` and `fuel` to be at least
`13440*M_0 + 480`.  This is a concrete budget floor for the construction, not a lower bound for all
possible schedules: the recurrence deliberately pays the full margin rather than its division by
ten, so it is not yet quantitatively tight.

Focused elaboration of the full quantitative-iteration source passed.  The new schedule and
geometric capstones use only `propext` and `Quot.sound`; the two numerical calibration capstones use
only `propext`.  No `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was added.

The precise next frontier is to tighten the backward step to the least natural survivor value

```text
R_i = max(2*R_(i+1), ceil(nextRoundActualMargin(r_(i+1), M_(i+1))/10)),
```

then recompute the two-round calibration and derive its finite-depth bound.  Only that least-budget
schedule should be compared against the intended polynomial initial slot envelope and the ambient
`n`/fuel budget; the present `13440*M_0+480` figure must not be mistaken for an impossibility result.
No P-versus-NP conclusion follows.

### The least backward survivor budget is attained and minimal

The conservative backward sum has now been replaced for quantitative comparisons by a separate,
kernel-checked least recurrence:

```text
ceilDivTen(x) = (x+9)/10,
L(0; M, r) = 0,
L(d+1; M, r) = max(2*L(d; shift M, shift r),
                    ceilDivTen(nextRoundActualMargin(r_1,M_1))).
```

`le_ten_mul_ceilDivTen` proves that the rounded term pays the exact `10*R` margin.
`exists_finiteBackwardSurvivorSchedule_least_initial_eq` constructs a schedule with initial value
exactly `L`, while `leastBackwardSurvivorBudget_le_initial` proves the converse: every schedule
satisfying `FiniteBackwardSurvivorSchedule` has `L <= R_0`.  Thus this is genuinely the least
natural initial survivor budget for the two recorded round obligations, rather than merely a
smaller witness.

There is also a finite-horizon bound.  If all `d+1` later margins are at most `A`, then

```text
L(d+1; M, r) <= 2^d * ceil(A/10).
```

This separates the one-time division by ten from the geometric shell nesting.  It is strictly more
informative than the earlier conservative `(2^(d+1)-1)*A` bound, but still depends on a usable
common `A` from the forward slot and residual-depth sequences.

For two residual-depth-zero rounds, where `M_1=3*M_0` and `M_2=9*M_0`, the exact calibration is

```text
L(2) = 2 * floor((288*M_0 + 17)/10),
20*L(2) = 40 * floor((288*M_0 + 17)/10)
        <= 1160*M_0 + 80.
```

The second-round margin dominates the first after shell nesting.  The leading shell coefficient is
therefore about `1152`, not the conservative `13440`; the earlier theorem remains preserved as an
audit of that deliberately overpaying route, not as an impossibility claim.

Focused elaboration of the full quantitative-iteration source passed.  Printed new capstones use
only `propext`, `Classical.choice`, and `Quot.sound`.  No `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was added.

The precise next frontier is to instantiate `L` with the intended finite residual-depth sequence
and its actual forward `iteratedSlotBound`, derive the resulting polynomial expression in the
initial circuit slot envelope, and test both `20*L <= min(n,fuel)` and the round-zero actual-margin
premise.  The first failing depth/slot/ambient inequality must be retained explicitly.  No
P-versus-NP conclusion follows.

### The cheapest all-depth schedule is exact; the initial density premise is now the blocker

The intended quantitatively cheapest residual-depth sequence, `r_i = 0`, has now been evaluated at
every finite depth.  The kernel-checked forward recurrence is

```text
M_i = M_0 * 3^i.
```

For `d+1` collapse rounds, the last actual-margin obligation dominates all earlier obligations even
after their factor-two nesting charges.  Consequently the least initial survivor budget is exactly

```text
L(d+1) = 2^d * floor((32*M_0*3^(d+1) + 17)/10).
```

The corresponding initial shell/fuel demand obeys

```text
20*L(d+1) <= 32*6^(d+1)*M_0 + 17*2^(d+1).
```

Thus for fixed circuit depth the survivor schedule itself costs only a constant multiple of the
initial bottom-slot envelope.  This closes the previously open finite-depth recurrence calculation;
the earlier two-round formula is its `d=1` instance.

The simultaneous round-zero audit exposes a stricter obstruction.  The actual-margin premise for an
initial width-`s+1` circuit is

```text
nextRoundActualMargin(s,M_0)
  = 8*(s+2)*M_0*2^(s+1) + 4*(s+2) <= n.
```

`nextRoundActualMargin_not_le_ambient_of_ambient_le_slots` proves that this is false for every
`s,n,M_0` with `n <= M_0`.  In particular, the present circuit-owned density theorem does not even
start on the broad linear-or-larger slot regime, hence a generic polynomial-size envelope cannot be
fed into this iteration merely by choosing the least survivor schedule.  This is a failure of the
current worst-case support/slot margin, not a circuit counterexample and not an impossibility theorem
for switching arguments.

Focused elaboration of the full quantitative-iteration source passed.  The new capstones report only
standard logical axioms; no `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was added.
`git diff --check` passed.

The precise next frontier is to sharpen the round-zero density interface: replace total bottom-slot
count by an effective variable-support or overlap-sensitive quantity that can be sublinear in `n`
even for polynomially many slots, while preserving normalization, localization, and the exact shell
contraction.  Absent such a refinement, the first-round premise—not the multi-round recurrence—is the
defensible stopping point.  No P-versus-NP conclusion follows.

### The first-round density interface now charges exact bottom-variable support

The existing hypergeometric support-tail argument has now been promoted through the complete
survivor-round API.  The new premise is

```text
16 * |layeredBottomVariableSupport C| <= n,
```

where `layeredBottomVariableSupport C` is the union of the variables in the unpolarized syntactic
bottom gates.  In particular, repeated clause occurrences and the normalized De Morgan polarity
are not charged again.  The new kernel-checked interfaces are:

- `normalizedLayered_commonShallowBad_scaled_le_of_sixteen_support`, the half-shell contraction;
- `supportDensity_normalizedSurvivorRound`, which also exports the leaf slot recurrence;
- `supportDensity_normalizedSurvivorRound_exactSubcube`, which selects the exact half shell and
  transports collapse equivalence;
- `supportDensity_normalizedSurvivorRound_localized`, which reindexes the reached circuit onto its
  live coordinate cube while preserving evaluation, depth, bottom width, and the slot bound.

Thus the previously recorded round-zero failure for `n <= M_0` is not intrinsic to a large slot
envelope: the first round can start with arbitrarily many overlapping clause slots provided their
distinct bottom-variable union occupies at most one sixteenth of the ambient coordinates.  The old
slot-based failure theorem remains valid for the stronger historical premise and is retained as a
failed worst-case route.

Focused elaboration reached beyond all new declarations after resolving a name collision with an
older, alphabet-envelope theorem.  A dependency-aware target build replayed the project and entered
the known long final compilation phase without reporting a new source error; it was manually stopped,
so no completed target or full build is claimed at this checkpoint.  `git diff --check` passed.  No
`sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was added.

The precise next frontier is to audit support propagation, not slot propagation: prove the strongest
valid upper bound on `|layeredBottomVariableSupport D|` for the localized collapsed circuit `D`.
If restriction/localization makes this support nonincreasing, the support-density premise may iterate
without the polynomial slot obstruction; if collapse introduces genuinely new live support or only
the ambient `10*R` bound is available, record the first resulting support-budget inequality.  No
P-versus-NP conclusion follows.

### Canonical leaf collapse is now proved support-nonincreasing

The first structural link in that audit is kernel checked at both bottom-gate polarities.  The new
clause-level theorems

```text
dtreeToCNF_canonicalDT_clauseVariableSupport_subset
dtreeToDNF_negTree_canonicalDT_clauseVariableSupport_subset
```

prove that every variable in every clause emitted by the canonical rejecting-path CNF, or by the
dual negated-tree accepting-path DNF, already occurs in the source bottom payload.  Their gate-level
corollaries state directly

```text
gateVariableSupport(switchedGate) ⊆ gateVariableSupport(sourceGate).
```

The proof composes the existing path-clause variable theorem with exact preservation of queried
variables by `toDTree` and `negTree`, then with
`canonicalDT_queriedVars_subset_gateVariableSupport`.  Thus the switching conversion itself does
not introduce new support; this rules out the most serious local failure mode.  It does not yet
justify a full-circuit cardinal inequality, because the leaf theorem must still be threaded through
the recursive `leafCollapse`, the flatten-only `mergePass`, and the coordinate map used by
`localizeLiveLayered`.

Direct elaboration of the large TwoSAT source passed these declarations and continued through the
later file without a source error.  The run had not completed at this checkpoint, so no completed
target or full build is claimed.  No `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was
introduced.

The precise next frontier is to lift the two gate-level subset theorems to

```text
layeredBottomVariableSupport (collapseRound fuel tau C)
  ⊆ layeredBottomVariableSupport C,
```

using a support-valued `BottomPred` invariant through `leafCollapse` and the existing
`mergePass_BottomPred`; then prove the localized image/intersection law.  That law will show whether
the chosen exact survivor set `freeVars kappa` can be made mostly disjoint from the old support, which
is the condition actually needed to recover the factor-16 density premise on the `10R` cube.  No
P-versus-NP conclusion follows.

### Full recursive collapse is now proved support-nonincreasing

The leaf-level support fact has now been threaded through the actual recursive circuit
transformation.  The new preservation-style invariant

```text
leafCollapse_BottomPred_of
```

differs materially from the older setter-style `leafCollapse_BottomPred`: it assumes a predicate on
the source bottom clauses and permits each of the two canonical leaf conversions to preserve that
predicate.  This is the source-sensitive interface needed for support containment.  Instantiating it
with `clauseVariableSupport T ⊆ layeredBottomVariableSupport C` yields

```text
layeredBottomVariableSupport (leafCollapse fuel tau C)
  ⊆ layeredBottomVariableSupport C.
```

The helper `layeredBottomVariableSupport_subset_of_BottomPred` converts the per-clause invariant
back to the circuit-wide finite union.  Composing the same invariant with the existing
`mergePass_BottomPred` then proves the complete round theorem

```text
layeredBottomVariableSupport (collapseRound fuel tau C)
  ⊆ layeredBottomVariableSupport C.
```

Thus neither recursive traversal nor same-polarity flattening reintroduces support; the full
unlocalized collapse is support-nonincreasing, with no depth, shallowness, fuel, or cleanliness
hypothesis.  This closes the structural half of the propagation audit.

Focused elaboration of the large TwoSAT source passed all new declarations and continued thousands
of later lines without an error before the 90-second run was stopped by its time limit.  No completed
target or full build is claimed.  `git diff --check` passed.  No `sorry`, `admit`, custom axiom,
`unsafe`, or `native_decide` was added.

The precise next frontier is the coordinate-localization law.  Prove that the bottom support of
`localizeLiveLayered kappa D` is exactly the preimage, under the live-coordinate embedding, of
`layeredBottomVariableSupport D ∩ freeVars kappa`; at minimum prove the corresponding subset and
cardinality bound.  Combined with round support monotonicity, this will reduce the next factor-16
density premise on the `10R` cube to an explicit bound on
`|layeredBottomVariableSupport C ∩ freeVars kappa|`.  The survivor selector must then be audited to
determine whether it controls that overlap or merely the total number of survivors.  No P-versus-NP
conclusion follows.

### Localization charges the old-support/survivor overlap from above

The coordinate-localization audit now has its strongest generally valid direction.  At clause,
DNF, CNF, and recursively layered levels, mapping localized support back through `liveCoordEquiv`
gives

```text
image(embed_kappa,
  layeredBottomVariableSupport (localizeLiveLayered kappa D))
    ⊆ layeredBottomVariableSupport D ∩ freeVars kappa.
```

Injectivity of the embedding gives the cardinal bound

```text
|layeredBottomVariableSupport (localizeLiveLayered kappa D)|
  <= |layeredBottomVariableSupport D ∩ freeVars kappa|.
```

Composing it with unconditional collapse-support monotonicity yields the actual round recurrence

```text
|layeredBottomVariableSupport
    (localizeLiveLayered kappa (collapseRound fuel tau C))|
  <= |layeredBottomVariableSupport C ∩ freeVars kappa|.
```

The tempting equality is deliberately not asserted: it is false when a variable is live in
`kappa` but occurs only in an old clause discarded because another literal is already killed.
Containment and the cardinal upper bound are therefore the correct interfaces.

Focused elaboration exposed and fixed the clause-variable rewrite and CNF-duality proof.  A
standalone focused harness then passed the complete clause/gate/layered/cardinality argument and
reported only `propext`, `Classical.choice`, and `Quot.sound`; it also checked the final composition
against an abstract collapse-support premise.  A
dependency refresh passed the support/collapse declarations and continued into the preserved late
counterexample section; that large source then hit its existing late `omega`/heartbeat failures
around lines 8215--8287, so no completed target or full build is claimed.  `git diff --check`
passed.  No `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was added.

The precise next frontier is the survivor selector.  Audit whether its exact `10*R` survivor set
proves

```text
16 * |layeredBottomVariableSupport C ∩ freeVars kappa| <= 10*R.
```

If current selection controls only total survivor count, the next needed step is an overlap-aware
shell selection/counting lemma.  No P-versus-NP conclusion follows.

### Exact-size survivor selection alone cannot propagate factor-sixteen support density

The selector audit is now negative and kernel checked.  The pointwise theorem
`freeVars_subset_of_restrictionExtends` strengthens the earlier live-count monotonicity statement:
an extension can only remove coordinates from the current live set.  Consequently,
`support_inter_freeVars_card_eq_stars_of_cover` proves that if the old support already covers all
coordinates live at a reached leaf, then every further extension has support overlap equal to its
entire star count.  Choosing a different exact-size subset cannot help.

The concrete witness `sparseSupport16`/`sparseSupportRoot16` shows that this obstruction is compatible
with the existing global premise.  Its support is the singleton `{0}` in `Fin 16`, so

```text
16 * |sparseSupport16| <= 16.
```

But the leaf has exactly that one coordinate live.  For every extension `rho` with `stars rho = 1`,
`sparseSupport16_exact_survivor_overlap` proves

```text
|sparseSupport16 ∩ freeVars rho| = 1
and not (16 * |sparseSupport16 ∩ freeVars rho| <= 1).
```

Thus the current `exists_restrictionExtends_stars_eq` interface controls only survivor cardinality;
global support sparsity does not propagate through an adversarially support-concentrated leaf.  The
counterexample is deliberately retained, so the iteration cannot silently assume the desired
factor-sixteen overlap inequality.

A focused harness compiled all new declarations and reported only `propext`, `Classical.choice`, and
`Quot.sound` for the capstone.  No `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was
introduced.

The precise next frontier is no longer a deterministic subset selector.  It is to strengthen the
common-trunk counting event so that reached leaves carry an overlap guarantee relative to
`layeredBottomVariableSupport C` (or to jointly count bad shallowness and support concentration).
The first quantitative target is a shell/trunk lemma ensuring enough live coordinates outside the
old support to choose `10*R` survivors with overlap at most `(10*R)/16`; absent such a correlated
count, support-density iteration fails even though collapse and localization are support-
nonincreasing.  No P-versus-NP conclusion follows.

### The overlap-aware survivor selector now has an exact leaf-capacity interface

The deterministic part of the correlated-selection problem is now kernel checked.  For a reached
leaf `base`, old support `S`, survivor target `K`, and overlap allowance `q`,
`exists_restrictionExtends_stars_eq_inter_card_le` proves that

```text
K <= stars(base)
K - q <= |freeVars(base) \ S|
q <= K
```

is sufficient to choose an extension `rho` with exactly `K` survivors and

```text
|S ∩ freeVars(rho)| <= q.
```

The construction first keeps `K-q` outside-support coordinates and then fills the remaining `q`
positions from the still-live coordinates.  It is therefore compatible with the existing
`keepFreeExtension` selector and preserves all values already fixed at the leaf.

The converse capacity charge is also formal.  Every restriction extension satisfies

```text
stars(rho) <= |freeVars(base) \ S| + |S ∩ freeVars(rho)|.
```

Consequently, factor-sixteen overlap density forces

```text
15 * stars(rho) <= 16 * |freeVars(base) \ S|.
```

Finally, `exists_restrictionExtends_factorSixteen_overlap_density` packages the sufficient side:
any integer `q` with `16*q <= K` and outside capacity at least `K-q` yields an exact `K`-survivor
extension satisfying `16*|S ∩ freeVars(rho)| <= K`.  Thus, up to the unavoidable integer
rounding, the deterministic selector needs and can use a `15/16` outside-support fraction.  The
retained `Fin 16` counterexample is the zero-outside-capacity endpoint of this criterion.

A standalone focused harness compiled the constructive selector, the necessity theorem, and the
factor-sixteen corollary.  Their printed axioms are exactly `propext`, `Classical.choice`, and
`Quot.sound`.  Direct elaboration of the large source reached the new block; after the one local
proof issue was fixed, the remaining module failures are the preserved earlier dependency-refresh
errors beginning around line 1013.  No completed target or full build is claimed.  No `sorry`,
`admit`, custom axiom, `unsafe`, or `native_decide` was added.

The precise next frontier is now purely the correlated trunk count: bound the common-shallow roots
whose reached leaves have fewer than `K-q` live coordinates outside
`layeredBottomVariableSupport C`, with `K = 10*R` and an integer `q` satisfying `16*q <= K`.
Combining that count with the new selector would re-establish the factor-sixteen support premise on
the next localized cube; without it, the current bad-shallowness count alone does not iterate.  No
P-versus-NP conclusion follows.

### The correlated leaf-capacity event collapses to the existing root support tail

The missing correlation does not require a new leaf-wise counting argument.  The canonical
normalized-family prefix queries only coordinates in `familyVariableSupport`, and that support is
contained in the old unpolarized `layeredBottomVariableSupport`.  Therefore every coordinate that
is live at the root and outside the old support remains live at every canonical prefix leaf.

This makes the already formalized root event `liveLayeredBottomSupportTail C (20*R) (10*R)` the
right strengthened bad set.  Outside it, the root has at most `10R` live supported coordinates and
hence at least `10R` live coordinates outside the old support.  The canonical prefix preserves all
of those outside coordinates.  The new capstone
`normalizedCanonicalPrefix_zeroOverlapSurvivor_of_not_supportTail` proves simultaneously that:

```text
CommonShallowAt (normalizedLayeredBottomFamily C) fuel sigma (10*R) 0
```

and, at every canonical reached leaf, there is an extending restriction with exactly `10R`
survivors whose overlap with `layeredBottomVariableSupport C` is zero.  This is stronger than the
previous `15/16` outside-capacity target and immediately implies the next factor-sixteen support
density premise after collapse and localization.

The strengthened bad set pays no worse counting exponent.  Under

```text
16 * |layeredBottomVariableSupport C| <= n,
```

`liveLayeredBottomSupportTail_scaled_le_sixteen_density` proves that the whole root support tail,
not just `commonShallowBad`, contracts by `2^(10R)` on the `20R` shell.  Thus the same
hypergeometric estimate now supplies both residual shallowness and overlap-aware survivors; no
union bound is needed.  The retained `Fin 16` counterexample remains valid for arbitrary reached
leaves and explains why selecting the canonical support-respecting trunk is essential.

A focused source-slice harness checked the canonical-prefix support, outside-survival, complete
support-tail contraction, and zero-overlap survivor capstone.  All four printed only `propext`,
`Classical.choice`, and `Quot.sound`.  A target build refreshed 8,000+ dependencies and entered the
final large bridge elaboration but was stopped after producing no target error for several minutes;
no completed target or full build is claimed.  No `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was added.

The precise next frontier is to replace the `commonShallowBad` complement in the localized
survivor-round capstone by the stronger `liveLayeredBottomSupportTail` complement and thread its
canonical zero-overlap witness through `collapseRound` and `localizeLiveLayered`.  Then verify that
the resulting next circuit satisfies the same support-density hypothesis and audit the finite
multi-round recurrence with this strengthened good event.  No P-versus-NP conclusion follows.

### The support-tail complement now propagates through the complete localized round

The one-round interface is now kernel checked.  The pointwise theorem
`canonicalFamily_prefix_depth_eq_zero_of_live_support_le` exposes the specific canonical prefix
leaf already used by the zero-overlap selector and proves that every normalized family member has
residual depth zero there.  This removes the earlier mismatch between an existential
`CommonShallowAt` trunk and the support-respecting canonical trunk.

The capstone `supportTail_normalizedSurvivorRound_localized` now replaces the old
`commonShallowBad` complement by

```text
sigma ∉ liveLayeredBottomSupportTail C (20*R) (10*R).
```

At every reached assignment it uses that same canonical leaf `tau`, chooses an extending
restriction `kappa` with exactly `10R` survivors and zero overlap with the old bottom support,
runs `collapseRound fuel tau C`, and transports the result to the exact live-coordinate cube with
`localizeLiveLayered kappa`.  The resulting circuit `D` satisfies:

```text
eval D = eval C on the lifted kappa-subcube,
BottomWidth 1 D,
bottomSlotCount D <= 3 * bottomSlotCount C,
|layeredBottomVariableSupport D| = 0,
16 * |layeredBottomVariableSupport D| <= stars(kappa).
```

Thus support density does not merely remain factor sixteen after this round: the localized next
bottom support is empty.  The complete support-tail bad set still contracts by `2^(10R)` under the
old factor-sixteen root density premise, so no extra union bound is introduced.

A focused bridge slice compiled the new canonical-prefix theorem and the complete support-tail
count.  A focused iteration slice then compiled the localized capstone against that bridge.  All
three printed only `propext`, `Classical.choice`, and `Quot.sound`.  Direct elaboration of the full
bridge advanced through its long preserved late section but was interrupted after roughly eleven
minutes; no full target or full build is claimed.  `git diff --check` passed before this record was
added.  No `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was added.

The precise next frontier is the finite recurrence itself.  Package this strengthened localized
round as an iterable state transition whose next ambient dimension is `10R`, bottom width is one,
slot count grows by at most three, and bottom support is empty.  Then solve the backward shell/fuel
schedule across the remaining alternation depth and check that every next `20*R_next` shell fits
inside the current `10*R` cube.  The retained broad-density and small-parameter counterexamples
must remain visible during that audit.  No P-versus-NP conclusion follows.

### The zero-support recurrence has an exact geometric shell schedule

The first arithmetic and structural handoffs of the finite recurrence are now formal.  Live-
coordinate localization preserves `AltO` and `AltA` exactly, including their nonempty internal gate
lists.  Therefore an `AltO (k+3)` input becomes an `AltO (k+2)` localized collapse output, and
`localizeLiveLayered_collapseRound_NonEmptyGates` supplies the `NonEmptyGates` premise required by
the following localized round whenever an alternating layer remains.

For a terminal scale `r` and `d` transitions, define

```text
R_i = 2^(d-i) * r.
```

The theorem `zeroSupportSurvivorScale_shell_exact` proves, for every `i < d`,

```text
20 * R_(i+1) = 10 * R_i.
```

Thus the next shell is not merely bounded by the current survivor cube: it is exactly that cube.
Once the first localized round has emptied bottom support, the older slot-dependent
`nextRoundActualMargin` recurrence is unnecessary for shell fit.  The initial shell scale is
`20 * 2^d * r`, the terminal survivor parameter is `r`, and positivity propagates at every index.
This resolves the shell-balance and nonempty-gate portions of the requested iterable state.

Direct elaboration of the large iteration source checked all new declarations before reaching the
preserved dependency-refresh failures beginning at the old support block (`gateVariableSupport_negDNF`
and subsequent identifiers).  The printed axioms for the new structural capstones are only
`propext`, `Classical.choice`, and `Quot.sound`; the exact arithmetic shell theorem uses only
`propext` and `Quot.sound`.  No `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was
introduced.  No completed target or full build is claimed.

The precise next frontier is to strengthen `supportTail_normalizedSurvivorRound_localized` itself
with the `AltO (k+3) -> AltO (k+2)` witness and package its existential branch data into a recursive
localized-round state indexed by `zeroSupportSurvivorScale`.  The remaining audit must compose the
per-shell bad-set contractions (and fuel choices) across those dependent existential subcubes;
the exact shell arithmetic alone does not yet provide that global counting composition.  The
retained broad-density and small-parameter counterexamples remain applicable to the first round.
No P-versus-NP conclusion follows.

### The support-tail round now carries the alternating-shape handoff

The complete localized support-tail capstone now consumes the actual structural premise

```text
AltO (k+3) C
```

rather than only `NonEmptyGates C`.  For every selected canonical leaf and zero-overlap survivor
restriction, `supportTail_normalizedSurvivorRound_localized` returns both

```text
AltO (k+2) D
NonEmptyGates D
```

for `D = localizeLiveLayered kappa (collapseRound fuel tau C)`.  Thus the dependent circuit witness
produced by one round has exactly the shape and nonemptiness required to invoke the next round; the
nonemptiness premise used in the slot bound is now derived from the incoming alternating shape.

The transport lemma was correspondingly generalized to take distinct collapse and localization
restrictions.  This matters in the real survivor round: the collapse occurs at the canonical prefix
leaf `tau`, while localization uses its exact-size extension `kappa`.  Conflating those restrictions
would not type the actual composition.

A focused source-slice harness compiled the generalized transport lemmas and the strengthened
support-tail capstone.  The capstone printed only `propext`, `Classical.choice`, and `Quot.sound`.
Direct elaboration of the large source also checked the generalized structural declarations before
reaching the preserved dependency-refresh failures in the old support block.  No `sorry`, `admit`,
custom axiom, `unsafe`, or `native_decide` was added.

The precise next frontier is to define the dependent recursive localized-round state over
`zeroSupportSurvivorScale`, using the returned `AltO` witness at each successor step, and then lift
the one-shell support-tail contraction through that recursion.  The unresolved quantitative issue
is the global composition of bad-root counts across changing subcube coordinate types and fuel
choices; the structural handoff and exact shell fit are now both available.  No P-versus-NP
conclusion follows.

### The recursive localized state now retains its semantic subcube edge

The dependent state interface is now explicit.  `ZeroSupportLocalizedState R level M` stores an
existential ambient dimension `n`, a circuit on `Fin n`, the exact identity `n = 20*R`, alternating
shape `AltO (level+2)`, bottom width one, slot bound `M`, and empty bottom support.  Keeping `n` as a
field avoids casting a circuit produced on the natural coordinate type `Fin (stars κ)`.

More importantly, `ZeroSupportLocalizedStep` stores the actual restriction `κ`, its child circuit
on `Fin (stars κ)`, and the semantic equation

```text
eval child z = eval parent (liftLiveAssignment κ z).
```

Thus the recursive object is an edge-labelled tree of dependent states, not merely a sequence of
unrelated circuits.  `ZeroSupportLocalizedStep.toState` forgets only this semantic edge when another
round is invoked.

The first successor constructor, `ZeroSupportLocalizedState.exists_next`, applies the complete
support-tail capstone at the all-free root of a zero-support state.  The good-event premise is then
automatic, `zeroSupportSurvivorScale_shell_exact` identifies the child ambient dimension, the
alternating level drops by one, bottom width remains one, support remains empty, and the slot bound
changes from `M` to `3*M`.  A focused harness kernel-checked the dependent state/edge packaging,
the automatic all-free support-tail exclusion, and the exact shell transport; the two capstones
printed only `propext`, `Classical.choice`, and `Quot.sound`.  Direct elaboration of the full
iteration source again reached the preserved dependency-refresh failures beginning at the older
support block.  A refreshed TwoSAT-bridge build and direct source elaboration were stopped after
long silent final elaboration, so no completed target or full build is claimed.  `git diff --check`
passed.  No `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was added.

The precise next frontier is to define the finite dependent tree/chain generated by repeated
`exists_next` choices and prove the transitive semantic lifting equation along its edges.  Only
after that structural recursion is kernel checked should the one-shell contraction be lifted to a
global bad-root count; that counting step must account for branch-dependent `κ` coordinate maps and
fuel choices rather than multiplying unrelated shell ratios.  No P-versus-NP conclusion follows.

### Two dependent localized edges now compose semantically

The first nontrivial recursive path is now explicit.  `ZeroSupportLocalizedTwoStep` retains two
successive edge-labelled steps, with the second restriction living on the first step's dependent
live-coordinate type.  Its `middleAssignment` performs only the definitional transport exposed by
`ZeroSupportLocalizedStep.toState`, and `liftAssignment` composes the two canonical live-assignment
embeddings.

The theorem `ZeroSupportLocalizedTwoStep.eval_eq` proves the transitive equation

```text
eval grandchild z = eval root (lift kappa0 (lift kappa1 z)).
```

Here the displayed inner lift includes the definitional `toState` coordinate transport; no
identification of the two restrictions as restrictions on one ambient type is assumed.
`ZeroSupportLocalizedState.exists_two_step` also packages two actual `exists_next` invocations at
successive geometric scales, using separate fuel bounds and yielding slot envelope `((M*3)*3)`.
Thus the semantic edge data is sufficient for genuine iteration at depth two, not merely for two
unrelated one-round witnesses.

During dependency verification, the preserved finite-profile proof
`twoPairLocalCostLive_weighted_sum` exposed an invalid strict-bound route: `cost <= stars <= 4`
does not imply `cost < 4`.  The proof now uses the already established sharp theorem
`twoPairFlexibleQueryCost_le_three`.  This failed inference is recorded here because weakening the
profile range to five would change the six-fiber convolution audit.

A standalone focused harness, importing the real restriction/cardinality and layered-circuit
definitions, kernel-checked the dependent two-edge package and semantic equation.  Its printed
axioms were exactly `propext`, `Classical.choice`, and `Quot.sound`.  Direct elaboration of the full
iteration source reached the known stale-support dependency block; after correcting the new
`toState` transport, it reported no further type error in the two-edge declarations.  A refreshed
full TwoSAT-bridge elaboration passed the old failure and reached the late file, but the process was
killed with exit 137 before completion, so no target or full build is claimed.  No `sorry`, `admit`,
custom axiom, `unsafe`, or `native_decide` was added.

The precise next frontier is to replace the two-edge special case by a length-indexed dependent
path whose endpoint assignment embedding folds all retained restrictions, and prove its semantic
equation by induction.  Only then can the per-shell support-tail counts be lifted through the full
branch-dependent tree; the counting proof must measure preimages under those composed embeddings
and cannot simply multiply the one-shell contraction factors.  No P-versus-NP conclusion follows.

### Arbitrary finite dependent semantic paths now compose

The two-edge calculation has now been factored through a genuinely length-indexed object.
`LocalizedSemanticPath C length` is inductive: every successor stores a restriction on the current
ambient type, a circuit on that restriction's live-coordinate type, its semantic edge equation,
and a tail whose ambient type is therefore branch dependent.  The zero-length constructor is the
identity path.

The recursive projections `endpointN` and `endpointCircuit` expose the final dependent circuit,
while `liftAssignment` folds every retained `liftLiveAssignment` from the endpoint back to the
root.  `LocalizedSemanticPath.eval_eq` proves by induction that

```text
eval endpointCircuit z = eval rootCircuit (foldedLift z)
```

for every finite length.  Both `ZeroSupportLocalizedStep` and the existing two-step package now
embed into this uniform path type, so the special semantic calculation is no longer the only
available composition interface.

A standalone focused harness importing the real restriction/cardinality and layered-circuit
definitions kernel-checked the arbitrary-length semantic theorem.  Its printed axioms were
exactly `propext`, `Classical.choice`, and `Quot.sound`.  Direct elaboration of the large iteration
source reported no error in the new path declarations before continuing through the preserved
stale-support dependency failures beginning at `gateVariableSupport_negDNF`; no full target or
full build is claimed.  No `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was added.

The precise next frontier is to index this semantic path additionally by the geometric shell,
remaining alternation level, and `M * 3^length` slot envelope, then build it recursively from
`ZeroSupportLocalizedState.exists_next`.  After that stateful generator is kernel checked, the
first genuinely quantitative obligation is a preimage bound for the folded assignment embeddings;
the one-shell contractions still cannot be multiplied without controlling those branch-dependent
fibers.  No P-versus-NP conclusion follows.

### The full geometric state path is now generated recursively

`ZeroSupportGeometricPath d r level M i length S` now carries all three structural recurrence
indices in its type.  Its root is on shell `zeroSupportSurvivorScale d r i`, has `length`
alternation drops remaining, and uses slot envelope `M * 3^i`; every successor is on shell `i+1`
with envelope `M * 3^(i+1)`.  `endpointState` exposes the exact endpoint state on shell
`i+length`, at remaining level `level`, with envelope `M * 3^(i+length)`.

`ZeroSupportLocalizedState.exists_geometric_path` proves that every finite prefix satisfying
`i+length <= d` is inhabited by recursively invoking `exists_next`.  The fuel budget is allowed to
vary by shell and is required only on the actually traversed interval.  The proof therefore makes
no unrecorded uniform-fuel assumption.  `ZeroSupportGeometricPath.toSemanticPath` forgets only the
schedule invariants, and `ZeroSupportGeometricPath.eval_eq` transfers the already proved folded
semantic equation to every generated state path.

Direct elaboration of the large iteration source reported no error in the new declarations.  It
still fails earlier in the preserved stale-support dependency block beginning with the missing
refreshed `gateVariableSupport_negDNF`, so the source elaborator inserts `sorryAx` into later
dependency reports and no target or full build is claimed.  A separate structural harness, with
the one-step constructor supplied as an ordinary theorem parameter rather than an axiom,
kernel-checked the exact geometric recursion, endpoint indices, and semantic fold.  Its three
printed capstones depend exactly on `propext`, `Classical.choice`, and `Quot.sound`.  No `sorry`,
`admit`, custom axiom, `unsafe`, or `native_decide` was added.

The precise next frontier is now quantitative rather than structural: prove that
`liftLiveAssignment` is injective on each retained live cube, lift injectivity through
`LocalizedSemanticPath.liftAssignment`, and turn that into a finite-cardinality/preimage theorem
for the branch-dependent folded embeddings.  That controls assignment fibers along one fixed
generated path; a subsequent theorem must still relate the different path branches before the
per-shell support-tail contractions may be multiplied.  No P-versus-NP conclusion follows.

### Folded live-assignment fibers are exactly controlled on every fixed path

The fixed-branch preimage problem is now closed.  `liftLiveAssignment_injective` reads every local
bit back at `liveCoordEquiv tau i`, so extending a live-cube assignment into its ambient cube loses
no information.  `LocalizedSemanticPath.liftAssignment_injective` composes this fact through the
entire dependent path, even though each successive restriction has a branch-dependent coordinate
type.

The finite consequence is packaged as `liftAssignment_fiber_card_le_one`: for every root Boolean
assignment, the set of endpoint assignments mapped to it by a fixed folded path has cardinality at
most one.  Thus no multiplicity factor is required inside one retained branch.  This is stronger
than a generic finite preimage bound, but it does not compare images belonging to different paths.

A focused harness importing the real restriction/cardinality and layered-circuit definitions
kernel-checked the one-edge injection, dependent induction, and finite fiber theorem.  All three
printed capstones depend exactly on `propext`, `Classical.choice`, and `Quot.sound`.  Direct
elaboration of the full iteration source also reported the same clean axiom sets for the four new
declarations and no error in their source ranges; as before, the preserved stale-support block
beginning at `gateVariableSupport_negDNF` prevents clean module elaboration, so no target or full
build is claimed.  `git diff --check` passed.  No `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was added.

The precise next frontier is cross-branch compatibility: define the finite family of generated
geometric paths at a shell and bound how many distinct path images can contain the same root
assignment (or prove the images disjoint under an adequate retained label).  Only that theorem can
justify composing the one-shell contractions across the branch-dependent tree; fixed-path
injectivity alone does not permit multiplying them.  No P-versus-NP conclusion follows.

### Cross-branch overlap is exactly restriction compatibility, not disjointness

The generic disjoint-image route is now ruled out at the first localized edge.
`exists_liftLiveAssignment_eq_iff_agrees` identifies the image of `liftLiveAssignment tau` exactly
with the total assignments agreeing with `tau`.  Defining `RestrictionsCompatible tau upsilon` to
mean that the two restrictions never fix one coordinate to opposite values,
`restrictionsCompatible_iff_exists_agrees` proves that compatibility is equivalent to a common
total extension.  Combining the two gives the exact criterion

```text
range(liftLiveAssignment tau) intersects range(liftLiveAssignment upsilon)
  iff RestrictionsCompatible tau upsilon.
```

The preserved theorem `exists_distinct_restrictions_with_overlapping_lift_ranges` witnesses the
failure of generic disjointness already on `Fin 2`: one branch fixes coordinate zero to false and
the other fixes coordinate one to false.  They are distinct but retain a common all-false root
assignment.  Thus restriction identity or live-set identity cannot serve as an adequate disjoint
branch label.

Direct source elaboration reported no errors in these new declarations before reaching the
preserved stale-support dependency block beginning at `gateVariableSupport_negDNF`.  A clean full
target or full build is therefore not claimed.  Printed dependencies for the new compatibility
theorem are exactly `propext`; the image characterizations and explicit counterexample use exactly
`propext`, `Classical.choice`, and `Quot.sound`.  No `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was added.

The precise next frontier is to fold the dependent restrictions along
`LocalizedSemanticPath` into one ambient root restriction and prove that the folded assignment
image is exactly its extension cube (up to the canonical live-coordinate equivalence).  The
cross-branch multiplicity problem then becomes a finite compatibility-degree bound for those
composed restrictions, or a stronger retained label that separates compatible branches.  The
one-edge counterexample shows that plain path/restriction distinctness is insufficient.  No
P-versus-NP conclusion follows.

### Dependent path restrictions now fold to one exact ambient cube

The branch-dependent coordinate transports have now been eliminated from the image statement.
`agreeRestriction_liftLiveRestriction_iff` proves that agreement with a lifted local restriction
is exactly ambient agreement together with agreement on the canonical live coordinates.
`LocalizedSemanticPath.rootRestriction` recursively lifts every tail restriction back to the root
cube, with exact live dimension `stars path.rootRestriction = path.endpointN`.

`LocalizedSemanticPath.exists_liftAssignment_eq_iff_agrees` proves that the entire folded
assignment image is precisely the total assignments agreeing with this one root restriction.
Consequently `LocalizedSemanticPath.liftAssignment_ranges_overlap_iff` gives the arbitrary-path
criterion: two dependent path images overlap exactly when their composed root restrictions are
compatible.  This closes the canonical-coordinate bookkeeping gap, but it also confirms that path
length and path identity provide no separation beyond compatibility.

Direct source elaboration reported no errors in the new declarations.  It still encounters the
preserved stale-support dependency failures beginning at `gateVariableSupport_negDNF`, so no clean
target or full build is claimed.  Printed dependencies for all four new capstones are exactly
`propext`, `Classical.choice`, and `Quot.sound`; `git diff --check` passed.  No `sorry`, `admit`,
custom axiom, `unsafe`, or `native_decide` was added.

The precise next frontier is now the actual finite compatibility degree: define the finite family
of composed `rootRestriction`s generated by the geometric path tree and bound, for each total root
assignment, how many of those restrictions it extends.  If that degree is not small enough to
compose the shell contractions, the retained branch label must be strengthened with data that
separates otherwise compatible composed restrictions.  No P-versus-NP conclusion follows.

### The ambient compatibility degree is exactly binomial

The compatibility-degree question now has an exact schedule-independent ceiling.
`restrictionWithFreeSet x S` is the unique restriction whose live set is `S` and whose fixed
coordinates agree with the total assignment `x`.  The equivalence
`agreeingRestrictionEquivFreeSet` therefore identifies all `K`-live restrictions containing `x`
with the `K`-element subsets of the ambient coordinate set.

Consequently `card_agreeing_restrictions_of_stars_eq` proves the exact count

```text
|{rho : Restriction n // stars rho = K and rho agrees with x}| = choose(n,K).
```

The companion theorem `card_distinct_agreeing_restriction_family_le_choose` applies this directly
to every finite injectively indexed family of distinct composed restrictions.  Thus duplicate path
descriptions may first be quotiented by `rootRestriction`, after which the universal cross-branch
multiplicity charge is at most `choose(n,K)`.  The bound is exact for the ambient family, so no
smaller estimate follows from endpoint live dimension and compatibility alone.  In the central
half-shell regime this binomial factor is exponentially large; whether the actually generated
geometric path tree occupies a much sparser subfamily is therefore decisive.

Direct source elaboration reported no errors in the new declarations before reaching the preserved
stale-support dependency failure at `gateVariableSupport_negDNF`.  A focused harness importing the
compiled restriction/cardinality kernel checked the equivalence and both counting theorems.  The
printed dependencies are exactly `propext`, `Classical.choice`, and `Quot.sound`.  No `sorry`,
`admit`, custom axiom, `unsafe`, or `native_decide` was added.

The precise next frontier is to define the finite image of generated geometric paths under
`rootRestriction` and test its per-assignment degree against the product of shell contractions.
The exact ambient theorem shows that a proof using only common endpoint dimension can pay as much
as `choose(n,K)` and is therefore too coarse in the half-shell regime; the next useful invariant
must exploit the canonical tree choices or retain a separating branch label.  No P-versus-NP
conclusion follows.

### The finite admissible path image is explicit; constructor provenance is the missing invariant

`admissibleGeometricRootRestrictions S` is now the finite set of composed root restrictions of
all inhabitants of `ZeroSupportGeometricPath ... S`.  The auxiliary endpoint theorem
`ZeroSupportGeometricPath.semantic_endpointN` proves that every such path lands on the scheduled
shell, and `stars_eq_of_mem_admissibleGeometricRootRestrictions` transfers that exact dimension to
every member of the image.  Filtering this image by one total root assignment gives the proved
bound

```text
card(admissible roots agreeing with x)
  <= choose(S.n, 20 * zeroSupportSurvivorScale d r (i + length)).
```

This closes the literal “finite image” construction, but exposes an important interface boundary.
`ZeroSupportGeometricPath` is a type of every structurally admissible edge sequence.  In contrast,
`exists_geometric_path` only returns `Nonempty` after choosing the all-false branch at each round;
it does not retain a predicate or label saying that a particular path was produced by those
canonical constructor calls.  Therefore the newly defined finite set is honestly named the
*admissible* image, not the generated-constructor image.  Its compatibility theorem necessarily
recovers only the already sharp ambient binomial ceiling.  Any claim that the current interface
defines a sparser generated family would conflate existence with provenance.

A focused harness over the real restriction/cardinality kernel checked the finite existential
image and its agreement-degree theorem; the printed capstone axioms were exactly `propext`,
`Classical.choice`, and `Quot.sound`.  Direct source elaboration, with an increased heartbeat
budget, accepted the new indexed endpoint reduction before the preserved stale TwoSAT support
exports contaminated the dependent state with universe metavariables.  Those pre-existing failures
still begin at the missing refreshed `gateVariableSupport_negDNF` and
`layeredBottomVariableSupport`.  A dependency-refresh build replayed more than 8,000 jobs and then
remained silent in the known expensive final elaboration, so it was stopped and no target or full
build is claimed.  `git diff --check` passed.  No `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was added.

The precise next frontier is to replace the existential-only successor interface by a finite,
provenance-carrying branch generator: define the actual finite choices made by one canonical round,
prove completeness for the desired root assignments, and retain its choice label through
`ZeroSupportGeometricPath`.  Only then is there a meaningful generated-image fiber to compare with
the product of shell contractions.  If that provenance-aware fiber is still binomial in the
half-shell regime, the branch label must be strengthened rather than discarded.  No P-versus-NP
conclusion follows.

### The survivor selector now follows its branch assignment

The first provenance loss occurred before `Nonempty`.  The prior exact-size helper used
`keepFreeExtension`, which fixes every discarded live coordinate to a selector-internal default;
there was therefore no theorem that its survivor restriction agreed with the assignment used to
choose the canonical prefix leaf.  A finite branch generator built directly on that helper would
not have had the required root-assignment completeness property.

`assignmentKeepFreeExtension keep x` now fixes every discarded coordinate to its value in `x`.
Its free set is exactly `keep`, it extends the base whenever `keep` is base-live and `x` extends the
base, and it is itself extended by `x`.  The proved selector
`exists_assignmentExtending_stars_eq_inter_card_le` retains the old exact-size and support-overlap
bounds while adding this assignment-extension certificate.  The zero-overlap survivor theorem and
the localized support-tail round thread the certificate through, and
`ZeroSupportLocalizedState.exists_next_agreeing` exposes it at the state transition; the original
`exists_next : Nonempty ...` remains as a compatibility wrapper.

A focused harness importing the compiled restriction/common-tree kernel checked the complete new
selector and printed exactly `propext`, `Classical.choice`, and `Quot.sound`.  Direct elaboration of
the iteration source accepted the standalone selector declarations before the preserved stale
`gateVariableSupport_negDNF`/`layeredBottomVariableSupport` exports contaminated later declarations.
A dependency refresh replayed more than 8,000 jobs and again stalled silently in expensive final
elaboration, so it was stopped; no target or full build is claimed.  `git diff --check` passed.  No
`sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was added.

The precise next frontier is now a finite one-round generator indexed by total assignments, using
`exists_next_agreeing` (or a fixed classical choice of it), together with a completeness theorem
that every root assignment extends the restriction of its selected successor.  That finite label
must then be threaded dependently through geometric paths and its *distinct root-restriction*
fibers measured.  Assignment agreement repairs provenance correctness but does not itself improve
the potentially binomial cross-branch multiplicity.  No P-versus-NP conclusion follows.

### The one-round branch generator is finite and root-assignment complete

`ZeroSupportLocalizedState.selectedNextStep` now fixes one successor for every total Boolean root
assignment by applying classical choice to `exists_next_agreeing`.  The assignment itself is the
finite provenance label.  `generatedNextLabels` retains the entire Boolean assignment cube rather
than prematurely quotienting labels that may select the same restriction.

The capstone `generatedNextLabels_complete` proves that every root assignment both belongs to the
finite label generator and extends its selected successor restriction.  The companion exact count

```text
card(generatedNextLabels) = 2^S.n
```

is only the honest assignment-domain size; no sparsity is inferred from it.  This closes the
one-round existential-to-generator interface without pretending that different assignments yield
different restrictions or that compatible branch cubes are disjoint.  An attempted immediate
`Finset.image` of selected restrictions was rejected in direct elaboration because the preserved
stale support exports currently leave the dependent step projection universe-metavariable
contaminated; retaining labels is also the correct provenance interface, so that failed quotient
route is not hidden.

A focused kernel harness for the generic choice selector, completeness proof, and exact finite
label count passed; the printed capstone axioms were exactly `propext`, `Classical.choice`, and
`Quot.sound` (the selector agreement theorem itself used only `Classical.choice`).  Direct source
elaboration reports no new error in the finite-label declarations, but still fails earlier at the
preserved stale `gateVariableSupport_negDNF`/`layeredBottomVariableSupport` dependency boundary;
downstream declarations therefore inherit `sorryAx` from elaborator recovery, and no target or
full build is claimed.  `git diff --check` passed.  No `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was added.

The precise next frontier is to refresh those stale dependency exports, then define an
assignment-threaded dependent geometric path: at each selected successor, restrict the same root
assignment to the canonical live coordinates, use that local assignment as the next label, and
prove that the resulting composed root restriction is extended by the original root assignment.
Its finite distinct-root image can then be measured against the shell contraction; the present
one-round count alone does not improve the binomial compatibility charge.  No P-versus-NP
conclusion follows.

### The stale-export boundary is exact; the monolithic refresh is now the blocker

A direct compiled-interface probe of
`ComputationalDepthMultiSwitchingTwoSATBridge` located the stale boundary exactly.  The current
`.olean` exports `gateVariableSupport` and
`canonicalDT_queriedVars_subset_gateVariableSupport`, but it does not export
`gateVariableSupport_negDNF`, `layeredBottomVariableSupport`, or
`layeredBottomVariableSupport_collapseRound_subset`.  Thus the first downstream unknown identifier
is not an accidental namespace or import error: the compiled artifact ends before the refreshed
support layer used by quantitative iteration.

Direct source elaboration passed the refreshed support declarations and continued beyond line
7,600 with warnings only.  An actual targeted `lake build` replayed all 8,485 prerequisites and
entered the final bridge job, but that last monolithic elaboration produced no further output for
twelve minutes.  It was stopped without writing a replacement artifact, so no target or full build
is claimed.  A short-lived export-probe file was removed after use; no proof declarations were
added by this audit.

This rules out a small import shim as an honest repair: quantitative iteration consumes many
declarations later than the stale boundary, so restating only the first missing theorem would
merely move the unknown identifier downstream.  The precise next frontier is to split the bridge
at a dependency-safe boundary before the expensive exhaustive padded-two-pair proofs, compile the
support/survivor-round prefix as its own module, and import that prefix from quantitative
iteration.  Only after that artifact is kernel-checked should the assignment-threaded geometric
path be added.  The failed long-refresh route is retained here rather than reported as a build
success.  No P-versus-NP conclusion follows.

### The support/survivor prefix is now an independent kernel-checked module

`ComputationalDepthMultiSwitchingSupportSurvivor.lean` now contains the contiguous support-sensitive
layer from `clauseVariableSupport` through
`actualMargin_normalizedSurvivorRound_exactSubcube`.  The monolithic 2-SAT bridge imports this
module for its later developments, while quantitative iteration imports the prefix directly and no
longer depends on the stale `ComputationalDepthMultiSwitchingTwoSATBridge.olean`.

The new target built successfully: 8,349 jobs, with its final module completing in 6.6 seconds.
Its printed survivor-round capstones depend exactly on `propext`, `Classical.choice`, and
`Quot.sound`.  This independently kernel-checks the refreshed support definitions, collapse-round
support monotonicity, hypergeometric tail estimates, and normalized survivor interfaces that were
previously trapped beyond the stale export boundary.

Building quantitative iteration against the new artifact now reaches that file's own source and
exposes a genuine downstream defect rather than an unknown identifier.  The unused implicit `s`
in `actualMargin_normalizedSurvivorRound_localized` was removed, closing one inference failure.
The remaining build error is the dependent eliminator proof
`ZeroSupportGeometricPath.semantic_endpointN_eq_endpointState_n`: its current induction expands to
an unsolved dependent `casesOn` goal.  Direct `cases`/recursive simplification and induction on the
length index were also tested; one times out during weak-head normalization and the other does not
make the two tactic-defined projections definitionally equal.  Those failed routes are preserved
here; no quantitative-iteration or full-build success is claimed.

The precise next frontier is to give `toSemanticPath` and `endpointState` explicit constructor
equation lemmas (or refactor them to equation-style recursive definitions), then prove the endpoint
dimension theorem by rewriting only those equations.  Once the quantitative target kernel-checks
without `sorryAx`, proceed to the assignment-threaded geometric path and measure its distinct
composed-root fibers.  No P-versus-NP conclusion follows.

### The quantitative iteration artifact is refreshed and the endpoint schedule is kernel-checked

`ZeroSupportGeometricPath.toSemanticPath` and `endpointState` are now equation-style recursive
definitions.  More importantly, `toSemanticPath_endpointN_cons` isolates the only endpoint
computation needed by the dependent induction: one geometric successor has the same semantic
endpoint dimension as its tail.  The new theorem `toSemanticPath_endpointN_scheduled` then proves
directly, from the ambient-shell certificate stored in each state, that

```text
path.toSemanticPath.endpointN
  = 20 * zeroSupportSurvivorScale d r (i + length).
```

`semantic_endpointN_eq_endpointState_n` is now a short transitivity argument between that schedule
equation and `path.endpointState.ambient_eq`.  This avoids normalizing the proof transports inside
the dependent endpoint state.  A broader `simp only` induction over both recursive definitions was
also tested after the equation-style refactor, but still timed out in weak-head normalization; that
failed route is retained here because it confirms that the useful interface is the scalar semantic
endpoint equation, not definitional equality of transported state terms.

The quantitative-iteration target built successfully: 8,451 jobs, with the final module completing
in 34 seconds.  Printed dependencies for the one-step equation, scheduled endpoint theorem,
semantic/state endpoint equality, semantic endpoint capstone, admissible-image shell theorem, and
agreement-degree theorem contain only `propext`, `Classical.choice`, and `Quot.sound`; the previous
`sorryAx` contamination is gone.  No `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide`
was added.

The precise next frontier is the assignment-threaded dependent geometric path: at each selected
successor, derive the local live-cube assignment from the same original root assignment, prove the
composed `rootRestriction` remains extended by that root assignment, and define the finite image of
these provenance-carrying generated paths.  Its distinct-root fiber must then be compared with the
product of shell contractions; endpoint schedule bookkeeping and stale support exports are no
longer blockers.  No P-versus-NP conclusion follows.

### Assignment provenance now composes through every geometric round

`liftLiveAssignment_restrict_eq_of_agrees` records the canonical one-edge retraction: restricting
an agreeing ambient assignment to the current live coordinates and lifting it again returns the
same assignment.  The new recursive theorem
`ZeroSupportLocalizedState.exists_geometric_path_lifting_assignment` uses that retraction at every
round.  It selects the first successor from the root assignment, passes the root assignment
restricted to that successor's live coordinates into the recursive call, and returns an endpoint
assignment whose full dependent lift is exactly the original root assignment.

`selectedGeometricPath` fixes this witness as an assignment-indexed path, and
`selectedGeometricPath_rootRestriction_agrees` proves the requested end-to-end provenance
invariant: the original assignment extends the path's composed root restriction.  The only
arithmetic transport in the recursion is the slot identity
`(M * 3^i) * 3 = M * 3^(i+1)`.  Casting the whole successor structure across that equality was
tested first, but projection equality became a stuck dependent-elimination goal.  The successful
route rebuilds the successor record with the same restriction and circuit and transports only its
`slots_le` proof; the failed broad cast is retained here because it is a useful warning for later
dependent image definitions.

The quantitative-iteration target kernel-checks the assignment-threaded path construction.  The
precise next frontier is to take the finite image of
`x ↦ (selectedGeometricPath ... x).toSemanticPath.rootRestriction`, prove that every image
element lies on the scheduled survivor shell, and measure the fibers of this *generated* map.
The existing admissible-image binomial bound counts all structurally possible paths and therefore
does not yet show whether assignment provenance absorbs the product of half-shell contractions.
No P-versus-NP conclusion follows.

### The generated composed-root image has endpoint-sized fibers

The assignment-selected path map is now packaged as the finite image
`generatedGeometricRootRestrictions`.  Every member has exactly the scheduled final live
dimension

```text
20 * zeroSupportSurvivorScale d r (i + length).
```

The complementary assignment-side count is also exact: a restriction `rho` is extended by
exactly `2^(stars rho)` total assignments.  Since assignment provenance proves that every input in
one selected-map fiber extends that fiber's root restriction,
`card_generatedGeometricRootFiber_le` bounds each generated fiber by the final endpoint cube.
Fiberwise counting then gives the capstone

```text
2^S.n <= 2^(20 * zeroSupportSurvivorScale d r (i + length))
           * card(generatedGeometricRootRestrictions ...).
```

This resolves the first distinct-root audit decisively: assignment provenance does not collapse
the scheduled root image below the ordinary endpoint-cube partition scale.  In fact, it forces at
least `2^(S.n - endpointN)` distinct composed roots whenever that subtraction is interpreted via
the displayed product inequality.  Thus provenance supplies correctness and an exact fiber
ceiling, but it cannot by itself absorb an additional product of half-shell switching charges.

The quantitative-iteration target built successfully: 8,451 jobs, with the final module completing
in 35 seconds.  The full `lake build` also passed: 8,068 jobs.  Printed dependencies for the exact
assignment count, generated shell theorem, fiber containment, fiber ceiling, and product lower
bound are exactly `propext`, `Classical.choice`, and `Quot.sound`.  An initial proof wrote a
`Finset.filter` with a propositional predicate directly in theorem types; Lean correctly rejected
the missing `DecidablePred` before entering the local `classical` proof.  The preserved repair is
the explicit noncomputable finite set `assignmentsAgreeingRestriction`, which keeps classical
decidability inside the definition.  `git diff --check` passed.  No `sorry`, `admit`, custom axiom,
`unsafe`, or `native_decide` was added.

The precise next frontier is no longer basic root-fiber counting.  It is to define a round-by-round
charged label on the generated roots and prove whether the verified half-shell bad-set savings can
be charged injectively (or with controlled multiplicity) across *distinct* composed roots.  The
new lower bound shows that any successful argument must exploit circuit/bad-event structure, not
merely quotient assignment-selected paths by their final root restriction.  No P-versus-NP
conclusion follows.

### The zero-support geometric iterator has no bad event left to charge

The proposed next charge was audited against the actual recursive state rather than added as a
formal label without a source.  Two new kernel-checked theorems make the result exact.  For every
`ZeroSupportLocalizedState`, every shell size `K`, and every trunk depth, the circuit-owned set

```text
liveLayeredBottomSupportTail S.circuit K trunkDepth
```

is empty.  If `K <= fuel`, the normalized-family switching event

```text
commonShallowBad (normalizedLayeredBottomFamily S.circuit)
  fuel K trunkDepth residualDepth
```

is empty as well.  The first statement follows from the state's invariant that the bottom-variable
support has cardinality zero; the second composes the existing common-shallow-bad-to-support-tail
reduction with that exact emptiness theorem.

This changes the interpretation of the generated-root fiber lower bound.  The geometric iterator
begins only *after* the support-tail selection has eliminated bottom support, and each later round
runs from an all-free local root whose bad event is vacuous.  Therefore there is no nontrivial
round-by-round support-tail or normalized common-shallow charge available on the generated roots.
The factor-two shell handoff inside this iterator is survivor partitioning, not another bad-set
probability saving.  Attaching a nominal bad-event label here would erase this distinction and
cannot provide the missing contraction.

The precise next frontier is to move the charging boundary earlier: retain provenance for the
initial nonzero-support shell selection and map its genuinely bad/good bucket structure into the
zero-support successor roots with controlled multiplicity.  Equivalently, strengthen the recursive
state to carry the pre-collapse circuit/root event that produced it.  Only that bridge can test
whether the verified switching saving survives quotienting by distinct composed roots; the current
zero-support state has intentionally forgotten the only nonempty event that could supply it.  The
failed route of charging bad events internal to the existing geometric iterator is preserved by
the two emptiness theorems.  No P-versus-NP conclusion follows.

### The initial good-event boundary now retains its zero-support successor

`InitialSupportTailSuccessor` packages the previously separated sides of the charging boundary.
It retains the initial `40R` root, proof that the root is outside the genuine support-tail bad
event, the assignment selecting its canonical prefix leaf, the resulting `20R` restriction, the
localized collapsed circuit, and all zero-support state invariants.  Crucially, `root_extends`
composes the root-to-prefix and prefix-to-survivor extension proofs, so the child is now connected
directly to the event-bearing root rather than only to an unnamed intermediate leaf.

`exists_initialSupportTailSuccessor` constructs this package for every good root and every
assignment extending it.  `InitialSupportTailSuccessor.toState` then forgets exactly the initial
event provenance and yields the state consumed by the existing geometric iterator.  This proves
that strengthening the recursive state is not necessary merely to cross the boundary: the old
iterator can be entered through an explicit provenance wrapper without changing its internals.

The quantitative-iteration target kernel-checks this bridge.  The precise next frontier is now a
finite image/fiber count for the map from `(good initial root, extending assignment)` to the
successor restriction (and then to its composed geometric endpoint).  The relevant multiplicity
must use `root_extends` and the exact `40R -> 20R` shell sizes; counting assignments alone will
repeat the already-proved endpoint-cube partition and cannot recover the switching saving.  The
zero-support internal charging route remains ruled out by the preceding emptiness theorems.  No
P-versus-NP conclusion follows.

### The exact initial `40R -> 20R` selected-successor fiber is bounded

`restrictionCoarseningShellFiber kappa` isolates the earlier shell roots that can extend to one
fixed successor.  The live-set difference

```text
freeVars sigma \ freeVars kappa
```

injectively labels this fiber: once the predecessor live set is known, every other Boolean value
is forced by `kappa`.  Consequently a `K`-star coarsening fiber has size at most

```text
choose (n - stars kappa) (K - stars kappa).
```

At the actual initial boundary this becomes `choose (n-20R,20R)`.  The proof uses the exact
extension direction; it introduces no spurious Boolean factor on root restrictions.

The genuine finite domain is now also formalized as `InitialGoodRootAssignmentPair`: a root on the
`40R` shell, outside the nonempty support-tail bad event, together with an extending total
assignment.  `initialSupportTailSuccessorImage` maps these pairs to the selected successor supplied
by `exists_initialSupportTailSuccessor`.  Each map fiber injects into the product of the root
coarsening fiber and the assignments extending the fixed successor.  Since a `20R` successor has
exactly `2^(20R)` extending assignments, the verified numerical ceiling is

```text
fiber(kappa) <= choose (n-20R,20R) * 2^(20R).
```

This cleanly separates the combinatorial shell multiplicity from the endpoint assignment cube.
It also confirms that provenance alone retains an unavoidable `2^(20R)` factor; any switching
saving must enter through the number of good initial roots, not through further quotienting of
assignments over one successor.

The quantitative-iteration target built successfully (8,451 jobs), and the full `lake build`
passed (8,068 jobs).  Printed dependencies for the coarsening injection, generic and specialized
root-fiber bounds, product-fiber bound, and numerical selected-successor ceiling are exactly
`propext`, `Classical.choice`, and `Quot.sound`.  No `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was added.  The first product-membership proof attempted to rewrite through a
let-bound finite product; Lean rejected that non-definitional rewrite.  The retained proof applies
the product-membership equivalence explicitly, avoiding any opacity assumption.

The precise next frontier is to compute the cardinality of `InitialGoodRootAssignmentPair` as the
number of good `40R` roots times `2^(40R)`, apply the new fiber ceiling to obtain an image lower
bound, and compare that inequality with the already verified support-tail bad-set contraction.
Only then should the selected successor be composed with the zero-support geometric endpoint;
that composition may add endpoint collisions but cannot improve the initial successor bound by
assignment counting alone.  No P-versus-NP conclusion follows.

### The initial good-domain count and successor-image lower bound now compose

The finite charging boundary is now counted exactly.  `initialGoodRoots` names the good roots on
the `40R` shell, and `initialGoodRootAssignmentPairs` names the underlying root/assignment pairs.
Fiberwise counting over the root projection proves

```text
card(initialGoodRootAssignmentPairs)
  = card(initialGoodRoots) * 2^(40R).
```

The same equality is proved for the finite subtype domain consumed by the selected-successor map.
Combining it with the previously verified uniform fiber ceiling gives

```text
card(good roots) * 2^(40R)
  <= (choose(n-20R,20R) * 2^(20R)) * card(selected 20R successors).
```

The support-tail contraction is now compared to this count without an informal probability
translation.  Good and bad roots are proved to partition the complete `40R` shell exactly.  For
`R > 0`, the existing `2^(20R)`-scaled bad-tail estimate implies that at least half the shell is
good.  Consequently the combined kernel-checked inequality is

```text
card(40R shell) * 2^(40R)
  <= 2 * (choose(n-20R,20R) * 2^(20R))
       * card(selected 20R successors).
```

This is the first direct distinct-successor lower bound in which the genuine initial switching
event, its good population, the exact assignment cube, and the exact root-coarsening collision
cap all occur in one statement.  It also sharpens the interpretation of the switching estimate:
at this boundary its exponential bad-set saving reduces to a factor-two loss after restricting to
good roots; the remaining quantitative loss is the explicit coarsening binomial and successor
assignment cube, not an untracked bad-event charge.

The target module compiled successfully.  The new partition, half-shell, exact-domain, image, and
combined capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.
`git diff --check` passed, and no `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was
added.

The precise next frontier is to compose each selected `20R` successor with the existing
zero-support geometric endpoint and prove a controlled fiber bound for that second map.  The
initial inequality shows exactly how much additional endpoint collision can be tolerated; a
successful iteration argument must now bound those collisions using geometric-state structure,
since assignment provenance has already been fully spent at the initial boundary.  No P-versus-NP
conclusion follows.

### The initial event now composes through every zero-support geometric round

The selected initial successor and the assignment-generated geometric iterator are now joined by
`selectedInitialGeometricEndpointRestriction`.  Starting with scale

```text
R₀ = zeroSupportSurvivorScale d r 0 = 2^d r,
```

it lifts the geometric path's composed local restriction back through the selected initial
`20R₀` successor to one restriction on the original ambient `Fin n` cube.  Three provenance
facts kernel-check across this dependent-coordinate boundary:

- the final ambient restriction has exactly `20r` live coordinates;
- the original total assignment extends the final restriction;
- the original `40R₀` shell root coarsens the final restriction.

These facts give a direct full-path fiber bound.  For a fixed final endpoint `rho` with
`stars rho = 20r`, every preimage injects into the product of its original root and assignment,
and that product lies in

```text
restrictionCoarseningShellFiber (K = 40R₀) rho
  × assignmentsAgreeingRestriction rho.
```

Consequently

```text
fiber(rho)
  ≤ choose(n - 20r, 40R₀ - 20r) * 2^(20r).
```

This is sharper and structurally cleaner than multiplying the initial successor cap by one cap
per geometric round: all intermediate live-coordinate collisions disappear from the estimate.
Combining the exact good-domain count with this ceiling proves

```text
#goodRoots * 2^(40R₀)
  ≤ [choose(n - 20r, 40R₀ - 20r) * 2^(20r)] * #finalEndpoints.
```

For `r > 0`, the genuine support-tail contraction again replaces `#goodRoots` by half of the
complete initial shell, yielding the capstone

```text
#shell(40R₀) * 2^(40R₀)
  ≤ 2 * [choose(n - 20r, 40R₀ - 20r) * 2^(20r)] * #finalEndpoints.
```

The quantitative-iteration target passed.  Printed dependencies for the endpoint shell,
assignment and root provenance, direct product and numerical fiber bounds, and both image
inequalities are exactly `propext`, `Classical.choice`, and `Quot.sound`.  No `sorry`, `admit`,
custom axiom, `unsafe`, or `native_decide` was added, and `git diff --check` passed.

The precise next frontier is arithmetic and no longer dependent-type composition: normalize this
endpoint lower bound against the exact cardinalities of the `40R₀` initial shell and the `20r`
terminal shell.  This will determine whether the remaining coarsening binomial leaves a large
enough terminal population for the intended depth-reduction cashout, or whether a stronger
cross-root structural restriction is required.  No P-versus-NP conclusion follows.

### Exact shell normalization exposes the remaining density loss

The full-path endpoint inequality is now normalized against both exact restriction shells.  A
generic cancellation theorem starts from a `K -> L` image estimate of the verified form

```text
#Shell(K) * 2^K <= 2 * choose(n-L,K-L) * 2^L * #Image
```

under `L <= K <= n`.  Expanding `#Shell(t) = choose(n,t) * 2^(n-t)` and applying

```text
choose(n,L) * choose(n-L,K-L) = choose(n,K) * choose(K,L)
```

cancels every ambient-`n` binomial and every Boolean assignment factor, leaving the exact
normalized conclusion

```text
#Shell(L) <= 2 * choose(K,L) * #Image.
```

Specializing to the composed geometric schedule gives

```text
#Shell(20r)
  <= 2 * choose(40 * 2^d * r, 20r) * #finalEndpoints.
```

Thus the current construction guarantees terminal-shell density only
`1 / (2 * choose(40 * 2^d * r,20r))`.  The coarsening binomial does not cancel against the shell
ratio; it is exactly the surviving loss.  In particular this is not a constant-density terminal
population as either `r` or `d` grows, so the present count alone is insufficient for any cashout
that requires a uniformly positive fraction of the terminal shell.

The quantitative-iteration target compiled successfully, and the full `lake build` passed (8,068
jobs).  Both new capstones print exactly `propext`, `Classical.choice`, and `Quot.sound` as
dependencies.  `git diff --check` passed, and no `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was added.

The precise next frontier is now structural rather than arithmetic: determine the weakest terminal
density actually consumed by the depth-reduction cashout.  If it requires constant or merely
singly-exponential-in-`r` density independent of `d`, the direct root-coarsening fiber is too coarse
and must be refined using cross-root provenance (for example, a bounded family of admissible freed
coordinate sets).  If the cashout tolerates the displayed reciprocal binomial, compose that exact
threshold directly.  No P-versus-NP conclusion follows.

### The parity endpoint needs existence, not terminal-shell density

The first downstream threshold audit now distinguishes two possible cashouts.  Every member of the
selected full-path image is proved to have exactly `20r` live coordinates.  More importantly, for
`r > 0` and whenever the initial `40·2^d·r` shell fits the ambient cube, the normalized endpoint
inequality proves constructively at the finite-set boundary that this image is nonempty:

```text
∃ rho ∈ finalEndpoints, stars rho = 20r.
```

The proof uses positivity of the exact `20r` shell and the already verified inequality

```text
#Shell(20r) ≤ 2 · choose(40·2^d·r,20r) · #finalEndpoints.
```

Thus the reciprocal binomial loss does **not** obstruct a parity-style endpoint theorem that only
needs one surviving subcube.  It remains an obstruction for an enumerative or SAT-algorithm
cashout that needs a uniformly large terminal population.  This milestone deliberately does not
claim the parity contradiction itself: the selected endpoint restriction must still be packaged
together with its terminal localized circuit, composed evaluation equivalence, and the strict
terminal shallowness inequality consumed by `iterated_not_parity_tight`.

The precise next frontier is to expose that semantic endpoint package from
`selectedInitialGeometricEndpointRestriction` (or strengthen the selected path API to return it),
then bridge its final bottom circuit to `iterated_not_parity_tight`.  In parallel, any SAT-speedup
route must still refine the cross-root fiber or explicitly tolerate the reciprocal binomial.  No
P-versus-NP conclusion follows.

### The selected terminal circuit and its composed semantics are now exposed

`selectedInitialGeometricPath` retains the complete provenance-carrying path chosen after the
genuine initial support-tail successor.  Unlike the earlier restriction-only endpoint API, its
type exposes the terminal localized circuit, the dependent live-coordinate embedding, and the
terminal structural state.  The new theorem `selectedInitialGeometricPath_eval_eq` proves

```text
eval terminalCircuit z
  = eval originalCircuit
      (liftInitialRestriction (liftGeometricPath z)).
```

Thus semantic composition is no longer missing: every edge from the original ambient circuit to
the final localized circuit is present in one kernel-checked equation.  The target build passes,
and the capstone uses only the standard logical dependencies already present in this development.

This audit also sharpens the parity interface gap.  The terminal circuit is a `Layered` circuit on
the relabelled `Fin (20r)` live cube, while `iterated_not_parity_tight` requires a sequence of
circuits all living on the original `Fin n` cube and concludes parity disagreement there.  A direct
application is therefore not well typed.  Moreover, ambient parity restricted to a subcube equals
live-coordinate parity only up to the XOR of the fixed ambient bits, so the bridge must carry that
phase (or use a parity/complement-symmetric terminal contradiction).  Strict terminal shallowness
is still also required; `width_one` and terminal `AltO` alone do not supply the strict
`canonicalDT.depth < stars` premise.

The precise next frontier is to prove a localization-aware parity cashout over a dependent semantic
path: first formalize the fixed-bit parity phase under `liftLiveAssignment`, then combine it with a
strict shallow bound for the terminal localized bottom gate.  Retrofitting the localized path into
the same-ambient `iterated_not_parity_tight` API would require an unnecessary circuit transport and
is not presently justified.  The SAT-density obstruction remains unchanged.  No P-versus-NP
conclusion follows.

### The fixed-bit parity phase and localized cashout are now formalized

The dependent-coordinate parity obstruction is resolved directly on the live cube.  The new
definitions `fixedTrueCount` and `fixedParityPhase` record the number and parity of ambient
coordinates fixed to `true`.  The counting theorem

```text
trueCount (liftLiveAssignment tau x)
  = trueCount x + fixedTrueCount tau
```

is proved by partitioning the ambient true coordinates into live and fixed parts and using the
canonical live-coordinate equivalence.  Consequently `parity_liftLiveAssignment` kernel-checks
the exact phase law

```text
parity (liftLiveAssignment tau x)
  = xor (parity x) (fixedParityPhase tau).
```

The phase is harmless for the terminal lower bound: `DTree.shallow_dtree_not_parity_xor` proves
that every decision tree of depth strictly below the live dimension disagrees with parity xor an
arbitrary fixed Boolean phase.  Thus transporting the terminal localized circuit back to the
original `Fin n` cube is unnecessary, and the parity side of a localization-aware cashout no
longer has an interface gap.

The remaining parity obstruction is now purely structural: expose the terminal localized bottom
DNF (or an evaluation-equivalent decision tree) and prove its canonical decision-tree depth is
strictly less than the terminal dimension `20r`.  The existing `width_one` and terminal `AltO`
facts do not by themselves establish that strict inequality.  The reciprocal-binomial density
loss remains relevant only to the SAT/enumerative route.  No P-versus-NP conclusion follows.

### Zero support makes the terminal DNF a canonical leaf

The terminal structural inequality is now proved, using the invariant that was stronger than the
previous frontier assessment recorded.  The reusable theorem
`canonicalDT_depth_eq_zero_of_gateVariableSupport_card_eq_zero` shows that a DNF gate with empty
variable support has canonical depth exactly zero for every restriction and every fuel budget.
Indeed every clause then has an empty literal list, so the DNF either contains a satisfied empty
clause or has no active clause.

At remaining level zero, `ZeroSupportLocalizedState.exists_terminalDnf_depth_zero` combines
`AltO 2` with the already-threaded `support_zero` field and exposes the state circuit as
`Layered.dnf D`, with

```text
(canonicalDT D fuel sigma).depth = 0
```

uniformly in `fuel` and `sigma`.  The geometric-path specialization
`ZeroSupportGeometricPath.exists_endpointDnf_depth_lt` therefore proves, whenever the scheduled
endpoint scale is positive,

```text
(canonicalDT D fuel sigma).depth < endpointState.n.
```

For a full `0 -> d` schedule this endpoint dimension is `20r`.  Thus width one is not doing the
terminal work: zero bottom support closes the strict shallowness bound outright.

The focused support-survivor and quantitative-iteration modules elaborate successfully.  Printed
dependencies for the new capstones are limited to the standard logical axioms already accepted in
this development.  No `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was added.

The precise next frontier is the last dependent presentation bridge: identify (or transport along
`semantic_endpointN_eq_endpointState_n`) the DNF stored in `path.endpointState.circuit` with
`path.toSemanticPath.endpointCircuit`, whose evaluation is the one already composed back to the
original circuit.  Then combine canonical-DT evaluation, the fixed parity phase, and
`shallow_dtree_not_parity_xor` in one localization-aware contradiction theorem.  The SAT-density
obstruction remains unchanged.  No P-versus-NP conclusion follows.

### The localization-aware parity contradiction now closes end to end

The dependent presentation bridge is discharged without casting the whole endpoint-state record.
That cast route was tested and failed at the successor case because `endpointState` itself is
transported across arithmetic equalities, so projecting its circuit leaves nested dependent casts.
The cleaner theorem `exists_semantic_endpointDnf_depth_lt` instead recurses directly through the
retained geometric path.  It produces the terminal DNF definitionally on
`path.toSemanticPath.endpointN`, exactly the cube consumed by the composed evaluation theorem.

The first attempted cashout also exposed and preserves a genuine correction to the earlier
frontier: the parity phase is not contributed only by the initial successor.  Every dependent
localized edge fixes coordinates and contributes its own phase.  `LocalizedSemanticPath.parityPhase`
now XOR-accumulates those phases, and `parity_liftAssignment` proves

```text
parity (path.liftAssignment z) = parity z xor path.parityPhase.
```

With that invariant, `exists_semantic_endpoint_disagrees_parity_xor` combines the semantic DNF,
canonical-tree evaluation at the all-free endpoint restriction, exact depth-zero shallowness, and
the parity-XOR lower bound.  Finally
`selectedInitialGeometricPath_exists_disagrees_parity` proves that for every genuine selected
initial good root/assignment pair, positive `r`, the stated initial and per-round fuel bounds,
sparse initial bottom support, and `AltO (d+3)`, there is an ambient assignment `x` with

```text
Layered.eval C x != parity x.
```

The explicit good-pair parameter is also eliminated.  Membership in
`initialGeometricEndpointImage` definitionally exposes a preimage in the genuine initial good-pair
domain, so `zeroSupportGeometric_exists_disagrees_parity` composes endpoint existence with the
localized cashout.  Under positive `r`, initial shell fit, initial and per-round fuel bounds, sparse
bottom support, and `AltO (d+3)`, it concludes

```text
∃ x, Layered.eval C x != parity x.
```

This is an end-to-end theorem for the stated zero-support geometric regime, but it is not a general
ACC0 lower bound and does not establish P versus NP.  In particular, the next audit must determine
whether the simultaneous hypotheses

```text
20 * (2 * zeroSupportSurvivorScale d r 0) <= n
16 * card(layeredBottomVariableSupport C) <= n
```

and the full fuel schedule cover the intended nontrivial circuit family after preprocessing, rather
than only circuits whose bottom support is already unusually sparse.  The reciprocal-binomial loss
continues to obstruct the separate SAT/enumerative route.

The precise next frontier is therefore hypothesis applicability: specialize the new capstone to the
intended circuit-size/depth parameterization and audit whether sparse bottom support is obtainable
without changing the computed function or exhausting the ambient shell.  If it is not, the parity
route returns to the initial support-tail step and needs a mechanism that reaches zero support from
dense bottom support.  Separately, the SAT route still needs a stronger density/fiber argument.

### Sparse initial support is already a direct parity obstruction

The hypothesis-applicability audit closes decisively for the current parity route.  The new
semantic-support theorem `Layered.eval_eq_of_agree_on_bottomSupport` proves that a layered circuit's
value is determined entirely by `layeredBottomVariableSupport C`: two assignments agreeing on that
set have identical circuit evaluations, regardless of the circuit's depth, width, or gate count.

Consequently `exists_disagrees_parity_of_bottomSupport_card_lt` proves that if the bottom support
omits one ambient coordinate, flipping that coordinate leaves the circuit fixed but flips parity.
The capstone premise has the immediate specialization

```text
0 < n
16 * card(layeredBottomVariableSupport C) <= n
------------------------------------------------------
exists x, Layered.eval C x != parity x.
```

This is formalized as `sparseSupport16_exists_disagrees_parity`, without any switching, shell,
fuel, alternation-depth, or survivor hypothesis.  Therefore the existing geometric capstone is
correct but does not yet reach a nontrivial parity-computing family: on every positive-dimensional
cube, its sparse initial support premise already excludes exact parity before iteration begins.
Semantics-preserving preprocessing cannot turn a parity circuit into this sparse syntactic regime,
because the resulting function would become blind to every omitted coordinate.

The precise next frontier is now narrower: replace the initial sparse-support tail with a dense-
support mechanism.  It must reduce *live* support after restriction while allowing the original
bottom support to cover all `n` variables, and it must preserve enough survivor mass to enter the
verified zero-support geometric schedule.  A useful next audit is the exact hypergeometric tail for
the number of support coordinates left live when the initial support is full; the current
zero-overlap event is impossible there.  The separate SAT-density/fiber obstruction is unchanged.
No P-versus-NP conclusion follows.

### Full initial support makes the hypergeometric tail deterministic

The proposed dense-support audit is now exact.  In
`ComputationalDepthMultiSwitchingSupportSurvivor.lean`,
`live_bottomSupport_card_eq_stars_of_eq_univ` proves that when

```text
layeredBottomVariableSupport C = univ,
```

every restriction has live support overlap exactly `stars sigma`.  Therefore
`liveLayeredBottomSupportTail_eq_shell_of_full_support` identifies the complete tail, for
`trunkDepth < K`, with the whole `K`-star shell:

```text
liveLayeredBottomSupportTail C K trunkDepth
  = { sigma | stars sigma = K }.
```

The companion cardinality theorem specializes the already proved hypergeometric formula to

```text
#tail = choose(n,K) * 2^(n-K).
```

Thus the full-support distribution is a point mass at overlap `K`, not a tail with a useful
small-probability region.  At the geometric parameters `K = 20R`, `trunkDepth = 10R`, and `R > 0`,
`fullSupport_halfShell_mem_liveLayeredBottomSupportTail` proves that every shell root lies in the
tail.  The current initial successor needs a root outside this tail, so its good-root domain is
empty in the full-support case.  This is stronger than merely observing that zero overlap is
impossible.

The precise next frontier is to replace the initial zero-overlap/support-tail successor, not to
sharpen its probability estimate.  Any replacement must permit positive (indeed full, for a
localized parity computation) live support and obtain terminal shallowness from decision-tree
structure rather than from support becoming zero.  The next useful formal audit is a
localization-aware necessity theorem: every circuit equivalent on a positive-dimensional live
cube to parity XOR a fixed phase has full live bottom support.  That will determine exactly which
support-reduction invariants are incompatible with semantic preservation before designing the
dense-support round.  The separate SAT-density/fiber obstruction is unchanged.  No P-versus-NP
conclusion follows.

### Localized parity forces full live bottom support

The localization-aware necessity theorem is now proved directly in the support-survivor module.
`Layered.bottomSupport_eq_univ_of_eval_eq_parity_xor` states that for any localized dimension `m`,
fixed Boolean phase `b`, and layered circuit `C : Layered m`,

```text
(forall x, Layered.eval C x = parity x xor b)
------------------------------------------------
layeredBottomVariableSupport C = univ.
```

The proof flips a coordinate omitted from the bottom support.  Semantic completeness of bottom
support makes the circuit invariant under that flip, while `parity_flip` changes parity; XOR by a
fixed phase preserves the contradiction.  The companion theorem
`Layered.bottomSupport_card_eq_of_eval_eq_parity_xor` records the exact cardinal consequence
`card(bottomSupport C) = m`.  Applied after localization, these statements say that every still-
live coordinate must occur in the localized circuit's bottom family.  They also cover dimension
zero (where both supports are empty), so no positivity side condition is needed in the interface.

This closes the proposed audit and rules out every semantically faithful parity round whose
progress invariant is a strict reduction in live bottom support.  In particular, weakening the
current target from zero support to any proper subset of the live cube cannot repair the initial
successor.  A dense-support round must keep full live support and make progress in a different
measure, such as simultaneous canonical decision-tree depth or a structural residual-depth
potential.

The precise next frontier is to formulate a dense-support successor whose good event is common
canonical shallowness while retaining full localized bottom support, then test whether the
already-proved common-shallow shell contraction and layered collapse can iterate without invoking
the support-tail complement.  The first concrete audit should compare the existing
`commonShallowBad` selector with full-support parity: determine whether its complement is
nonempty at the geometric parameters, or whether full sensitivity forces every root into that bad
set as well.  The separate SAT-density/fiber obstruction is unchanged.  No P-versus-NP conclusion
follows.

### Full support is compatible with a good common-shallow root

The proposed selector audit now closes in the nonvacuous direction.  The new theorem
`exists_commonShallowAt_linearGap_realized` extracts the strict consequence of the existing
scaled bad-set estimate.  For positive `G`, `m`, and `r`, width-two duplicate-free gates with at
most `m` clauses, ample fuel, and ambient dimension

```text
n = 1000 * (G*m) * r,
```

the `20*r` shell is nonempty and the saving factor `2^(10*r)` is at least two.  Hence the bad set
has cardinality strictly smaller than the shell, and there exists a root `sigma` with

```text
stars sigma = 20*r
CommonShallowAt gates fuel sigma (10*r) residualDepth.
```

The support-survivor specialization
`exists_commonShallowAt_linearGap_realized_of_full_support` adds the exact premise

```text
familyVariableSupport gates = univ
```

and obtains the same witness.  Thus full variable sensitivity does **not** force every geometric
shell root into `commonShallowBad`; unlike the zero-support tail, common canonical shallowness is a
viable progress measure for dense-support parity rounds.  This is an existence result for one
family at the realized-density scale, not yet a dense-support successor or an iterated parity
lower bound.

The precise next frontier is to specialize this good-root witness to
`normalizedLayeredBottomFamily C` for a localized parity-equivalent circuit, with circuit-owned
positive `G` and clause bound `m`, and construct the semantic collapse successor while retaining
the forced full bottom support.  Then audit whether the post-collapse actual alphabet/slot
recurrence still satisfies the realized-density premise at every remaining round.  The separate
SAT-density/fiber obstruction is unchanged.  No P-versus-NP conclusion follows.

### Dense-support parity has a semantic common-shallow successor

The circuit specialization and semantic handoff are now proved.  First,
`normalizedLayeredBottomFamily_support_eq_bottomSupport` strengthens the earlier one-way support
inclusion to the exact identity

```text
familyVariableSupport (normalizedLayeredBottomFamily C)
  = layeredBottomVariableSupport C.
```

The positive copy of every circuit bottom gate supplies the reverse inclusion, while `eraseDups`
preserves membership.  Consequently
`normalizedLayeredBottomFamily_support_eq_univ_of_eval_eq_parity_xor` shows that every localized
parity-XOR circuit gives the exact normalized selector a full-support family.

Next, `exists_normalizedLayered_commonShallowAt_of_realized_density` extracts a good `20*r`-star
root directly for the circuit-owned two-polarity family under `BottomWidth 2`, `BottomCount m`,
ample fuel, shell fit, positive `r`, and the rectangular realized-density inequality using the
exact index count `(layeredBottomFamilyList C).length`.  No separately supplied abstract `G` or
full-support premise is needed.

Finally, `exists_denseParity_normalizedCollapseSuccessor_of_realized_density` follows that common
trunk by `collapseRound`, refines to exactly `10*r` live coordinates, and transports the result to
the live cube.  If `C` computes `parity XOR phase`, the successor `D` computes

```text
parity XOR (fixedParityPhase kappa XOR phase),
```

has `BottomWidth (residualDepth+1)`, obeys the existing slot recurrence

```text
bottomSlotCount D
  <= bottomSlotCount C * (2^(residualDepth+1) + 1),
```

and its normalized bottom family is again exactly full support.  Thus dense semantic sensitivity
survives one proved common-shallow collapse round; support reduction is neither assumed nor
obtained.

The precise next frontier is quantitative iteration: instantiate the next round's clause bound
and exact two-polarity index count for this localized successor, then decide whether the available
`10*r` ambient coordinates can satisfy the next realized-density inequality after the width and
slot recurrences.  The likely pressure point is that the current theorem reduces width two to
`residualDepth+1`; retaining the width-two hypothesis roundwise requires residual depth at most one,
while the clause/slot envelope grows by `2^(residualDepth+1)+1`.  The separate SAT-density/fiber
obstruction is unchanged.  No P-versus-NP conclusion follows.

### Full support contradicts the rectangular realized-density premise

The next-round audit fails one step earlier than the width and slot recurrences.  The theorem
`not_normalizedLayered_realized_density_of_full_support` proves that, for every positive `r`, a
width-two circuit whose normalized two-polarity family has full support cannot satisfy

```text
(4 * (3 * (G*m + 1))) * (20*r) + 20*r <= n + 1,
```

where `G = length(layeredBottomFamilyList C)` and `m` bounds every indexed gate.  Indeed, width
two and full support give

```text
n <= 2 * sum_g length(normalizedLayeredBottomFamily C g) <= 2 * G*m.
```

But even before applying the positive `20*r` shell multiplier, the density base is strictly
larger than `2*G*m+1`.  The semantic corollary
`not_normalizedLayered_realized_density_of_eval_eq_parity_xor` derives the same contradiction
directly from `eval C = parity XOR phase`.

Consequently the hypotheses of
`exists_denseParity_normalizedCollapseSuccessor_of_realized_density` are inconsistent: its
successor statement is formally valid but vacuous for parity.  There is no next-round slot
schedule to optimize under this rectangular density theorem.  This corrects the earlier claim
that the abstract full-support specialization at ambient size `1000*(G*m)*r` was nonvacuous.
Its `_hfull` argument was unused by the proof, but width two and the `m` clause bound give support
capacity at most `2*G*m`, far below that ambient dimension for positive `r`; its combined premises
are therefore empty as well.

The precise next frontier is to replace the realized-density contraction with a support-compatible
counting theorem whose ambient requirement does not scale linearly with the full-support clause
alphabet times a positive shell size.  A sharp next audit is whether the existing canonical
common-shallow bad-set encoding can be charged to decision-tree queries or overlap structure
rather than total gate/term occurrences.  Without such a stronger selector theorem, dense-parity
iteration cannot start.  The separate SAT-density/fiber obstruction is unchanged.  No P-versus-NP
conclusion follows.

### Exact queried-variable subset charging is still vacuous at full support

The first proposed support-compatible replacement has now been audited without a power or density
relaxation.  `not_supportSubset_exact_balance_half_of_live_le_supportAlphabet` keeps the exact
factor

```text
choose A r
```

for the set of `r` queried variables.  At `K = 2r`, `d = r`, and saving exponent `r`, its exact
shell balance is impossible whenever the shell is nonempty and `n <= A`.  After the Boolean fiber
is cancelled, the smaller shell contributes `choose n r`; support coverage gives another
`choose n r <= choose A r`; and the standard product identity gives
`choose n (2r) <= choose n r * choose n r`.  The remaining factor `2^(2r)` makes the proposed
upper bound strictly larger than the target shell.

The circuit specialization
`not_normalizedLayered_supportSubset_balance_of_full_support` instantiates

```text
A = 2 * sum_g length(normalizedLayeredBottomFamily C g),
K = 20R,
d = saving = 10R.
```

For a width-two normalized family with full support, the existing support-cardinality theorem
forces `n <= A`, so the exact support-subset balance cannot hold.  The semantic corollary
`not_normalizedLayered_supportSubset_balance_of_eval_eq_parity_xor` obtains the same contradiction
from `eval C = parity XOR phase`.  Thus replacing stable gate/term keys by the global set of queried
variables removes occurrence redundancy but still cannot start the dense-parity round; this is an
exact no-go for that encoder, not an artifact of the earlier rectangular density estimate.

The precise next frontier is endpoint-local rather than global-support counting: seek a bound on
the average or distribution of realized query-set multiplicities inside each residual endpoint
fiber, using overlap or fixed-value profile structure.  Any uniform decoder that merely chooses an
arbitrary `d`-subset of the full live support necessarily pays the impossible `choose n d` factor.
The separate SAT-density/fiber obstruction is unchanged.  No P-versus-NP conclusion follows.

### Fixed-value profiles alone do not shrink the semantic bad event

The first endpoint-local fallback has now been separated from the all-false-profile artifact.
`restrictionFalseCompletion` canonically completes an arbitrary restriction, and
`restriction_not_commonShallowAt_independentLiteral_zero` proves that for the independent positive
singleton family every restriction satisfying

```text
d < stars sigma
```

fails `CommonShallowAt ... d 0`.  The proof follows an arbitrary fixed profile, flips one live
coordinate missed by the depth-`d` trunk, and uses leaf agreement to show that coordinate remains
free; its singleton gate therefore still has canonical depth one.

Consequently `commonShallowBad_independentLiteral_zero_eq_shell` identifies the complete semantic
bad set with the entire `K`-star restriction shell whenever `d < K`.  This includes every Boolean
assignment on the fixed coordinates, not just the previously audited all-false roots.  Thus
conditioning or averaging only on fixed-value profiles cannot supply a uniform endpoint-local
saving.  As before, the independent family uses one clause occurrence per live coordinate and is
outside the strict realized-density regime, so this is a regression boundary rather than a
density-admissible counterexample.

The precise next frontier is to make the endpoint-local estimate genuinely overlap-sensitive and
density-aware: bound realized query-set multiplicity using repeated ownership of live coordinates
by a sublinear clause-occurrence alphabet, or construct a density-admissible family that still
saturates a positive fraction of the endpoint fibers.  Any proposed fixed-profile-only saving is
now ruled out by the full-shell theorem above.  The separate SAT-density/fiber obstruction is
unchanged.  No P-versus-NP conclusion follows.

### Singleton endpoint multiplicity is exactly a live-support tail

The overlap-sensitive singleton audit is now exact.  For an arbitrary coordinate selector

```text
v : Fin G -> Fin n
```

`selectedLiteralGates v` contains one positive singleton gate per selector entry; `v` need not be
injective, so repeated ownership is allowed.  The theorem
`familyVariableSupport_selectedLiteralGates` identifies its actual support with `univ.image v`,
which quotients repeated owners automatically.

With ample fuel, `commonShallowAt_selectedLiteral_zero_iff` proves

```text
CommonShallowAt (selectedLiteralGates v) fuel sigma d 0
  iff card {i in image(v) | sigma(i) is live} <= d.
```

Both directions are semantic.  The upper direction uses the canonical support-respecting trunk.
For the lower direction, any shallower trunk misses a live owned coordinate on some path; flipping
that coordinate preserves the path and forces its singleton residual tree to retain depth one.
No fixed-value, selector-injectivity, or occurrence-multiplicity assumption is used.

Consequently `commonShallowBad_selectedLiteral_zero_eq_liveSupportTail` identifies the complete
bad set on every fuel-covered `K`-shell with the exact tail

```text
card(live(sigma) intersect image(v)) > d.
```

This sharpens the preceding full-shell regression boundary: fixed profiles are irrelevant, but
repeated ownership does help exactly to the extent that it shrinks the *distinct* support.  In the
density-admissible regime the remaining singleton count is therefore a hypergeometric support-tail
problem, rather than an endpoint-fiber multiplicity problem.

Direct module elaboration passed.  The downstream quantitative-iteration target passed with
8,451 jobs, and the full build passed with 8,068 jobs.  The two new printed capstones depend only
on `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was added.  `git diff --check` passed.  Existing counterexamples and unrelated
worktree changes were preserved.

The precise next frontier is to count this exact tail on a `K`-star restriction shell and derive a
closed binomial/hypergeometric bound in terms of `n`, `K`, `d`, and `card(image v)`.  Then compare
that sharp singleton benchmark with width-two families: either lift the charge from distinct live
support to a clause-overlap statistic, or exhibit a width-two interaction whose bad set is larger
than every bound predicted by its distinct-support tail.  The separate SAT-density/fiber
obstruction is unchanged.  No P-versus-NP conclusion follows.

### The singleton tail has a closed hypergeometric shell bound

The exact semantic classification now has a quantitative shell theorem.  For an arbitrary owned
support `A`, `liveSupportTail_card_le` covers every `K`-star restriction having more than `d` live
owned coordinates by a live `(d+1)`-subset of `A`.  Reusing the exact extension-fiber count gives

```text
|tail(A,K,d)|
  <= choose(|A|,d+1) * choose(n-(d+1),K-(d+1)) * 2^(n-K).
```

The selector specialization `commonShallowBad_selectedLiteral_zero_card_le` applies this directly
to `A = image(v)`.  The division-free balance theorem
`commonShallowBad_selectedLiteral_zero_hypergeometric_balance` rewrites the same result against the
exact shell size:

```text
choose(n,d+1) * |bad|
  <= choose(|image(v)|,d+1) * choose(n,K) * choose(K,d+1) * 2^(n-K).
```

Thus the singleton bad fraction is at most the standard first-moment hypergeometric factor

```text
choose(|image(v)|,d+1) * choose(K,d+1) / choose(n,d+1).
```

This count is overlap-sensitive in exactly the right singleton sense: repeated owners disappear
before the binomial factor is formed.  It also preserves the earlier full-support regression
boundary.  When `image(v)=univ` and `d<K`, the semantic bad event is the whole shell; the cover
overlaps heavily, so the first-moment bound correctly supplies no contraction.  The theorem is a
factorially sharp union bound, not a claim that its overlapping cover is an exact partition.

Direct elaboration of the support-survivor module passed.  The downstream quantitative-iteration
target passed with 8,451 jobs, and the full build passed with 8,068 jobs.  The three new capstones
depend only on `propext`, `Classical.choice`, and `Quot.sound`; no prohibited proof device was
introduced.  `git diff --check` passed, and existing counterexamples and unrelated worktree changes
were preserved.

The precise next frontier is width two.  Determine whether a width-two family's residual-depth-one
bad event can be charged to a bounded collection of `(d+1)`-subsets of a distinct-support or
overlap statistic, so that the same exact shell-fiber count applies.  The decisive alternative is
an explicit width-two family whose bad set exceeds every singleton-tail prediction based on its
distinct support.  An exact disjoint hypergeometric layer-sum for singletons would sharpen constants
if the union bound is borderline, but it does not address this structural question.  The separate
SAT-density/fiber obstruction is unchanged.  No P-versus-NP conclusion follows.

### Distinct support alone does not control residual-depth-one badness

The decisive width-two comparison is now kernel checked.  First,
`selectedLiteral_canonicalDT_depth_le_one` proves that every positive singleton gate has canonical
depth at most one for every fuel and every restriction.  Hence
`commonShallowAt_selectedLiteral_one` gives every selected-singleton family a zero-query common
trunk at residual depth one; its semantic bad set is empty at that threshold, independently of
the number of live support coordinates.

The theorem `widthTwo_residualOne_badness_not_determined_by_distinct_support` compares this family
with the existing exhaustive two-bit width-two gate at the identical parameters

```text
n = 2, fuel = 2, K = 2, trunkDepth = 0, residualDepth = 1.
```

Both families have exactly the full support `{0,1}`.  Nevertheless the fully live root is bad for
the exhaustive width-two family and good for the two singleton gates.  Thus residual-depth-one
badness is not a function of the distinct support set, and the singleton hypergeometric tail
cannot be lifted to width two by merely substituting the same support cardinality.  The missing
quantity must record clause interaction, polarity, or another structure finer than variable
ownership.

Direct elaboration of the support-survivor module passed.  The downstream quantitative-iteration
target passed with 8,451 jobs, and the full build passed with 8,068 jobs.  The three new printed
capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`,
custom axiom, `unsafe`, or `native_decide` was introduced.  `git diff --check` passed, and existing
counterexamples and unrelated worktree changes were preserved.

The precise next frontier is to extract the smallest interaction statistic that separates these
same-support families and still admits subset-fiber counting.  The first concrete candidate is the
number (or a fractional packing weight) of simultaneously live width-two clauses after deleting
gates already canonical-depth at most one.  Prove a shell upper bound in that statistic, or use
the existing two-polarity gadgets to show that unweighted live-edge counts also fail.  The separate
SAT-density/fiber obstruction is unchanged.  No P-versus-NP conclusion follows.

### Unweighted live width-two clause count also fails

The suggested raw live-edge statistic is now ruled out by a matched, kernel-checked comparison.
Define `liveWidthTwoClauseCount gates rho` to count width-two clause occurrences whose two variables
are both live at `rho`.  At the fully live four-coordinate root, the existing two-pair polarity
family and a new family consisting of both polarities of two disjoint one-clause gates have:

```text
the same distinct support = {0,1,2,3},
the same live width-two clause count = 4,
fuel = K = 4, trunkDepth = 2, residualDepth = 1.
```

Their badness is opposite.  The interacting family puts two disjoint clauses inside each polarity
gate and has exact common-trunk cost three, so the all-live root is bad at budget two.  The matched
disjoint family puts one clause in each indexed gate; querying coordinates `0` and `2` makes every
gate residual-depth one, so the same root is good at budget two.  Thus neither distinct support nor
unweighted live width-two clause count, even taken together, determines residual-depth-one badness.
The missing information is specifically within-gate clause interaction: regrouping the same four
live clauses changes the common switching cost.

The new capstones are `localDisjointPairPolarityFamily_commonShallowAt_two`,
`twoPairPolarity_matched_live_clause_profile`, and
`widthTwo_residualOne_badness_not_determined_by_live_clause_count` in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  They introduce no `sorry`, `admit`, custom
axiom, `unsafe`, or `native_decide`.

An isolated elaboration of the exact added declarations against the last valid bridge artifact
passed; all three printed capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.
Direct elaboration of the support-survivor module passed, the quantitative-iteration build passed
with 8,451 jobs, and `git diff --check` passed.  A direct full target rebuild of the much larger
2-SAT bridge was also attempted.  It elaborated the new section without error, but later failed in
pre-existing declarations around lines 7311--7417 (`twoPairTenFlexibleCostTailCoefficient_eq_sum`
and dependents) through heartbeat timeouts followed by an unknown-constant/unsolved-goal cascade;
the process finally exited with code 137.  Therefore no full-build pass is claimed for this step.

The precise next frontier is to test the smallest within-gate statistic: count (or fractionally
pack) unordered pairs of simultaneously live clauses belonging to the same indexed gate, after
discarding gates already residual-depth one.  Either charge every bad trunk to a bounded subset of
such co-live clause pairs and reuse the exact shell-fiber count, or construct a matched regrouping
with equal within-gate pair mass but opposite badness.  If the latter exists, the statistic must
retain polarity-sensitive transversal/conflict structure rather than scalar edge mass.  The
separate SAT-density/fiber obstruction is unchanged.  No P-versus-NP conclusion follows.

### Scalar within-gate co-live pair mass also fails

The smallest proposed within-gate scalar refinement is now ruled out by a matched,
kernel-checked comparison.  Define `activeWithinGateLivePairMass` by first discarding every
indexed gate whose canonical tree is already within the requested residual-depth budget, then
summing `choose(L_g,2)`, where `L_g` is the number of width-two clauses in gate `g` whose two
variables are live.

At the fully live four-coordinate root, compare the existing `twoPairPolarityFamily` with
`localOppositePairGroupedFamily`.  The first groups two disjoint clauses by global polarity; the
second groups the positive and negative clauses of each local coordinate pair.  The two families
have:

```text
the same distinct support = {0,1,2,3},
the same live width-two clause count = 4,
the same active within-gate co-live pair mass = 2,
fuel = K = 4, trunkDepth = 2, residualDepth = 1.
```

Their badness is nevertheless opposite.  The polarity-grouped family has exact common-trunk cost
three and is bad at budget two.  For the local-pair-grouped family, querying coordinates `0` and
`2` leaves at most one live singleton clause in each nonterminal gate, so it is good at budget
two.  Thus scalar within-gate pair mass still forgets decisive structure: which polarities and
coordinate transversals the paired clauses realize.

The new capstones are `localOppositePairGroupedFamily_commonShallowAt_two`,
`twoPairPolarity_matched_withinGatePair_profile`,
`twoPairPolarity_withinGatePairMass_eq_two`, and
`widthTwo_residualOne_badness_not_determined_by_withinGatePairMass` in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  They introduce no `sorry`, `admit`, custom
axiom, `unsafe`, or `native_decide`.

An isolated elaboration of the exact new declarations against the last valid bridge artifact
passed.  All four printed capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.
A direct elaboration of the large 2-SAT bridge reached and passed the complete new section, then
continued through line 7024 before it was stopped rather than spending another long cycle in the
already documented heartbeat-heavy tail; no full bridge build pass is claimed.  The downstream
quantitative-iteration build passed with 8,451 jobs.  `git diff --check` passed, and existing
counterexamples and unrelated worktree changes were preserved.

The precise next frontier is no longer a scalar pair count.  Retain a polarity-sensitive
within-gate conflict/transversal type for each co-live clause pair, and test whether its small
finite profile determines the local residual-depth-one switching cost.  The decisive alternatives
are: prove that every bad trunk exposes a bounded subset of incompatible pair types, enabling the
existing shell-fiber count; or construct another matched example with the same typed pair profile
but opposite badness, forcing genuine higher-order clause hypergraph data.  The separate
SAT-density/fiber obstruction is unchanged.  No P-versus-NP conclusion follows.

### Signed conflict/transversal typing separates the scalar-pair counterexample

The first polarity-sensitive co-live pair profile is now defined and kernel checked.  For each
active within-gate unordered pair of live width-two clauses it records the triple

```text
(same-polarity shared variables,
 opposite-polarity shared variables,
 union-support size).
```

This is a finite local refinement of scalar pair mass: the first two coordinates retain literal
conflict and the third retains transversal geometry.  On the previous matched families, the two
units of scalar mass split into opposite exact types:

```text
twoPairPolarityFamily:             type (0,0,4) has count 2; type (0,2,2) has count 0,
localOppositePairGroupedFamily:    type (0,0,4) has count 0; type (0,2,2) has count 2.
```

Thus the bad polarity-grouped gadget consists of disjoint sign-aligned clause pairs, while the
good local grouping consists of same-support opposite-sign conflicts.  The new type therefore
separates the exact counterexample that defeated scalar within-gate mass; that counterexample is
not evidence against typed charging.  This is only a separation result, not a proof that the type
profile determines common switching cost.

The new definitions are `clausePositiveVariableSupport`, `clauseNegativeVariableSupport`,
`clausePairSamePolarityOverlap`, `clausePairOppositePolarityOverlap`, `clausePairTypeCount`, and
`activeWithinGateLivePairTypeCount`.  The exact capstones are
`twoPairPolarity_disjointAlignedPairType_eq_two`,
`localOppositePairGrouped_oppositeConflictPairType_eq_two`, and
`twoPairPolarity_typedPairProfile_separates_matched_families` in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.

Focused elaboration through the complete new section passed.  The three printed capstones depend
only on `propext`, `Classical.choice`, and `Quot.sound`.  The downstream quantitative-iteration
build passed with 8,451 jobs, and `git diff --check` passed.  A direct full bridge elaboration was
started and passed the insertion region but was stopped before its known heartbeat-heavy tail, so
no full bridge pass is claimed.  Existing counterexamples and failed routes remain in place.  The
precise next frontier is to test sufficiency rather than separation:
enumerate the smallest normalized width-two families with the same complete triple-count profile
and compare their exact flexible common-query costs.  An equal-profile/opposite-cost match would
force higher-order clause-hypergraph data; if none appears, prove that every residual-depth-one bad
trunk exposes a bounded collection of disjoint-aligned `(0,0,4)`-type pairs and connect that charge
to the existing subset-fiber count.  The separate SAT-density/fiber obstruction is unchanged.  No
P-versus-NP conclusion follows.

### Complete signed pair profiles still do not determine common-query cost

The smallest normalized-family test found and kernel checked an equal-profile/opposite-cost
comparison.  Both new families use two active indexed gates, exactly two distinct width-two clauses
per gate, and only coordinates `0,1,2` of an ambient four-coordinate block.  Their active pair types
are identical as a complete histogram over `Fin 3 × Fin 3 × Fin 5`: one gate contributes type
`(1,1,2)` and the other contributes type `(0,1,3)`.  They also agree on distinct support, live
width-two clause count, and scalar within-gate pair mass.

The clause presentations are:

```text
low cost:  {¬0¬1, ¬0·1}   {¬0¬1, 0¬2}
high cost: {¬0¬1, ¬0·1}   {¬0¬2, ¬1·2}
```

Their exact residual-depth-one common-query costs differ.  Querying coordinate zero switches the
low-cost family, and no zero-query trunk works, so its exact cost is one.  Querying coordinates zero
and one switches the high-cost family.  Conversely, exhaustive leaf classification proves that any
restriction shallowing both high-cost gates has at most two live ambient coordinates.  The general
leaf-agreement lower bound leaves at least three coordinates live after a depth-one trunk from the
fully live root, so such a trunk is impossible.  Its exact cost is therefore two.  At trunk budget
one the matched families have opposite semantic badness.

The new capstones are `typedPairFamilies_complete_profile_eq`,
`typedPairLowCostFamily_exact_cost_one`, `typedPairHighCostFamily_exact_cost_two`, and
`widthTwo_badness_not_determined_by_complete_typed_pair_profile` in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  Focused direct elaboration passed through the
entire new section and continued into the later finite-game development.  Printed axioms for all
new capstones are exactly `propext`, `Classical.choice`, and `Quot.sound`.  No `sorry`, `admit`,
custom axiom, `unsafe`, or `native_decide` was introduced.  The downstream quantitative-iteration
build passed with 8,451 jobs.  The direct bridge elaboration's known heartbeat-heavy tail was not
run to completion, so no separate full direct bridge pass is claimed for this step.

The precise next frontier is higher-order incidence, not another aggregate pair histogram.  Retain
which active pair-type witnesses share variables across indexed gates (a colored support-incidence
graph), and test whether a bounded incidence signature controls residual-depth-one cost.  The first
target is the new matched pair: isolate the cross-gate overlap that distinguishes exact costs one
and two, then either derive a subset-fiber charge from bounded connected incidence components or
construct an incidence-matched counterexample forcing triple-of-clauses data.  The separate
SAT-density/fiber obstruction is unchanged.  No P-versus-NP conclusion follows.

### Signed cross-gate clause incidence separates the equal-pair-profile example

The first higher-order incidence refinement is now defined and kernel checked.  For every ordered
pair of distinct active indexed gates, `activeCrossGateLivePairTypeCount` counts a live width-two
clause from each gate by the same bounded signed type used within gates:

```text
(same-polarity shared variables,
 opposite-polarity shared variables,
 union-support size).
```

The normalized low- and high-cost families from the preceding comparison have exactly the same
indexed *uncolored* gate supports: corresponding gates use the same variable sets.  Thus even the
gate-support hypergraph, with gate identities retained, does not distinguish them.  Their signed
cross-gate clause incidence does.  The low-cost family repeats the identical clause `¬0¬1` across
its two gates, so it has two ordered cross-gate witnesses of type `(2,0,2)`; the high-cost family
has none.  Consequently their complete bounded cross-gate signed profiles differ.

The new definitions are `crossClausePairTypeCount`, `activeCrossGateLivePairTypeCount`, and
`boundedActiveCrossGatePairTypeProfile`.  The principal capstones are
`typedPairFamilies_indexed_gate_supports_eq`,
`typedPairFamilies_crossGate_identicalAligned_separates`,
`typedPairFamilies_crossGate_complete_profiles_ne`, and
`typedPairFamilies_crossGate_profile_is_new_information` in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.

Direct Lean elaboration passed the complete new section and continued into the later finite-game
development.  The deliberately capped run then stopped before the bridge's already documented
heartbeat-heavy tail, so no separate full direct bridge pass is claimed.  Printed axioms for all
four new capstones are exactly `propext`, `Classical.choice`, and `Quot.sound`.  The downstream
quantitative-iteration build passed with 8,451 jobs.  No `sorry`, `admit`, custom axiom, `unsafe`,
or `native_decide` was introduced.  Existing counterexamples and failed routes remain in place.

The evidence now supports a sharper boundary: an uncolored cross-gate support graph is still too
coarse, while signed clause-level cross-gate incidence separates the current minimal matched pair.
This is a separation result only, not evidence that the aggregate cross-gate profile determines
common-query cost.  The precise next frontier is to enumerate the smallest normalized families
matching both the complete within-gate and complete cross-gate signed profiles and compare exact
residual-depth-one costs.  An opposite-cost match would force witness-identified incidence
components or triple-of-clauses data; if no small match exists, the next positive step is a bounded
connected-component charge into the subset-fiber count.  The separate SAT-density/fiber
obstruction is unchanged.  No P-versus-NP conclusion follows.

### Aggregate signed cross-gate profiles still do not determine common-query cost

The smallest support-matched counterexample found by the next normalized-family search is now
kernel checked.  It uses three active indexed gates, two distinct width-two clauses per gate, and
the common global support `{0,2,3}` inside an ambient four-coordinate block.  Both families agree
on all aggregate invariants developed so far:

```text
global variable support,
live width-two clause count,
active within-gate pair mass,
every coordinate of the complete within-gate signed pair profile,
every coordinate of the complete ordered cross-gate signed pair profile.
```

The low-cost clauses are

```text
{0·2, ¬0¬2}   {0·2, ¬2¬3}   {¬2¬3, 2·3},
```

and the high-cost clauses are

```text
{0¬2, 2¬3}   {¬0¬3, 0·3}   {0·3, ¬0¬3}.
```

Coordinate `2` is a common good query for all three low-cost gates, so their exact
residual-depth-one common-query cost is one.  For the high-cost family, exhaustive restriction
classification proves that every simultaneously shallow restriction has at most two live ambient
coordinates.  The general leaf-agreement lower bound therefore rules out a depth-one trunk from
the fully live root, while querying coordinates `0` and `3` supplies a depth-two trunk.  Its exact
cost is two.  Hence the matched families have opposite semantic badness at trunk budget one.

The aggregate profile loses exactly the expected witness placement: the functions assigning an
uncolored variable support to each indexed gate are unequal.  Thus aggregate cross-gate color
counts cannot support the proposed connected-component charge; gate-pair identity (or an
equivalent witness-identified colored incidence structure) must be retained before components can
be defined.

The new definitions are `aggregateCrossLowCostFamily` and
`aggregateCrossHighCostFamily`.  The principal capstones are
`aggregateCrossFamilies_complete_profiles_eq`,
`aggregateCrossFamilies_indexed_gate_supports_ne`, `aggregateCrossFamilies_exact_costs`, and
`widthTwo_badness_not_determined_by_aggregate_signed_pair_profiles` in
`ComputationalDepthMultiSwitchingTwoSATBridge.lean`.  Focused elaboration of the complete new
section passed.  Printed axioms for all four capstones are exactly `propext`,
`Classical.choice`, and `Quot.sound`.  The downstream quantitative-iteration build passed with
8,451 jobs, `git diff --check` passed, and no `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was introduced.  The exhaustive search also preserved two useful negative results: no
support-matched opposite-cost pair exists in the searched two-gate/two-clause universes on three,
four, or five variables, while five four-variable matches appear if global support equality is
dropped.  These search observations guide minimality but are not claimed as Lean theorems.

The precise next frontier is to retain the complete signed profile separately for every indexed
gate pair (rather than summing over all pairs) and test the new three-gate witness.  If that indexed
profile separates it, enumerate the smallest indexed-profile match; such a match would force
triple-of-clauses or explicit connected-component data.  If no small match appears, formulate a
bounded witness-identified component code and compare its alphabet cost with the existing
subset-fiber saving.  The separate SAT-density/fiber obstruction is unchanged.  No P-versus-NP
conclusion follows.

### Indexed gate-pair profiles separate the aggregate witness

The complete signed cross-gate profile has now been retained separately for every ordered indexed
gate pair.  `indexedActiveCrossGatePairTypeProfile` uses the same active-gate, live-width-two, and
signed overlap/transversal coordinates as the previous aggregate profile, but does not sum away
the pair `(g,h)` carrying each witness.

The capstones `aggregateCrossFamilies_indexed_gate_zero_one_separates` and
`aggregateCrossFamilies_indexed_crossGate_profiles_ne` are kernel checked.  At ordered gate pair
`(0,1)`, signed type `(same=2, opposite=0, unionSize=2)` has count one in the low-cost family and
zero in the high-cost family, so the complete indexed profiles are unequal.  Thus the current
counterexample is fully explained by witness redistribution among indexed gate pairs; it does not
refute the indexed refinement.  This is only a separation of one witness, not a proof that
indexed pair profiles determine common-query cost in general.

Focused direct elaboration passed the new definition and capstone and continued beyond them into
the later finite-game section; the deliberately stopped run is not claimed as a full direct-file
pass.  The quantitative-iteration target also passed as a separate regression build (8,451 jobs).  No
`sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was introduced, and the existing
counterexamples and failed routes remain intact.

The precise next frontier is to search for the smallest normalized opposite-cost families that
match the complete within-gate profile and the complete signed profile for every indexed gate
pair.  A match would prove that triple-clause or explicit connected-component incidence is
necessary.  If no small match exists, formulate a bounded witness-identified component code and
compare its alphabet cost with the existing subset-fiber saving.  The separate SAT-density/fiber
obstruction is unchanged.  No P-versus-NP conclusion follows.

### The aggregate witness also fails the indexed within-gate profile

Auditing the preceding interpretation exposed a second loss of witness placement.  The complete
within-gate signed profile used there is still summed over gate indices.  The new
`indexedActiveWithinGatePairTypeProfile` retains the active gate carrying each signed unordered
clause-pair type, complementing the already indexed off-diagonal cross-gate profile.

The same three-gate low/high-cost comparison is separated on this diagonal data too.  At gate
zero and signed type `(same=0, opposite=2, unionSize=2)`, the low-cost family has count one and the
high-cost family has count zero.  The capstones
`aggregateCrossFamilies_indexed_within_gate_zero_separates` and
`aggregateCrossFamilies_indexed_withinGate_profiles_ne` are kernel checked.  Consequently the
earlier aggregate counterexample cannot be described as failing only because ordered gate-pair
identities were summed away: it redistributes both within-gate and cross-gate colored witnesses.

As search guidance, exhaustive external enumeration found no opposite one-query-cost pair among
38,226 canonically ordered two-gate/two-distinct-clause families on four variables, nor among
50,116 three-gate/two-distinct-clause families on three variables, when global support, the
complete indexed cross-gate profiles, and the applicable complete within-gate profile were
matched.  These finite-search observations are not Lean theorems and are not used as proof.

The precise next frontier is therefore to match the *indexed* within-gate profile together with
every indexed cross-gate signed profile.  Search the three-gate/four-variable normalized universe
for an opposite-cost pair.  A match would isolate genuinely triple-clause incidence; if none
appears, define the full indexed pair-incidence matrix (diagonal plus off-diagonal) and bound a
witness-identified connected-component code against the existing subset-fiber saving.  The
separate SAT-density/fiber obstruction is unchanged.  No P-versus-NP conclusion follows.

### The normalized three-gate/four-variable indexed-profile search is negative

The next finite frontier has now been exhaustively audited by
`tools/search_indexed_pair_profiles.cpp`.  The search constructs all 24 signed width-two clauses
on pairs of distinct variables in `Fin 4`, all 276 canonically clause-ordered gates containing two
distinct clauses, and all 21,024,576 **ordered** triples of such gates (including repeated gates).
Keeping ordered triples is essential: two matched families can require different permutations of
their indexed gates.

The executable recurrence directly mirrors `canonicalDT` with fuel four.  All 276 normalized
gates are active at residual-depth budget one.  Each family is keyed by:

```text
global variable support,
the exact signed within-gate pair type at each of the three gate indices,
the complete four-witness signed cross-gate histogram at each indexed gate pair.
```

For each key, the search compares whether some single variable, on both Boolean branches, leaves
all three canonical gate trees at depth at most one.  It found 60,395 distinct exact signatures
and no signature containing both a one-query-good family and a one-query-bad family:

```text
NO_MATCH families=21024576 active_gates=276 signatures=60395
```

This is exhaustive for the stated normalized universe, including all indexed orders, but it is an
external finite-search result rather than a Lean theorem.  It neither proves that indexed pair
profiles determine common-query cost for larger variable sets, more clauses per gate, or more
gates, nor rules out a triple-incidence counterexample there.  Existing positive counterexamples
to every coarser aggregate profile remain valid.

The evidence nevertheless changes the best next action.  Another search over the same local
shape has been exhausted; the precise next frontier is to define the full indexed pair-incidence
matrix (diagonal within-gate cells and off-diagonal cross-gate cells) as a single bounded object,
then formulate a witness-identified connected-component code and compare its alphabet cost with
the verified subset-fiber saving.  In parallel, the first genuinely stronger counterexample
search should add one clause per gate or one gate, rather than merely adding unused ambient
coordinates.  The separate SAT-density/fiber obstruction is unchanged.  No P-versus-NP
conclusion follows.

### The complete indexed pair-incidence matrix has a finite but prohibitive raw alphabet

The diagonal and off-diagonal signed profiles are now packaged into one lossless bounded object.
`IndexedPairIncidenceMatrix G m` has one coordinate for every ordered indexed gate pair and every
signed width-two type in `Fin 3 × Fin 3 × Fin 5`.  Under the standard per-gate clause bound
`length ≤ m`, each coordinate lies in `Fin (m*m+1)`.

The bound is kernel checked rather than imposed by truncation.  The new lemmas
`clausePairTypeCount_le_length_sq` and `crossClausePairTypeCount_le_length_mul` prove respectively
that a diagonal unordered-pair count and an off-diagonal ordered-pair count are at most `m²`.
`indexedPairIncidenceMatrix_diagonal` and `_offDiagonal` then recover the earlier complete indexed
profiles exactly from the packaged object.

The exact raw alphabet cost is also proved:

```text
card (IndexedPairIncidenceMatrix G m) = (m²+1)^(45*G²).
```

This resolves the bounded-object interface but gives a negative quantitative audit of the naive
code.  In the exhausted normalized search universe `G=3,m=2`, the ambient matrix alphabet already
has size `5^405`, despite the search realizing only 60,395 exact signatures among 21,024,576
families.  Charging the entire matrix as an auxiliary label would therefore discard nearly all
available structure and has no verified comparison that is absorbed by the existing
prefix-subset fiber saving.  The matrix is a semantic container, not yet a viable encoder.

Focused direct elaboration passed the new section and continued into the later finite-game
development.  A complete package target build replayed 8,486 dependencies and entered the
known heartbeat-heavy target tail, but the managed process ended without producing a fresh olean
or a reliable completion status, so no full direct-file or printed-axiom completion is claimed.
The separate quantitative-iteration regression build passed with 8,451 jobs.  No `sorry`,
`admit`, custom axiom, `unsafe`, or `native_decide` was introduced; existing counterexamples,
negative searches, and failed routes remain in place.

The precise next frontier is to replace the raw `G² × 45` array by a sparse
witness-identified incidence object: define the support of its nonzero cells, form connected
components through shared clause witnesses, and prove an injective reconstruction from component
data.  Only then should its realized component alphabet be compared with the subset-fiber saving.
For counterexample search, the first stronger universe remains three clauses per gate or four
gates.  The separate SAT-density/fiber obstruction is unchanged.  No P-versus-NP conclusion
follows.

### The nonzero matrix support now has a lossless sparse encoding

The first sparse layer is now formalized.  `IndexedPairIncidenceCoordinate G` bundles the two
indexed gates and the three signed type coordinates, and `indexedPairIncidenceSupport` retains
exactly those bundled coordinates whose bounded matrix value is nonzero.
`SparseIndexedPairIncidenceCode G m` stores a canonical finite support and values only under
membership proofs for that support; its nonzero invariant prevents padding by irrelevant zero
coordinates.

The capstones `sparseIndexedPairIncidenceDecode_encode` and
`sparseIndexedPairIncidenceEncode_injective` prove that this representation loses no matrix
information.  The coordinate universe is also kernel checked exactly:

```text
card (IndexedPairIncidenceCoordinate G) = 45 * G * G.
```

An isolated elaboration of the exact sparse definitions and proofs passed, with all three new
capstones depending only on `propext`, `Classical.choice`, and `Quot.sound`.  Direct elaboration
of the complete bridge passed the new section and continued beyond line 6,250 before the known
heavy tail was deliberately stopped; no full direct-file completion is claimed.  `git diff
--check` passed, and no `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was added.

This separates the two costs that the raw alphabet conflated: choosing the realized nonzero
cells and storing their nonzero multiplicities.  It does **not** yet prove a useful alphabet
bound, because no bound on realized support size has been derived.  More importantly, a nonzero
matrix cell still aggregates all clause-pair witnesses of that type.  Therefore connectedness
through a shared clause occurrence cannot be recovered from matrix support alone, even though
the matrix itself is reconstructed exactly.

The precise next frontier is consequently sharper: define indexed live clause occurrences
(gate index plus term position), define typed incidence witnesses as occurrence pairs, and prove
that forgetting witness identities recovers `indexedPairIncidenceSupport` and its stored counts.
Only at that witness level can connected components through shared occurrences be formed and
their realized component alphabet compared with the subset-fiber saving.  The first stronger
counterexample universe remains three clauses per gate or four gates.  The separate
SAT-density/fiber obstruction is unchanged.  No P-versus-NP conclusion follows.

### Occurrence identities now recover every sparse matrix cell exactly

The matrix aggregation boundary has now been crossed without loss.  `indexedLiveClauses` fixes
the exact filtered list used by the matrix, and `IndexedLiveClauseOccurrence` records its gate,
filtered-list position, and clause payload.  The position deliberately distinguishes duplicate
syntactic clauses.  `indexedLiveClauseOccurrences` is the canonical `zipIdx` enumeration from
which every incidence witness is built.

`typedIncidenceWitnesses` retains the two occurrence identities behind one bundled signed matrix
coordinate.  On a diagonal cell it uses the earlier/later list orientation of
`clausePairTypeCount`; off the diagonal it uses the ordered Cartesian orientation of
`crossClausePairTypeCount`.  Gates already within the residual-depth budget contribute the empty
witness list, exactly matching the prior profiles.

The capstone `typedIncidenceWitnesses_length_eq_matrix` proves that forgetting identities by
taking list length recovers the bounded matrix value at every coordinate.  The companion
`mem_indexedPairIncidenceSupport_iff_witnesses_nonempty` proves that sparse support membership is
equivalent to existence of at least one such witness.  Thus both the stored multiplicities and
the canonical nonzero support are recovered from the witness layer.

Direct elaboration passed both capstones, printed their axioms as exactly `propext`,
`Classical.choice`, and `Quot.sound`, and continued past line 6,400 before the known heavy tail was
deliberately stopped; no full direct-file completion is claimed.  `git diff --check` passed, and
the quantitative-iteration regression build passed with 8,451 jobs.  No `sorry`, `admit`, custom
axiom, `unsafe`, or `native_decide` was introduced.  Existing counterexamples, negative searches,
and failed routes remain intact.

The precise next frontier is now to put an undirected adjacency relation on live occurrences:
two occurrences are adjacent when they appear together in some typed incidence witness.  Define
the resulting finite connected components, prove that component data reconstructs the complete
witness lists (and hence the sparse matrix), and only then audit the realized component alphabet
against the subset-fiber saving.  A key quantitative question is whether component locality pays
for occurrence positions without reverting to the prohibitive ambient `45 * G²` coordinate
charge.  The separate SAT-density/fiber obstruction is unchanged.  No P-versus-NP conclusion
follows.

### The occurrence graph interface exposes a likely component-locality failure

The undirected witness adjacency is now defined as `TypedIncidenceAdjacent`: two distinct live
occurrence identities are related exactly when one orientation of their pair belongs to some
`typedIncidenceWitnesses` coordinate.  `typedIncidenceAdjacent_symm` records the required
symmetry directly, without quotienting occurrence identities or forgetting duplicate positions.

Inspecting the defining branches before building a connected-component API exposes a more
important structural fact.  The coordinate alphabet ranges over the exact signed type of every
width-two clause pair.  Consequently, for two distinct active gate indices `g ≠ h`, every
canonical live occurrence at `g` pairs with every canonical live occurrence at `h` in the
off-diagonal Cartesian branch, at the uniquely determined `(same, opposite, unionSize)`
coordinate.  Thus the proposed graph is complete bipartite across every pair of active gates.
When at least two active gates have live occurrences, all their occurrences lie in one connected
component; splitting by connected components cannot provide the hoped-for gate locality.  The
same-gate unordered branch only strengthens this collapse.

This is presently a definition-level audit, not a newly kernel-checked clique theorem.  The
current managed shell exposes neither `lean`, `lake`, nor `elan`, and a filesystem search found no
executable toolchain, so no elaboration or printed-axiom claim is made for the new adjacency
lines.  `git diff --check` does pass.  The general cross-gate completeness proof was drafted far
enough to identify its exact obligations--the `Fin 3`, `Fin 3`, and `Fin 5` bounds follow from
the two width-two clauses--then removed rather than leaving an unverified capstone.  This failed
verification route is recorded here rather than being silently promoted to evidence.

The precise next frontier is therefore to kernel-check the adjacency definition and formalize
the cross-gate completeness theorem as soon as the Lean toolchain is available.  If it passes,
abandon connected components of the *complete typed-pair witness graph* as a compression device.
The next viable locality test should instead use a strictly sparser edge notion (for example,
shared variables or signed conflicts only) together with an explicit proof of what additional
data reconstructs the omitted disjoint-pair witnesses.  Only that reconstruction cost should be
compared with the subset-fiber saving.  The separate SAT-density/fiber obstruction is unchanged.
No P-versus-NP conclusion follows.

### Cross-gate Cartesian completeness is now kernel checked modulo the explicit type bounds

The defining structural claim has been separated into two reusable theorems.
`mem_crossTypedOccurrencePairs_iff` proves that membership in the off-diagonal witness list is
exactly membership of the two occurrences in their respective canonical live lists together
with their three signed-type equalities.  Thus the enumerator contains every Cartesian pair at
its uniquely determined color; there is no hidden filtering condition beyond that color.

`typedIncidenceAdjacent_of_crossGate_mem_of_type_lt` then proves that any two canonical
occurrences from distinct active gates are adjacent whenever their determined color fits the
declared `Fin 3 × Fin 3 × Fin 5` alphabet.  The three bounds are left as explicit hypotheses,
rather than being concealed inside the graph theorem.  This kernel-checks the decisive
completeness mechanism and confirms that connected components of the complete typed-pair graph
cannot yield gate locality once those routine width-two bounds are supplied.

The absolute toolchain at `/home/darre/.elan/bin` was used for direct elaboration.  Lean passed
both new theorems and continued beyond line 7,700 of the bridge without an error before the
known heavy tail was stopped; therefore no full-file completion or printed-axiom result is
claimed.  `git diff --check` passes, and no `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was introduced.  Existing counterexamples and failed compression routes remain
in place.

The precise next frontier is to discharge the three finite-color premises directly from
membership in `indexedLiveClauseOccurrences`: prove same-polarity and opposite-polarity overlap
at most two and union support at most four for the filtered width-two clauses.  That will give
the unconditional cross-gate clique theorem.  Once obtained, abandon components of this complete
graph and test a sparse shared-variable or signed-conflict graph, with an explicit reconstruction
charge for omitted disjoint-pair witnesses.  No P-versus-NP conclusion follows.

### The complete typed-pair occurrence graph has an unconditional cross-gate clique

The finite-color premises are now discharged from canonical occurrence membership itself.
`IndexedLiveClauseOccurrence.lits_length_eq_two_of_mem` pulls membership through the mapped
`zipIdx` enumerator and the live-clause filter, proving that every enumerated payload has literal
length exactly two.  The two signed-support inclusion lemmas show that positive and negative
variable supports lie inside the unsigned clause support.  Consequently
`clausePairSamePolarityOverlap_le_leftSupport` and
`clausePairOppositePolarityOverlap_le_leftSupport` bound both signed overlaps by the first
clause's unsigned support.

`liveOccurrence_pair_type_bounds` combines these facts with
`clauseVariableSupport_card_le_width` and `Finset.card_union_le`: each signed overlap is at most
two and the union support is at most four.  Therefore every pair of canonical live width-two
occurrences has a valid color in `Fin 3 × Fin 3 × Fin 5`.

The capstone `typedIncidenceAdjacent_of_crossGate_mem` now removes all three explicit type-bound
hypotheses from the prior Cartesian theorem.  Any canonical occurrences belonging to distinct
active gates are adjacent.  This formally rules out connected components of the complete typed
pair witness graph as a gate-local compression: its off-diagonal active part is a clique across
gate parts, independent of the particular signed overlaps.

Direct Lean elaboration passed the new support lemmas, occurrence-width theorem, finite-color
bound, and unconditional clique theorem, then continued beyond line 8,200 before the known heavy
tail was deliberately stopped.  Thus no full-file completion or printed-axiom result is claimed.
`git diff --check` passes, and no `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was
introduced.  Existing counterexamples and failed compression routes remain intact.

The precise next frontier is to define the strictly sparser shared-variable or signed-conflict
graph and prove an exact decomposition of `typedIncidenceWitnesses` into retained edges plus the
omitted disjoint-pair witnesses.  The resulting reconstruction payload--especially occurrence
positions for omitted pairs--must then be counted against the subset-fiber saving.  If that
payload recreates a quadratic gate-pair charge, this locality route should be abandoned rather
than hidden behind component notation.  No P-versus-NP conclusion follows.

### Shared-variable sparsification now has an exact lossless witness split

The first sparse locality candidate is now formalized as
`SharedVariableTypedIncidenceAdjacent`: it restricts the complete typed-incidence graph to pairs
whose unsigned clause supports have nonempty intersection.  Symmetry is proved, so the relation
is ready for a finite-component construction if its reconstruction charge proves favorable.

More importantly, sparsification no longer hides the omitted information.
`typedIncidenceWitnessDecomposition` maps every witness in every matrix coordinate to a tagged
sum: the left tag retains shared-variable pairs and the right tag records disjoint-support pairs.
`map_forgetTypedIncidenceWitnessTag_decomposition` proves that forgetting only this tag recovers
the original witness list exactly, including occurrence identities, duplicate positions, gate
orientation, and list order.  The companion filtered lists
`sharedVariableTypedIncidenceWitnesses` and `disjointVariableTypedIncidenceWitnesses` satisfy the
exact length partition `shared_add_disjoint_witness_lengths_eq`.

Thus the sparse graph itself is cheap only if the right-tagged disjoint payload is cheap.  There
is presently no such bound: every omitted witness still carries both occurrence identities, and
the earlier cross-gate Cartesian theorem shows that disjoint pairs can occur across all active
gate pairs.  Component notation alone therefore provides no compression theorem yet; it merely
separates the hoped-for local part from the payload that must be counted.

Direct Lean elaboration passed all new definitions and proofs and continued beyond line 7,900
before the known heavy tail was deliberately stopped.  No full-file completion or printed-axiom
claim is made.  The quantitative-iteration regression target passed with 8,451 jobs.  A separate
exact bridge-module build replayed its dependencies and reached the final source job without an
error, but that heavy job exceeded a six-minute bound; this is recorded as a timeout, not a build
success.  `git diff --check` passes, and no `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was introduced.  Existing counterexamples and failed routes remain intact.

The precise next frontier is quantitative: prove an exact cross-gate formula for the right-tagged
payload, then construct a width-two family with pairwise disjoint clause supports to test its
worst case.  If the disjoint payload reaches the full Cartesian product of occurrence lists over
quadratically many active gate pairs, the shared-variable component route recreates the original
quadratic witness charge and should be abandoned.  Only if a restriction- or survivor-specific
bound prevents that worst case should connected components be developed further.  No
P-versus-NP conclusion follows.

### The disjoint reconstruction payload realizes the full cross-block product

The off-diagonal omitted payload now has an exact formula.
`disjointVariableTypedIncidenceWitnesses_crossGate` proves that for two distinct active gates,
one colored cell is exactly the corresponding Cartesian live-occurrence enumerator filtered only
by disjoint variable support.  There is no additional survivor, orientation, or sparsity filter:
the three signed statistics merely route each pair to its unique matrix coordinate.
The parameterized theorem
`exists_mem_disjointVariableTypedIncidenceWitnesses_of_crossGate` makes the consequence explicit:
every disjoint pair of canonical live occurrences from any two distinct active gates appears in
the omitted payload at its determined signed-type coordinate.

The existing two-polarity family of two disjoint width-two blocks provides a kernel-evaluated
stress test.  At the fully live root with fuel four and residual depth one, all four one-clause
gates are active.  Each of the two gates on the first block is disjoint from each of the two gates
on the second block, in both ordered directions.  The theorem
`localDisjointPairPolarityFamily_total_disjoint_payload` proves that the sum over all 720 colored
coordinates is exactly eight, namely the complete `2 * 2 * 2` ordered cross-block product.  The
same-block pairs are retained by the sparse graph and diagonal one-occurrence cells contribute
nothing.

This closes the proposed stress test negatively: shared-variable components do not compress the
complete typed-pair certificate in general.  Exact reconstruction restores every omitted
cross-component Cartesian pair, so families with many disjoint active blocks recreate a
quadratic block-pair charge.  Developing a connected-component API for this edge notion would
therefore add notation without improving the worst-case alphabet.

Direct Lean elaboration passed both new theorems and continued beyond line 8,000 before the
known heavy tail hit a four-minute timeout; no full-file completion or printed-axiom result is
claimed.  `git diff --check` passes, and no `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was introduced.  Existing counterexamples and failed routes remain intact.

The precise next frontier is to abandon shared-variable components as a general compression
route and ask whether the certificate can charge only witnesses actually used by the canonical
common-query trunk.  The first defensible test is an ordered first-conflict/first-query selector:
define a deterministic selected occurrence pair for each non-shallow gate pair, prove whether
the selected data reconstructs the queried prefix, and measure its multiplicity on the existing
matched-profile counterexamples.  If reconstruction again requires all unselected pairs, record
that failure before trying another locality quotient.  No P-versus-NP conclusion follows.

### Canonical root-query selection does not determine common-trunk cost

The first deterministic selector test is now formalized without using a support proxy.
`activeCanonicalFirstQueryProfile` records, for every residually deep indexed gate, the variable
chosen by the first free literal of its actual first active term.  Already-shallow gates record
`none`.  `activeCanonicalFirstQueryMultiplicity` counts the exact indexed multiplicity of any
selected variable.

The existing normalized matched-profile counterexample defeats this root selector.  In both
`typedPairLowCostFamily` and `typedPairHighCostFamily`, both active gates canonically select
coordinate zero at the fully live root.  Thus the complete indexed selector functions are equal,
and coordinate zero has multiplicity exactly two in each family.  Nevertheless the previously
proved exact common-query costs remain one for the low-cost family and two for the high-cost
family.  The capstone
`canonicalRootQuerySelector_does_not_determine_commonQueryCost` packages these four facts.

This is a narrow negative result: charging one actual root query per active gate avoids the full
Cartesian occurrence payload, but it loses the branch-conditioned evolution that creates the
second common query in the high-cost family.  Root first-query identities and their multiplicity
therefore cannot reconstruct even the length-two queried prefix in general.

The finite selector evaluation was independently elaborated in a minimal scratch module, and
direct elaboration of the full bridge reached the new section.  The initial whole-function
decision proof was replaced by gatewise finite reduction and a multiplicity proof derived from
the resulting profile equality.  `git diff --check` passes, and no `sorry`, `admit`, custom
axiom, `unsafe`, or `native_decide` was introduced.  Existing counterexamples and failed routes
remain in place.

The precise next frontier is to define the branch-conditioned selector stream: after the chosen
root variable is assigned, recompute the active gates' canonical first queries and retain only
the first newly forced conflict/query at each step.  Prove whether the stream plus branch bits
reconstructs the common queried prefix, then evaluate its length and per-variable multiplicity on
the same low/high normalized pair.  If reconstruction needs the full vector of every gate's
successor query at each branch, record the resulting `G * d` charge before attempting a count.
No P-versus-NP conclusion follows.

### One selected successor query separates the matched root-profile families

The first branch-conditioned selector level is now formalized.  `activeCanonicalFirstFamilyQuery`
scans the indexed canonical root-query profile in gate order and retains only its first present
query.  `branchConditionedCanonicalQueryStep` records that selected root query and recomputes the
same single selection after each Boolean value of the root variable.  It therefore stores one
chosen query per reached branch, rather than the complete `G`-entry successor vector.

Exact evaluation on the existing normalized matched pair is decisive at this level.  Both
families select coordinate zero at the root.  The low-cost family then selects no successor on
either branch, matching its depth-one common trunk.  The high-cost family selects coordinate two
after `0 := false` and coordinate one after `0 := true`, matching the need for a second common
query.  `branchConditionedCanonicalQueryStep_separates_typedPairFamilies` packages the contrast:
the indexed root profiles are identical, while the one-step branch-conditioned selectors differ.

This rules out the strongest immediate negative forecast on the current counterexample: its
branch evolution does not require storing all gates' successor queries.  One gate-order selected
query per branch suffices to distinguish the one-query and two-query costs.  This is not yet a
reconstruction theorem, and a full selector tree may still have exponential branch payload or
lose information when the first selected gate is not compatible with a globally shallow trunk.

Direct elaboration passed all new definitions and theorems and continued beyond line 6,900 before
the known heavy tail was deliberately stopped; no full-file completion or printed-axiom result is
claimed.  The quantitative-iteration regression build passed with 8,451 jobs.  `git diff --check`
passed, and no `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was introduced.
Existing counterexamples and failed compression routes remain intact.

The precise next frontier is to define the recursive branch-conditioned selector tree, prove its
queries reconstruct a valid `CommonTree` whose leaves make every gate residually shallow, and
bound its depth by the selected-stream length.  The critical audit is then its certificate count:
determine whether branch sharing yields a prefix code charged per realized path, or whether
recording the full selector tree incurs `2^d` nodes.  Preserve a counterexample if the greedy
gate-order selector can exceed optimal common-trunk depth.  No P-versus-NP conclusion follows.

### Recursive selector accounting separates path cost from stored-tree cost

The branch-conditioned selector is now recursively materialized as
`branchConditionedCanonicalSelectorTree`.  At each state it stores only the first active
gate-order query, fixes that variable separately on the false and true branches, and recomputes
the selector from the resulting restriction.  Its leaf payload is exactly the accumulated
restriction.  No semantic optimality or leaf-shallowness claim is built into the definition.

Two unconditional structural bounds now isolate the accounting issue.  The selector tree has
depth at most its recursion budget `d`, so every realized assignment sees at most `d` selected
queries.  In contrast, the newly defined `CommonTree.queryNodeCount` is bounded only by
`2^d - 1` for the complete stored certificate.  Thus realized-path scale and explicit-tree scale
are genuinely different resources; branch conditioning alone does not supply a compact shared
representation.

The existing matched pair already realizes the distinction at the first nontrivial depth.  With
budget two, the low-cost family stops at depth one and stores one query node.  The high-cost
family has depth two and stores all three query nodes: root query zero, successor two on the false
branch, and successor one on the true branch.  This is an exact finite evaluation, not merely the
general upper bound.

An isolated elaboration of the generic node-count induction passed.  Direct elaboration of the
full bridge then passed the new definitions, structural theorems, and exact finite evaluations,
continuing beyond line 7,700 before the known expensive tail was deliberately stopped.  The
quantitative-iteration regression build passed with 8,451 jobs.  Existing counterexamples and
failed compression routes remain intact.  `git diff --check` passes, and no `sorry`, `admit`,
custom axiom, `unsafe`, or `native_decide` was introduced.

The precise next frontier is semantic: prove a stopping-to-`CommonShallowAt` bridge for this
specific greedy tree, including root extension and leaf agreement, and determine whether every
family admitting a depth-`d` common trunk makes the greedy selector stop within comparable depth.
If not, preserve the smallest counterexample and replace gate-order greediness by a selector with
a proved winning-query invariant.  Only after that should the counting argument decide whether a
realized-path encoding can avoid paying for the explicit `2^d` tree.  No P-versus-NP conclusion
follows.

### Greedy stopping now has exact common-shallow semantics

The recursive selector's semantic interface is now proved rather than assumed.
`activeCanonicalFirstFamilyQuery_eq_none_iff` shows that the gate-order selector returns `none`
exactly when every indexed canonical tree has depth at most the requested residual threshold.
The proof closes the apparent `activeTermLit = none` corner case: the new theorem
`canonicalDT_depth_eq_zero_of_activeTermLit_eq_none` proves that this can only leave a constant
canonical tree, at every fuel budget.

Every selected coordinate is also proved live in the current restriction by
`activeCanonicalFirstFamilyQuery_var_free`.  Induction on the recursion budget then gives
`branchConditionedCanonicalSelectorTree_run_spec`: every realized selector leaf extends the root
restriction and agrees with the assignment that reaches it.  Consequently
`commonShallowAt_of_branchConditionedCanonicalSelectorTree_stops` packages any budget whose
reached leaves all stop into a genuine `CommonShallowAt` certificate of the same depth.  No
semantic weakening or arbitrary leaf payload is used.

The new theorem section elaborated independently in a focused scratch module.  Direct elaboration
of the full bridge passed the new definitions and proofs and continued beyond line 8,400 before
the known expensive tail was deliberately stopped; no whole-file completion claim is made.  The
quantitative-iteration regression then passed with 8,451 jobs.  Existing counterexamples and
failed compression routes remain intact.  `git diff --check` passes, and no `sorry`, `admit`,
custom axiom, `unsafe`, or `native_decide` was introduced.

The precise next frontier is now purely competitive: compare the first budget at which this
gate-order greedy selector stops with the minimum `CommonShallowAt` trunk depth.  The smallest
defensible test is the already exhaustive 81-state two-pair family, using its flexible-game cost
as the exact semantic optimum.  Prove equality there or preserve the first state where greedy is
strictly worse; then generalize only if a winning-query invariant emerges.  The exponential
stored-tree count remains a separate later obstacle.  No P-versus-NP conclusion follows.

### The greedy selector is pointwise optimal on the exhaustive two-pair family

The first stopping budget of the specific gate-order selector is now executable.  The new
`twoPairGreedySelectorStops` recurrence follows exactly one
`activeCanonicalFirstFamilyQuery` at each nonterminal state and requires both Boolean children
to stop.  This avoids both an enumeration of total assignments and the explicit `2^d` selector
tree.  `twoPairGreedySelectorCost` records its first stopping budget in the complete local range
zero through three, and `twoPairGreedySelectorStops_three_code` checks that the final fallback
really stops on all 81 restrictions.

The competitive audit found no counterexample.  The kernel-checkable statement
`twoPairGreedySelectorCost_eq_flexibleQueryCost_code` compares the greedy and flexible costs
pointwise on every base-three state, rather than merely comparing histograms.  The decoding
surjectivity theorem then gives the presentation-free equality for every four-coordinate
restriction.  Both costs have the exact distribution `(56,16,8,1)` at budgets `(0,1,2,3)`.
Thus gate-order greediness is exactly optimal on this family, including the unique cost-three
fully live root.  This finite positive result does not establish a general competitive theorem.

The local definitions and comparison were independently mirrored by a read-only Python
evaluation, which returned no unequal state and the same histogram.  `git diff --check` passes,
and a source scan finds no newly introduced `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide`.  The current execution environment does not expose a Lean or Lake executable,
so fresh elaboration of the added declarations is not claimed in this step.

The precise next frontier is to prove, generically in the gate family, that the executable
stopping recurrence is equivalent to universal stopping of
`branchConditionedCanonicalSelectorTree` on all root-compatible assignments.  Composing that
equivalence with `commonShallowAt_of_branchConditionedCanonicalSelectorTree_stops` will turn the
finite cost equality into a fully connected semantic optimality theorem for the two-pair family.
Only then should one extract the winning-query invariant suggested by the 81-state equality and
test it on the next-smallest normalized width-two families.  The exponential stored-tree count
remains separate.  No P-versus-NP conclusion follows.

### Executable greedy stopping is now connected to realized-tree semantics

The greedy stopping recurrence is now generic in the indexed gate family rather than existing
only as a two-pair evaluator.  `branchConditionedCanonicalSelectorStops` follows the same
gate-order query and Boolean children as `branchConditionedCanonicalSelectorTree`, but computes a
Boolean conjunction without exposing the complete stored tree.

The theorem `branchConditionedCanonicalSelectorStops_eq_true_iff` proves exact equivalence between
that executable recurrence and universal stopping of the realized selector tree over every total
assignment compatible with the root restriction.  Both directions are substantive at the
interface: the forward direction routes assignments into the corresponding fixed child, while
the reverse direction transports each child-compatible assignment back through the live root
query.  The zero-budget converse uses the canonical `getD` completion, so it does not assume the
compatible-assignment set is inhabited without proof.

`commonShallowAt_of_branchConditionedCanonicalSelectorStops` composes the equivalence with the
existing run-specification and shallow-leaf bridge.  The former two-pair recurrence is now a
specialization of the generic predicate, and `twoPairCommonShallowAt_greedySelectorCost` proves
that its computed first stopping budget supplies an actual `CommonShallowAt` certificate.  Thus
the exhaustive equality with `twoPairFlexibleQueryCost` is connected to the semantic certificate
layer rather than remaining a detached finite calculation.

Direct Lean elaboration passed the new generic recurrence, both directions of the equivalence,
the common-shallow corollary, the specialized cost certificate, and continued beyond line 8,600.
The run was then stopped by its five-minute bound in the known expensive tail, so no whole-file
completion or printed-axiom result is claimed.  `git diff --check` passes, and a scan of the added
source finds no `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide`.  Existing
counterexamples and failed compression routes remain intact.

The precise next frontier is to extract a structural winning-query invariant from the two-pair
equality and test it on the next-smallest normalized width-two families.  The first useful audit
should enumerate three two-literal terms (and both polarities where relevant), compare greedy
stopping cost with the flexible semantic optimum pointwise, and preserve the first strict gap if
one exists.  A positive finite result should only be generalized after identifying an invariant
that explains the greedy choice.  The exponential stored-tree count remains a separate later
obstacle.  No P-versus-NP conclusion follows.

### The two-pair greedy selector is now semantically optimal

`twoPairFlexibleQueryCost_le_of_commonShallowAt` proves that the executable flexible-game cost is
no larger than the depth of any semantic `CommonShallowAt` certificate.  The proof uses the
verified game/semantics equivalence and audits all four possible first-winning budgets, including
the depth-three fallback.

Combining this lower bound with `twoPairGreedySelectorCost_eq_flexibleQueryCost` gives
`twoPairGreedySelectorCost_le_of_commonShallowAt`.  Together with the existing attainability
theorem `twoPairCommonShallowAt_greedySelectorCost`, the gate-order selector therefore has exact
minimum semantic common-trunk depth on every one of the 81 restrictions.

Direct Lean elaboration passed the new declarations and continued beyond line 8,500 before the
four-minute whole-file timeout.  No error occurred in or after the edited section; the timeout is
not claimed as a whole-file build success.  `git diff --check` passes, and no `sorry`, `admit`,
custom axiom, `unsafe`, or `native_decide` was introduced.

The next defensible step remains the three-term or four-gate normalized width-two audit.  It must
either expose a strict greedy/semantic gap or identify a structural winning-query invariant.
The exponential stored-tree count and independent SAT-density/fiber obstruction remain open.
No P-versus-NP conclusion follows.

### Three terms already give a strict greedy/semantic gap

The next-smallest normalized width-two audit found a strict counterexample on three variables.
The positive gate has the ordered clauses

```text
(¬0 ∧ ¬1), (0 ∧ ¬1), (1 ∧ ¬2)
```

and the indexed family consists of this gate and its termwise-negated polarity.  All three
clauses are distinct and each uses two distinct variables, so duplicate normalization does not
remove the example.

`threeTermGreedyGapFamily_exact_semantic_cost_one` proves that the exact semantic common-trunk
cost at the fully live root is one: querying coordinate one makes both polarities residual-depth
one on both branches, while the root itself has canonical depth three.  In contrast,
`threeTermGreedyGapFamily_greedy_stops_exactly_two` computes that the gate-order selector fails to
stop with budget one and succeeds with budget two.  It chooses coordinate zero from the first
active clause, and both resulting branches still require coordinate one.

Thus the pointwise optimality of the exhaustive 81-state two-pair family is accidental rather
than evidence for a general gate-order winning-query invariant.  The generic semantic bridge
remains valid, but its current deterministic query policy can be a factor two worse even in this
minimal three-term test.

Direct Lean elaboration passed every new definition and theorem and continued well beyond the
edited section before the six-minute whole-file timeout in the known expensive tail.  The
counterexample was also found and independently evaluated by exhaustive read-only search over
ordered normalized three-clause width-two gates on three variables.  `git diff --check` passes,
and no `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was introduced.  Existing
counterexamples and failed routes remain intact.

The precise next frontier is to replace gate-order first-active selection with a query rule that
can recognize the winning middle coordinate in this example.  The highest-information next test
is a minimax selector: at each state choose the live variable minimizing the maximum greedy
stopping cost of its two children, then determine whether its choice admits a compact structural
certificate or merely reimplements the full flexible game.  The exponential stored-tree count
remains a separate obstacle.  No P-versus-NP conclusion follows.

### One-step greedy rollout repairs the minimal counterexample

The first minimax-style test is now executable and kernel-checked.  The generic bounded function
`cappedGreedyStoppingCost` returns the first budget, through a supplied cap, at which the existing
gate-order recurrence stops.  `greedyRolloutQueryScore` scores a live root coordinate by the
maximum of those capped costs on its two Boolean children.  This is deliberately only a one-step
rollout heuristic: no recursive optimality or equivalence with the flexible semantic game is
assumed.

On the preserved normalized three-term counterexample, with child cap one, the exact score vector
for coordinates zero, one, and two is

```text
(1, 0, 1).
```

Thus the winning middle coordinate is a strict minimizer, while the old gate-order selector still
chooses coordinate zero.  `firstZeroGreedyRolloutQuery` selects coordinate one, and
`threeTermGreedyGapFamily_rollout_children_stop` independently computes that both children of
this query are stopped at budget zero.  The rollout rule therefore realizes the known depth-one
semantic optimum on this counterexample without calling the specialized flexible-game search.

An explicit five-minute Lean run elaborated all new declarations and continued beyond line 8,700
without errors before timing out in the known expensive tail; this is not claimed as a whole-file
build.  `git diff --check` passes, and no `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was introduced.  The strict greedy counterexample remains intact.

The precise next frontier is an exhaustive normalized three-term audit of the rollout rule across
all restrictions: compare its recursively realized stopping cost with the flexible semantic
optimum, and preserve the first strict gap if one exists.  A positive finite result is useful only
if its score admits a compact certificate that avoids evaluating both child games at every node;
otherwise rollout merely relocates the exponential flexible-game computation.  The stored-tree
cost remains a separate obstacle.  No P-versus-NP conclusion follows.

### Rollout is semantically optimal on all 27 states of the minimal counterexample family

The proposed restriction-wide audit is now complete for the preserved normalized three-term
family.  `minimumGreedyRolloutQuery` filters fixed coordinates before applying `List.argmin`; this
matters once scores above zero are compared, because the earlier fixed-coordinate sentinel can
tie a live coordinate whose two child searches both exhaust their cap.  The zero-score root test
was unaffected, but it was not a sound general minimizer without this filtering step.

`branchConditionedGreedyRolloutStops` recursively reapplies the one-step policy: at every
nonterminal state it minimizes the capped gate-order greedy child cost, queries that coordinate,
and requires both rollout children to stop.  Base-three coding enumerates all 27 restrictions of
the three variables.  The kernel-checked theorem `threeTermGreedyRolloutStops_one_code` proves
that every one of those states stops within one rollout query.

This finite result is connected to semantics, not left as an evaluator-only observation.
`commonShallowAt_of_branchConditionedGreedyRolloutStops_one` turns any successful one-query
rollout into a genuine `CommonShallowAt` certificate.  Consequently
`threeTermCommonShallowAt_greedyRolloutCost` proves attainability of the computed cost on every
restriction.  Conversely, `threeTermGreedyRolloutCost_le_of_commonShallowAt` proves that no
semantic common trunk can be shallower.  The reason the lower bound is compact here is specific:
the exhaustive cost range is only zero or one, so the existing zero-depth root characterization
rules out the only possible strict improvement.  This does not establish recursive optimality at
depth two or beyond.

Direct Lean elaboration passed all new definitions, the 27-state decision theorem, the generic
one-query semantic bridge, and both exact-optimality theorems, then continued beyond line 8,300
without errors before the expensive tail was stopped.  No full-file completion is claimed in
this step.  Existing counterexamples and failed routes remain intact.  `git diff --check` passes,
and no `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was introduced.

The precise next frontier is the first family or restriction whose semantic optimum is at least
two.  Exhaustively compare recursively realized rollout with the exact flexible game there and
preserve the first strict gap.  A positive result must also audit whether the argmin score has a
certificate smaller than evaluating both capped greedy children for every live coordinate;
otherwise the selector is semantically useful but merely relocates exponential search.  The
stored-tree and independent density/fiber obstructions remain open.  No P-versus-NP conclusion
follows.

### Recursive rollout remains optimal through semantic depth three on the two-pair gadget

The existing normalized two-pair gadget supplies the missing deeper test without introducing a
new family.  Its 81 restrictions have exact semantic-cost histogram `(56,16,8,1)` at costs
zero through three, so nine states genuinely exercise depth at least two and the fully live state
has exact cost three.

`twoPairGreedyRolloutStops` recursively reapplies the fixed-coordinate-safe rollout argmin with
child cap three.  Its associated cost keeps four as an explicit failure sentinel rather than
silently treating the known depth-three bound as success.  The kernel-checked theorem
`twoPairGreedyRolloutCost_eq_flexibleQueryCost_code` proves pointwise equality with the exact
flexible-game cost on all 81 restrictions.  `twoPairGreedyRolloutStops_cost_code` separately
proves that the computed budget actually stops, so the failure sentinel is unreachable.

The finite computation is connected back to semantics in both directions.
`twoPairCommonShallowAt_greedyRolloutCost` proves that the rollout cost is attained by a genuine
`CommonShallowAt` trunk, using the independently proved flexible-game soundness;
`twoPairGreedyRolloutCost_le_of_commonShallowAt` proves it is no larger than any semantic trunk
depth.  Thus recursive rollout is semantically optimal on this particular normalized family
through depth three, not only on the earlier zero/one family.

This is still finite evidence, not a compact general selector certificate.  The definition of
the argmin evaluates the capped greedy stopping recurrence on both children of every live
coordinate.  The exhaustive equality therefore does not show that rollout avoids exponential
child search; it may only relocate it.

Direct Lean elaboration passed all new definitions and theorems and continued beyond line 8,400
without errors before the expensive tail was stopped.  This is not claimed as a whole-file build.
`git diff --check` passes, and no `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was
introduced.  Existing counterexamples and failed routes remain intact.

The precise next frontier is an exhaustive normalized three-term width-two audit restricted to
states whose flexible semantic optimum is at least two.  Compare recursive rollout pointwise,
preserve the first strict gap if one exists, and for every positive case record whether the
winning argmin can be certified from a bounded local incidence profile rather than by evaluating
both capped child recurrences for every live coordinate.  The stored-tree and independent
density/fiber obstructions remain open.  No P-versus-NP conclusion follows.

### A three-term path gives a strict recursive-rollout gap

The proposed normalized three-term audit found a strict gap on four coordinates.  The positive
gate is the ordered path

```text
(¬0 ∧ ¬1), (¬1 ∧ ¬2), (¬2 ∧ ¬3),
```

and the indexed family contains this gate and its termwise-negated polarity.  The clauses are
distinct and every clause uses two distinct variables, so duplicate normalization leaves the
example intact.

`threeTermPathRolloutGapFamily_commonShallowAt_two` constructs a genuine depth-two common trunk:
query coordinates one and two, after which both polarities have residual canonical depth at most
one on all four branches.  In contrast,
`threeTermPathRolloutGapFamily_rollout_stops_exactly_three` computes that recursive rollout with
child cap four fails at budget two and succeeds at budget three.  The combined theorem
`threeTermPathRolloutGapFamily_strict_competitive_gap` therefore refutes semantic optimality of
the rollout rule, independently of whether the exhibited depth-two trunk is the unique optimum.

The counterexample was the first gap found by systematic read-only enumeration of ordered
normalized three-clause width-two gates on four variables, then restated and checked inside Lean.  It
preserves the earlier gate-order gap and the positive two-pair rollout audit: those equalities
were family-specific rather than a general minimax invariant.

A bounded five-minute Lean elaboration passed the new declarations and continued beyond line
9,000 with no errors before timing out in the known expensive tail; this is not claimed as a
whole-file build.  `git diff --check` passes.  No `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was introduced.

The precise next frontier is no longer to seek a universal proof for greedy rollout.  Audit why
the path's two middle coordinates beat the endpoint chosen by the child-greedy score, and test a
bounded local path/incidence certificate on normalized three-term families.  Preserve the next
collision: two states with the same proposed local certificate but different winning middle
queries or semantic costs.  Any replacement selector must avoid evaluating both full child
recurrences for every live coordinate.  The stored-tree and independent density/fiber
obstructions remain open.  No P-versus-NP conclusion follows.

### The path failure is a rollout-score tie repaired by live incidence

The exact root audit sharpens the preceding diagnosis.  The child-greedy rollout score vector on
the preserved four-coordinate path is

```text
(2, 2, 2, 2).
```

Thus the endpoint is not a strict score winner: `List.argmin` chooses coordinate zero only because
all four candidates collide and zero is first.  The kernel-checked theorem
`threeTermPathRolloutGapFamily_root_score_collision` records both the vector and the selected
endpoint.

A bounded alternative now exists as executable generic data.
`liveLiteralIncidenceMultiplicity` counts currently free literal occurrences of each variable
across the indexed family, and `maximumLiveIncidenceQuery` selects the first live maximum.  It
does not evaluate either child stopping recurrence.  On the normalized path its root profile is

```text
(2, 4, 4, 2),
```

so it chooses middle coordinate one.  After fixing coordinate one to either Boolean value, the
same rule chooses coordinate two.  These two facts, combined with the already proved
`threeTermPathRolloutGapFamily_commonShallowAt_two`, reproduce the winning depth-two trunk on
this counterexample using only the live incidence profile.

This is a positive path-local certificate, not a general selector theorem.  Occurrences are
counted with multiplicity deliberately; duplicate normalization is a separate interface and the
preserved example already satisfies it.  The precise next frontier is an exhaustive normalized
three-term width-two audit of this maximum-live-incidence selector.  Preserve the first collision
between equal incidence profiles and different winning queries or semantic costs; if no collision
occurs at this size, test the first four-term family.  A useful replacement must also admit a
compact semantic soundness argument beyond finite enumeration.  The stored-tree and independent
density/fiber obstructions remain open.  No P-versus-NP conclusion follows.

### Maximum live incidence has a strict normalized three-term gap

The requested audit found a counterexample without advancing to four terms.  Its positive gate is

```text
(¬0 ∧ ¬1), (¬0 ∧ 1), (¬2 ∧ ¬3),
```

and the indexed family contains this gate and its termwise-negated polarity.  Both clause lists
are duplicate-free and every clause uses two distinct coordinates.

The exact root incidence profile is `(4,4,2,2)`.  The deterministic maximum-incidence rule first
chooses coordinate zero and, on either Boolean child, next chooses coordinate one.  Nevertheless,
the explicit trunk querying coordinates zero and two leaves both polarities at canonical residual
depth at most one on every branch.  The kernel-checked recurrence records the strict gap:
maximum-live-incidence fails at budget two and first stops at budget three.

This refutes the proposed universal selector at the smallest family size under audit.  The failure
also identifies what incidence omits: it ranks repeated participation above component coverage.
The earlier path result remains useful as a positive local certificate, but cannot support a
general theorem even for normalized three-term width-two families.

The precise next frontier is to test the smallest bounded certificate that sees clause-component
coverage in addition to live incidence—for example, marginal coverage of still-active terms—and
preserve the first collision against exact semantic cost.  Any proposed rule must remain local and
avoid evaluating both recursive child games.  The stored-tree and independent density/fiber
obstructions remain open.  No P-versus-NP conclusion follows.

### Fully-live term coverage repairs incidence but still collides at the root

`fullyLiveTermCoverageMultiplicity` counts clauses containing a coordinate only while every
literal in that clause remains free.  This bounded rule repairs the preceding incidence
counterexample: after querying coordinate zero, the touched two-clause component scores zero and
the independent component forces coordinate two, so the selector stops at budget two.

The repair is not universal.  The adjacent normalized family

```text
(¬0 ∧ ¬1), (0 ∧ ¬1), (¬2 ∧ ¬3)
```

together with its termwise-negated polarity has the same root coverage vector `(4,4,2,2)`.  The
rule chooses zero and then two on both children, but fails at budget two and first stops at three.
Querying coordinates one and two gives a genuine depth-two `CommonShallowAt` certificate.  Thus
the two families collide under the entire unsigned root certificate while requiring different
tied first coordinates.  Both are clause-duplicate-free and use distinct variables per clause.

A bounded five-minute Lean run elaborated beyond line 9,200, well past every new declaration,
without errors before timing out in the known expensive tail; this is not a full-file build claim.
`git diff --check` passes, and no `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was
introduced.  All earlier positive examples and counterexamples remain in place.

The precise next frontier is the least polarity-sensitive local refinement separating this
collision—for example, constant versus mixed polarity of each coordinate across fully live
terms—followed immediately by the same normalized three-term width-two audit.  Preserve the first
collision against exact semantic cost.  A viable selector must remain local and avoid evaluating
both recursive child games.  The stored-tree and independent density/fiber obstructions remain
open.  No P-versus-NP conclusion follows.

### Within-gate polarity concentration separates the unsigned collision

The least polarity-sensitive refinement now has a generic executable definition.
`fullyLiveSignedTermCoverageMultiplicity` counts, inside one indexed gate, fully-live clauses
containing a coordinate with a specified sign.  `fullyLivePolarityConcentrationMultiplicity`
takes the larger signed count per gate and sums those maxima across the indexed family.  This is
invariant under adjoining the De Morgan polarity, but unlike the preceding unsigned score it
distinguishes a coordinate whose sign is constant within a gate from one whose sign is mixed.
It remains local and evaluates no child stopping game.

On the two preserved normalized families, the formerly identical unsigned profile `(4,4,2,2)`
splits exactly as follows:

```text
incidence-gap family:  (4,2,2,2), selecting coordinate 0
coverage-collision:    (2,4,2,2), selecting coordinate 1
```

`branchConditionedMaximumFullyLivePolarityConcentrationStops` recursively applies this selector.
The kernel-checked theorem `threeTermCoverageCollision_polarity_selector_repairs_both` computes
that it stops within budget two on both families, matching their already proved depth-two
`CommonShallowAt` certificates.  This repairs the exact unsigned collision; it is not evidence of
a universal selector theorem.

A bounded five-minute Lean elaboration reached line 9,384, beyond both new decision theorems at
lines 8,062–8,084, with warnings only before timing out in the known expensive tail.  This is not
a full-file build claim.  `git diff --check` passes, and no `sorry`, `admit`, custom axiom,
`unsafe`, or `native_decide` was introduced.  All earlier positive examples, counterexamples, and
failed routes remain intact.

The precise next frontier is the promised exhaustive normalized three-term width-two audit of
within-gate polarity concentration across restrictions.  Preserve the first collision against
exact flexible semantic cost, ideally between families with the same concentrated profile but
different winning queries.  If it survives this size, advance to four terms.  Any useful selector
still needs a compact semantic soundness argument and must avoid recursive child-game evaluation;
the stored-tree and independent density/fiber obstructions remain open.  No P-versus-NP
conclusion follows.

### Polarity concentration already has a strict three-term gap

The systematic normalized three-term width-two audit refutes the polarity-concentration selector
before any four-term search is needed.  Its first strict witness (in the audit script's explicit
lexicographic enumeration) is the positive gate

```text
(¬0 ∧ ¬1), (¬0 ∧ ¬2), (¬0 ∧ 2),
```

paired with its termwise-negated polarity.  Both gate lists are clause-duplicate-free and every
clause uses two distinct coordinates.  The root concentration profile is `(6,2,2)`, so the local
rule strictly prefers coordinate zero.  But querying coordinate two alone leaves the canonical
depth of both polarities at most one on both branches.  The selector therefore needs two queries
where the flexible semantic game needs only one.

`threeTermPolarityConcentrationGapFamily_commonShallowAt_one` gives the explicit semantic trunk,
while `threeTermPolarityConcentrationGapFamily_selector_stops_exactly_two` kernel-checks failure at
budget one and success at budget two.  Their combination is recorded by
`threeTermPolarityConcentrationGapFamily_strict_competitive_gap`.  The reproducible audit is
`scripts/multiswitching_polarity_selector_audit.py`; it mirrors the Lean canonical-depth and
selector recurrences and found this witness after 142 ordered gates and 11,422 restricted states.

A bounded five-minute Lean elaboration reached beyond line 9,400, past all new declarations, with
warnings only before timing out in the known expensive tail; this is not a full-file build claim.
`git diff --check` passes, and no `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was
introduced.  Earlier repairs, counterexamples, and failed routes remain preserved.

The precise next frontier is not another scalar occurrence score.  This witness shows that a
dominant common literal can be irrelevant to the minimax stopping objective, whereas querying a
lower-frequency complementary pair collapses two terms simultaneously.  Audit the smallest local
certificate that records complementary-term cancellation (for example, signed residual pairs
after deleting their shared literals), and preserve the first collision against exact flexible
cost.  Any replacement must avoid evaluating full child recurrences; the stored-tree and
independent density/fiber obstructions remain open.  No P-versus-NP conclusion follows.

### Complementary residual-pair priority fails on the fifth normalized gate

The requested pairwise audit is now executable and already refutes the proposed refinement.
For each live coordinate it counts unordered pairs of fully-live width-two clauses in one gate
that share one identical signed literal and have opposite signs of the coordinate as their two
residual literals.  The deterministic selector maximizes this count, using within-gate polarity
concentration only as a fallback.  It remains local and never evaluates either child recurrence.

The first strict witness in the explicit ordered audit is

```text
(¬0 ∧ ¬1), (¬0 ∧ 1), (0 ∧ ¬2),
```

paired with its termwise-negated polarity.  Its complementary residual-pair profile is
`(0,2,0)` and its concentration profile is `(4,2,2)`, so pair priority strictly selects coordinate
one.  But coordinate zero is the unique one-query winner: fixing it leaves both polarities at
canonical residual depth at most one on both branches.  The pair selector first stops after two
queries.  The third clause is the essential obstruction: its shared coordinate has the opposite
sign, so the sign distribution of the supposedly deleted common literal decides the minimax
value.

`fullyLiveComplementaryResidualPairMultiplicity` and
`maximumComplementaryResidualPairQuery` formalize the generic local certificate in Lean.
`threeTermComplementaryPairGapFamily_commonShallowAt_one` supplies the explicit semantic trunk,
and `threeTermComplementaryPairGapFamily_selector_stops_exactly_two` kernel-checks the strict
two-versus-one gap.  The witness remains normalized: both polarity lists are duplicate-free and
no clause repeats a coordinate.

The Python audit reproduced the earlier concentration witness and found this new witness after
five ordered gates and 325 restricted states.  A long Lean elaboration passed the new declarations
and continued beyond line 9,900 with warnings only; it was manually stopped in the known expensive
tail, so this is not a full-file build claim.  `git diff --check` passes, and no `sorry`, `admit`,
custom axiom, `unsafe`, or `native_decide` was introduced.  All earlier failed selectors and
counterexamples remain preserved.

The precise next frontier is to stop ranking cancellation motifs independently.  The smallest
plausible refinement must retain the signed incidence of the deleted shared literal into the
remaining clauses—for example, a two-coordinate signed motif recording both the complementary
residual variable and the shared variable's external opposite-sign incidence—and immediately
audit it on the same normalized three-term domain.  Preserve the first collision against exact
flexible cost.  A useful replacement still needs a compact semantic argument without recursive
child-game evaluation; the stored-tree and independent density/fiber obstructions remain open.
No P-versus-NP conclusion follows.

### External shared-sign incidence repairs the pair witness but fails on a disconnected component

The proposed signed two-coordinate refinement is now executable.  For each complementary
residual pair, it retains the pair's shared coordinate and counts it only when a distinct
fully-live clause occurrence in the same gate contains the opposite sign of that shared
coordinate.  The selector gives this external-opposition count strict priority, then falls back
to complementary residual-pair count and within-gate polarity concentration.  It remains local
and evaluates no recursive child game.

This motif repairs the immediately preceding witness.  On

```text
(¬0 ∧ ¬1), (¬0 ∧ 1), (0 ∧ ¬2)
```

its external shared-pair profile is `(2,0,0)`, so it selects the unique one-query winner zero and
stops at budget one.  However, the exhaustive normalized three-term audit finds a strict gap
after 31 ordered gates and 2,431 restricted states:

```text
(¬0 ∧ ¬1), (¬0 ∧ 1), (¬2 ∧ ¬3).
```

This is the already preserved incidence-gap family.  Its external profile is `(0,0,0,0)` and
its complementary residual-pair profile is `(0,2,0,0)`, so the fallback strictly selects
coordinate one.  The selector first stops after three queries, while the existing explicit trunk
querying coordinates zero and two proves semantic cost at most two.  The audit's exact minimax
calculation gives cost two, with root winning queries zero, two, and three.  Thus the extra signed
incidence sees the third-clause interaction when it is attached to the cancellation component,
but still fails to price coverage of a disconnected component.

`fullyLiveExternallyOpposedSharedPairMultiplicity` formalizes the occurrence-indexed motif;
`maximumExternallyOpposedSharedPairQuery` and its recursive stopping predicate formalize the
selector.  Kernel-checked `decide` theorems record both the repair and the strict three-versus-two
gap, reusing `threeTermIncidenceGapFamily_commonShallowAt_two` for the semantic certificate.  A
bounded five-minute Lean elaboration passed all new declarations and continued beyond line 9,600
with warnings only before timing out in the known expensive tail; this is not a full-file build
claim.  The Python audit reproduces all three successive counterexamples.

The precise next frontier is a component-aware certificate rather than another independently
ranked signed motif.  The smallest plausible step is to combine cancellation structure with the
marginal reduction in the number of live clause-support components caused by a query, then audit
that rule on the same normalized three-term domain.  Preserve the attached and disconnected
counterexamples as a matched test pair.  Any useful replacement must remain local and avoid full
child stopping recurrences; the stored-tree and independent density/fiber obstructions remain
open.  No P-versus-NP conclusion follows.

### Raw component marginal repairs the root but fails during its own rollout

The proposed component-aware certificate is now executable.  For each gate it forms the active
nonempty live support of every nonfalsified clause (and assigns no residual supports to a gate
that is already satisfied), closes support intersection transitively, and counts the resulting
components.  A live query is ranked first by the summed decrease in this component count over its
two immediate Boolean children.  External shared-sign incidence, complementary residual pairs,
and polarity concentration remain lexicographic tie-breakers.  This inspects two local residual
incidence graphs but never evaluates a child stopping recurrence.

At the root of the preserved disconnected witness

```text
(¬0 ∧ ¬1), (¬0 ∧ 1), (¬2 ∧ ¬3)
```

the raw marginal profile is `(2,0,2,2)` (equivalently the nonnegative Lean rank is
`(6,4,6,6)`).  Thus the refinement does exactly repair the preceding root error: it selects
coordinate zero, one of the three exact winning root queries.  However, after either value of
zero, its marginal profile becomes `(0,4,2,2)`.  It then selects coordinate one because deleting
the residual singleton cancellation component yields the largest raw component decrease.  That
singleton residue is already within the target residual depth one, while the disjoint width-two
clause is the component that still needs a query.  The rollout consequently still needs three
queries; the preserved explicit trunk `[0,2]` needs only two.

`liveClauseSupport`, `activeLiveClauseSupports`, `closeClauseSupport`, and
`clauseSupportComponentCount` formalize the generic executable incidence calculation.
`componentMarginalRank`, `maximumComponentAwareQuery`, and its recursive stopping predicate
formalize the selector.  Kernel-checked `decide` theorems record the repaired root choice, both
bad second choices, and the strict three-versus-two gap.  The Python audit reproduces all earlier
counterexamples and this rollout failure; it finds the latter on the same 31st ordered gate after
2,431 restricted states.

A bounded five-minute Lean elaboration passed all new declarations and continued into the known
expensive tail before timing out; this is not a full-file build claim.  `git diff --check` passes,
and no `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was introduced.  All earlier
failed selectors and witnesses remain preserved.

The precise next frontier is residual-depth-aware component accounting.  Raw component count
prices deletion of a component even when that component is already shallow enough to stop.  The
smallest next audit should count only component excess above the target residual depth (or an
equivalent local unresolved-component potential), verify that it retains the root repair, and
test its entire branch-conditioned rollout on this same witness before expanding the domain.
Any useful definition must remain local rather than silently reintroducing the exact child
stopping game; the stored-tree and independent density/fiber obstructions remain open.  No
P-versus-NP conclusion follows.

### Residual-depth-aware component excess loses the root repair

The smallest proposed refinement has now been tested and fails strictly earlier than the raw
component marginal.  For each active clause-support component, the new local potential charges

```text
max(0, |union of live variables in the component| - residualDepth).
```

Thus it genuinely ignores a singleton component at residual depth one and never evaluates an
exact child stopping game.  On the preserved disconnected family, however, the root family
potential is four and the two-child marginal profile is `(4,4,4,4)`.  The cancellation component
and the disconnected width-two component make all four coordinates look equally useful.  The
preserved lexicographic tie-breakers therefore select coordinate one, which is not an optimal root
query.  The resulting rollout again needs three queries, while the explicit semantic trunk
`[0,2]` still needs only two.

The indicator variant that merely counts components whose live-variable union exceeds the target
depth was also evaluated on the same witness.  It has the identical tied root marginal
`(4,4,4,4)`; after querying coordinate zero its profile is `(0,2,4,4)` on both branches.  Hence the
failure is not an artifact of weighting excess by its magnitude.

`clauseSupportComponentExcess`, `activeFamilySupportComponentExcess`,
`componentExcessMarginalRank`, and `maximumComponentExcessAwareQuery` formalize the generic local
potential and selector.  Kernel-checked executable theorems record root potential four, the Lean
rank vector `(44,44,44,44)`, the losing root choice, and the strict three-versus-two competitive
gap.  The Python audit adds excess and indicator selectors as fifth and sixth exhaustive passes;
both reproduce the same first gap after 31 ordered gates and 2,431 restricted states.  All
preceding counterexamples and failed routes remain preserved.

The precise next frontier is a two-axis component certificate: retain residual-depth-aware
unresolved mass, but add a within-component progress statistic that distinguishes querying the
shared cancellation coordinate zero from querying its residual coordinate one without reviving
the already-failed standalone motif ordering.  The smallest defensible audit is the Pareto pair
of raw component marginal and residual-aware excess marginal on the existing normalized domain,
with an explicit tie policy tested through the entire branch-conditioned rollout.  If every fixed
lexicographic order fails, the evidence points to a genuinely vector-valued or branch-balanced
component charge rather than another scalar local potential.  The stored-tree and independent
density/fiber obstructions remain open.  No P-versus-NP conclusion follows.

### Both lexicographic orders of the component pair fail

The proposed two-axis audit is now executable in both fixed lexicographic orders, with the full
branch-conditioned rollout checked at every restricted state.  Raw-component marginal followed
by residual-aware excess marginal still fails on the preserved disconnected family.  It chooses
the winning root coordinate zero, but after either root value the profiles are raw
`(0,4,2,2)` and excess `(0,2,4,4)`.  Raw priority therefore chooses the already-shallow
cancellation residue one and again needs three queries instead of the explicit trunk `[0,2]`'s
two.  The exhaustive audit finds this first gap after 31 ordered gates and 2,431 states.

Reversing the axes repairs that rollout but exposes a different strict obstruction:

```text
(¬0 ∧ ¬1), (¬0 ∧ ¬2), (¬0 ∧ 2),
```

paired with its termwise-negated polarity.  Coordinate two is the unique one-query winner, but
the raw component marginal is tied `(0,0,0,0)` and the excess marginal is `(8,4,4,0)`.
Excess-first therefore strictly selects coordinate zero and needs two queries.  This is stronger
than a bad tie policy: on the proposed two axes coordinate zero Pareto-dominates the actual winner
two.  Consequently no selector monotone in just these two marginal coordinates can repair this
witness.  The exhaustive audit finds it after 142 gates and 11,422 states.

`maximumRawThenExcessComponentQuery` and `maximumExcessThenRawComponentQuery` formalize the two
generic selectors.  `threeTermIncidenceGapFamily_raw_then_excess_queries_and_gap` kernel-checks
the first rollout failure.  The new normalized family, its explicit one-query common trunk, and
the strict excess-first two-versus-one gap are recorded by
`threeTermExcessThenRawGapFamily_normalized`,
`threeTermExcessThenRawGapFamily_commonShallowAt_one`, and
`threeTermExcessThenRawGapFamily_strict_competitive_gap`.  Both new Python audits pass.  A bounded
five-minute Lean elaboration passed all new declarations and continued beyond line 10,000 with
warnings only before timing out in the known expensive tail; this is not a full-file build claim.
`git diff --check` passes, and no `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was
introduced.  All earlier failed routes and counterexamples remain preserved.

The precise next frontier is no longer another aggregation of the same component pair.  Add one
local terminal-progress coordinate that can recognize cancellation coordinate two in the new
connected witness—the smallest candidate is the number of indexed gates whose two immediate
children both meet the requested residual depth—then exhaustively audit it together with the two
component axes through the full rollout.  This inspects immediate canonical residual depth but
does not evaluate a recursive child stopping game.  If it cannot defeat the new Pareto-dominance
witness without reopening an earlier one, return to a genuinely clause-signed vector
certificate.  The stored-tree and independent density/fiber obstructions remain open.  No
P-versus-NP conclusion follows.

### Immediate terminal progress repairs the Pareto witness but opens a connected gap

The proposed local terminal-progress coordinate is now executable.  For each live query it
counts indexed gates whose canonical trees have depth at most the requested residual depth in
both immediate Boolean children.  It evaluates exactly those two one-step child trees and no
recursive child stopping game.  The audited selector gives this coordinate strict priority,
then raw component marginal, residual-aware excess marginal, and the preserved signed-motif
tie rank.

This coordinate does distinguish the preceding Pareto witness: its root profile is
`(0,0,2,0)`, so terminal priority selects the unique one-query winner two instead of the
component winner zero.  However, exhaustive branch-conditioned audit finds a new strict gap
after 157 ordered gates and 12,637 restricted states:

```text
(¬0 ∧ ¬1), (¬0 ∧ ¬2), (¬1 ∧ ¬3),
```

paired with its termwise-negated polarity.  At the fully live root the terminal profile is
`(0,0,0,0)`, raw component marginal is `(-2,-2,0,0)`, and excess marginal is `(8,8,4,4)`.
Terminal progress therefore supplies no separation, and raw priority selects coordinate two.
The exact flexible game has cost two with winning root coordinates zero and one, while the
selector rollout needs three queries.  An explicit common trunk querying `[0,1]` supplies the
independent semantic depth-two certificate.

`immediateTerminalProgress`, `maximumTerminalThenRawThenExcessComponentQuery`, and its recursive
stopping predicate formalize the generic rule.  The normalized witness, explicit trunk, profile,
and strict three-versus-two gap are recorded by
`threeTermTerminalComponentGapFamily_normalized`,
`threeTermTerminalComponentGapFamily_commonShallowAt_two`, and
`threeTermTerminalComponentGapFamily_profiles_and_gap`.  The Python audit preserves all eight
earlier passes and adds the ninth terminal-first pass.

A bounded five-minute Lean elaboration accepted the new declarations and continued beyond line
10,100 with warnings only before the expensive tail ended the run; this is not a full-file build
claim.  Python syntax checking, all nine executable audits, and `git diff --check` pass.  No
`sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was introduced.

The precise next frontier is to determine whether terminal progress can serve as a secondary
coordinate without losing its repair: audit terminal-then-excess-then-raw and the four orders
where terminal is not primary, beginning with the three preserved witnesses before resuming the
full normalized domain.  If every fixed order fails, replace scalar lexicographic selection with
a clause-signed branch-balance certificate that prices simultaneous progress across both child
polarities.  The stored-tree and independent density/fiber obstructions remain open.  No
P-versus-NP conclusion follows.

### Terminal-then-excess-then-raw survives the complete bounded audit

All six fixed lexicographic orders of immediate terminal progress, residual-aware component
excess, and raw component marginal have now been tested.  Four of the five newly tested orders
fail immediately on preserved witnesses.  Raw-first orders retain the disconnected rollout gap;
putting raw before terminal also retains the connected terminal gap.  Excess-first orders retain
the one-query Pareto witness because excess strictly prefers coordinate zero over the unique
winner two.  Together with the already recorded terminal-then-raw-then-excess failure, five of
the six orders are therefore eliminated without discarding any counterexample.

The sole survivor is terminal progress, then excess marginal, then raw marginal.  It repairs all
three separating witnesses: it selects zero and stops in two queries on the disconnected family,
selects the unique winner two and stops in one query on the Pareto family, and selects zero and
stops in two queries on the connected terminal-gap family.  More significantly, its exhaustive
branch-conditioned rollout has no strict gap anywhere in the complete normalized ordered domain
of three distinct width-two clauses on four variables paired with their termwise-negated
polarity: 103,776 ordered gates and 8,405,856 restricted states were checked against the exact
flexible minimax cost.

`maximumTerminalThenExcessThenRawComponentQuery` and its recursive stopping predicate now
formalize this candidate in Lean.  The kernel-checked theorem
`terminalThenExcessThenRaw_repairs_preserved_witnesses` records its exact root choices and attained
budgets on the three critical families.  The Python audit now runs every axis order and clears
the canonical-depth cache between unrelated gate families, avoiding unbounded cache growth
without changing the semantics.

All fourteen Python audits passed, including the complete 8,405,856-state survivor audit, and
Python syntax checking passed.  A bounded five-minute direct Lean elaboration accepted the new
definitions and regression theorem and continued beyond line 10,100 with warnings only before
timing out in the known expensive tail; this is not a full-file build claim.  `git diff --check`
and the scoped forbidden-feature scan passed.  No `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was introduced.

This is positive finite evidence, not a general competitiveness theorem.  In particular the
audit fixes four variables, three clauses, width two, two paired polarities, and residual depth
one.  The precise next frontier is to search the smallest strictly larger normalized domain,
preferably four width-two clauses on four variables before increasing the variable count, while
separately identifying a local descent invariant that could prove terminal-then-excess-then-raw
competitive.  Any new counterexample must be preserved; if the candidate survives, the next
proof obligation is a generic branch-balance lemma rather than another scalar reordering.  The
stored-tree and independent density/fiber obstructions remain open.  No P-versus-NP conclusion
follows.

### Four clauses refute the surviving fixed lexicographic selector

The smallest proposed larger-domain audit finds a strict gap after only 6,513 ordered gates and
527,473 restricted states.  The positive gate is

```text
(¬0 ∧ ¬1), (¬0 ∧ ¬2), (¬0 ∧ ¬3), (2 ∧ 3),
```

paired with its termwise-negated polarity.  At the fully live root, immediate terminal progress
ties `(0,0,0,0)`, residual-aware excess rank is `(60,56,56,56)`, and the surviving selector
therefore chooses coordinate zero.  Its branch-conditioned rollout needs three queries.  The
exact flexible minimax cost is two, with coordinates two and three as the winning root queries;
the explicit common trunk `[2,3]` independently certifies residual depth one in budget two.

This eliminates the last of the six fixed lexicographic orders of terminal progress, excess
marginal, and raw component marginal: the other five remain separated by their preserved
three-clause witnesses.  The failure also identifies information discarded by the current
terminal coordinate.  It counts a gate only when that same gate is shallow in both children.
On the new witness this profile is zero everywhere, but the per-branch counts of shallow gates
are `(0,0)` for coordinates zero and one and `(1,1)` for coordinates two and three.  Thus a
branch-balanced aggregate sees the exact winners without evaluating a recursive stopping game.

`fourTermTerminalThenExcessGapFamily_normalized`,
`fourTermTerminalThenExcessGapFamily_commonShallowAt_two`, and
`fourTermTerminalThenExcessGapFamily_profiles_and_gap` preserve the normalized witness, its
semantic trunk, the separating score, and the strict three-versus-two rollout gap in Lean.  The
Python audit now has a reproducible `--four-clause-survivor` mode and an optional `--max-gates`
bound; the strict gap occurs before that bound matters.

Python syntax checking and the exact four-clause search passed.  A bounded five-minute direct
Lean elaboration accepted every new declaration and continued beyond line 10,600 with warnings
only before timing out in the known expensive tail; this is not a full-file build claim.
`git diff --check` and the scoped forbidden-feature scan pass.  No `sorry`, `admit`, custom axiom,
`unsafe`, or `native_decide` was introduced.

The precise next frontier is to formalize and exhaustively audit the local branch-balance
coordinate

```text
min(number of gates shallow in the false child,
    number of gates shallow in the true child)
```

on all preserved witnesses before searching the four-clause domain again.  If it reopens an
earlier gap, retain a two-child vector rather than imposing another fixed scalar order.  A future
positive result would still require a generic descent/competitiveness lemma; the stored-tree and
independent density/fiber obstructions remain open.  No P-versus-NP conclusion follows.

### Worst-child branch balance clears the complete three-clause frontier

The proposed local coordinate is now executable in Python and kernel-checked on the preserved
Lean witnesses.  For a live coordinate `i`, it separately counts the indexed gates whose
canonical tree has depth at most the residual target after `i := false` and after `i := true`,
then scores `i` by the smaller count.  The selector retains terminal, excess, raw, and the signed
motif rank only as lexicographic tie-breakers.  It still performs no recursive stopping-game
evaluation.

The complete normalized ordered three-clause width-two audit found no strict gap across 103,776
gates and all 8,405,856 restricted states.  A bounded four-clause audit found no gap in the first
7,000 ordered gates and 567,000 restricted states.  This prefix includes the old counterexample,
which occurred at gate 6,513.  On that witness the child-count pairs are `(0,0)`, `(0,0)`,
`(1,1)`, `(1,1)`; the new selector therefore chooses winning coordinate two and stops at the
exact two-query budget.

`immediateChildShallowCount`, `immediateBranchBalance`, `maximumBranchBalanceQuery`, and
`branchConditionedMaximumBranchBalanceStops` formalize the statistic and its rollout in Lean.
`branchBalance_repairs_preserved_selector_witnesses` records exact root profiles, selected
coordinates, and successful semantic budgets for the original greedy witness, the incidence,
excess/raw, and terminal-component witnesses, and the four-clause survivor.  A bounded five-minute
direct elaboration accepted these declarations and continued beyond line 10,300 with warnings
only before the timeout; this is not a full-file build claim.

Python syntax checking, the complete three-clause audit, and the bounded four-clause audit passed.
`git diff --check` and the scoped forbidden-feature scan pass.  No `sorry`, `admit`, custom axiom,
`unsafe`, or `native_decide` was introduced.

This remains finite evidence, not a competitiveness theorem.  The precise next frontier is a
generic one-step branch-balance lemma: relate the worst-child shallow-gate count to a monotone
deficit that lower-bounds every remaining common-shallow trunk.  In parallel, any future finite
search should quotient the four-clause space by safe polarity/coordinate symmetries before
attempting the remaining millions of ordered gates; a new gap must retain the full two-child
vector rather than collapse immediately to another scalar ordering.  The stored-tree and
independent density/fiber obstructions remain open.  No P-versus-NP conclusion follows.

### The direct branch-balance deficit is not monotone

The proposed generic proof route cannot use the complementary current shallow-gate count as its
monotone deficit.  The first normalized three-clause witness found by the executable audit is

```text
(¬0 ∧ ¬1), (¬2 ∧ ¬0), (¬0 ∧ ¬3).
```

Under the restriction fixing only coordinate three to false, its recomputed canonical tree has
depth one.  Extending that restriction by fixing coordinate one to true makes the recomputed
canonical depth rise to two.  For the singleton indexed family at residual target one, the
current shallow-gate count therefore drops from one to zero and its complementary deficit rises
from zero to one.  This is a canonical-order effect: restriction extension preserves semantics
but can change which active clause and literal the canonical procedure encounters first.

`shallowCountMonotonicityGapGate`, `currentShallowGateCount`, and
`currentShallowGateCount_not_monotone_under_fixVar` preserve the normalized witness and exact
depth/count/deficit values in Lean.  The Python audit has a reproducible `--shallow-monotonicity`
mode and finds the same first witness after 1,066 generated ordered gates.

This obstruction does not refute the branch-balance selector itself; it refutes the most direct
monotone-potential proof suggested by its finite success.  The precise next frontier is to test a
stored-tree deficit, where every child uses the restriction of the parent's already-built
canonical tree rather than recomputing a new canonical tree.  That quantity is monotone by tree
restriction, but it must still be shown to control the recomputed `canonicalDT` terminal condition
used by `CommonShallowAt`.  In parallel, the four-clause selector audit now clears 20,000 ordered
gates and 1,620,000 restricted states without a strict gap.  The independent density/fiber
obstructions remain open.  No P-versus-NP conclusion follows.

### Stored-tree monotonicity is real but does not control canonical recomputation

The proposed stored-tree audit now has a generic kernel-checked core.  `CommonTree.readOnce` is
the relevant restriction operation: if `tau` extends `rho`, then restricting one fixed stored tree
at `tau` has depth at most its restriction at `rho`.  Consequently the number of stored canonical
gate trees meeting a residual-depth target is monotone nondecreasing along a trunk, and its
complementary deficit is monotone nonincreasing.

The preserved shallow-count witness sharply separates this valid invariant from the terminal
condition actually used by `CommonShallowAt`.  Build the canonical tree once at the restriction
fixing coordinate three to false, then additionally fix coordinate one to true.  Restricting the
stored tree still has depth one, so the stored one-gate shallow count remains one.  Recomputing
`canonicalDT` at the extended restriction has depth two.  Thus stored-tree monotonicity repairs the
potential but does not by itself imply recomputed canonical shallowness, even on the first known
counterexample.

The generic result is formalized by `CommonTree.depth_readOnce_anti`,
`storedShallowGateCount_mono`, and `storedShallowGateDeficit_anti`; the exact separation is recorded
by `storedTree_repair_diverges_from_recomputedCanonical`.  The earlier recomputation counterexample
is retained unchanged.

The precise next frontier is no longer to prove stored-tree monotonicity.  It is to test the
weakest possible comparison between a stored residual tree and the recomputed canonical tree:
first search for a bounded blow-up inequality on normalized width-two gates, parameterized by the
number of newly fixed coordinates.  A factor-one comparison is already refuted here.  If no useful
bounded comparison survives, the branch-balance proof must target a semantic shallow-tree terminal
condition and separately bridge that condition into the layered collapse, rather than reuse the
canonical-depth terminal predicate.  The independent density/fiber obstructions remain open.  No
P-versus-NP conclusion follows.

### One new fixing can cost two extra canonical levels

The weakest additive comparison suggested by stored-tree monotonicity is already false.  The
normalized width-two gate

```text
(¬0 ∧ ¬1), (¬2 ∧ ¬0), (¬4 ∧ ¬0), (¬0 ∧ ¬3)
```

is considered at the restriction fixing only coordinate three to false.  Its stored canonical
tree queries coordinate zero first.  After additionally fixing coordinate one to true, restricting
that stored tree has depth one.  A fresh canonical run deletes the first clause and encounters
coordinates two and four before zero, so its depth is three.  Thus, with exactly one newly fixed
coordinate,

```text
recomputed depth = 3 > 1 + 1 = stored residual depth + newly fixed coordinates.
```

`storedTreeAdditiveGapGate_normalized` and
`storedTree_recomputed_depth_not_le_add_one` kernel-check the duplicate-free gate, the restriction
extension, both exact depths, and the failed inequality.  This preserves a strictly stronger
obstruction than the earlier depth-two-versus-one witness.

The executable audit also records useful finite boundary evidence: additive one holds throughout
all 103,776 normalized ordered three-clause width-two gates on four variables and all 22,415,616
one-coordinate extensions, and throughout the first 20,000 four-clause gates (4,320,000
extensions).  The fifth coordinate is therefore genuinely needed by the first explicit stacked
distraction found here; the finite success must not be mistaken for a general theorem.

The precise next frontier is to parameterize this stacked-distraction construction and prove that
one newly fixed coordinate permits arbitrarily large recomputed canonical depth while the stored
residual remains depth one, still with normalized width-two clauses.  That would rule out every
comparison depending only on stored depth and the number of new fixings.  If established, the
branch-balance route must move to a semantic terminal certificate and prove a separate semantic-to-
collapse bridge.  The independent density/fiber obstructions remain open.  No P-versus-NP
conclusion follows.

### The stacked-distraction mechanism is now parameterized and calibrated

The construction is no longer represented only by its first five-variable instance.
`stackedDistractionGate k` uses `k + 3` coordinates, one guard clause, `k` ordered distraction
clauses, and one terminal clause.  `stackedDistractionRestriction k` fixes only the terminal
coordinate false; the descendant additionally fixes only guard coordinate one true.  This keeps
the intended one-new-fixing comparison explicit at every size.

`stackedDistraction_six_calibration` kernel-checks the first substantially larger instance:
with six distractions the clauses are duplicate-free, every clause has two distinct variables,
the descendant extends the root by one fixing, the stored residual depth is one, and freshly
recomputed canonical depth is seven.  In particular, even an additive allowance of five over the
stored depth fails on this normalized width-two gate.

The Python audit now has a deterministic `--stacked-distraction MAX` mode.  It constructs this
same family directly and checks normalization plus the exact law

```text
stored residual depth = 1
recomputed canonical depth = k + 1
```

for every `k` from zero through `MAX`.  The run through `k = 64` passed, reaching recomputed depth
65 while stored depth remained one.  This is strong executable evidence for unbounded separation,
but it is not a proof for arbitrary `k`.

The isolated Lean calibration compiled successfully and its printed axioms are only `propext` and
`Quot.sound`.  A direct elaboration of the full large bridge reached beyond line 5,400 with warnings
only before it was stopped; no full bridge build is claimed.  Python syntax checking and the
65-instance parametric audit passed.  `git diff --check` and the scoped forbidden-feature scan pass.
No `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was introduced.

The precise next frontier is the symbolic exact-depth induction for `stackedDistractionGate k`.
It must show that after the guard fixing, the all-true distraction branch advances the canonical
active-term scan once per clause and finally queries coordinate zero, while the stored tree built
at the root collapses immediately to depth one.  That theorem would upgrade the current finite
calibration to an arbitrary-gap refutation of every bound depending only on stored residual depth
and the number of new fixings.  Only then is the semantic-terminal/collapse bridge forced as a
theorem rather than suggested by an extensively tested family.  The independent density/fiber
obstructions remain open.  No P-versus-NP conclusion follows.

### The symbolic family is uniformly normalized and changes exactly one coordinate

Two structural premises of the arbitrary-`k` induction are now discharged symbolically rather
than inferred from finite calibration.  `stackedDistractionGate_normalized k` proves for every
`k` that the guard, all `List.ofFn` distraction clauses, and the terminal clause form a
duplicate-free gate, and that each clause has two distinct variables.  The proof makes the
`List.ofFn` map injective from the first literal and separates its coordinates `2,...,k+1` from
the guard and terminal coordinates.

`stackedDistraction_one_new_fixing k` proves that the descendant restriction extends the root,
coordinate one changes from free to true, and every coordinate on which the two restrictions
differ is coordinate one.  Thus the eventual arbitrary separation cannot hide extra fixings or
lose normalization as `k` grows.

An isolated file containing these definitions and proofs compiled successfully.  Direct
elaboration of the full bridge passed the edited declarations and continued beyond line 10,600
with warnings only before being stopped; this is not a full-file build claim.  `git diff --check`
and the scoped forbidden-feature scan pass.  No `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was introduced.

The exact depths are deliberately not claimed yet.  Direct unfolding identifies the remaining
proof obligation sharply: prove a reusable `List.ofFn` active-scan lemma saying that after the
first `r < k` distraction coordinates are fixed true, `activeTermLit` selects distraction `r`,
and at `r = k` it selects coordinate zero.  Induction through `replayPath`, followed by
`canonicalDT_depth_ge_replay` and the fuel upper bound, will then give recomputed depth `k+1`.
The stored-depth-one statement remains a separate symbolic lemma.  This is the precise next
frontier; the independent density/fiber obstructions remain open.  No P-versus-NP conclusion
follows.

### The symbolic interior active scan is proved

The list-order core now has a uniform Lean theorem rather than finite calibration.
`stackedDistractionScanRestriction k r` explicitly fixes the terminal coordinate false, disables
the guard with coordinate one true, and fixes exactly the distraction coordinates indexed below
`r` true.  For every `r < k`, `stackedDistraction_activeTermLit_scan k r` proves that
`activeTermLit` selects the negative literal on distraction coordinate `r`.

The proof audits the actual `List.ofFn` ordering.  It proves that no term is already satisfied,
uses `List.find?_eq_some_iff_getElem` at gate index `r+1`, proves the guard and every earlier
distraction fail the active predicate, and reconstructs the indexed clause through `getElem?`.
Thus the selector cannot skip ahead or fall through to the terminal clause.  The statement is
symbolic in both `k` and `r`.

An isolated version of the proof compiled successfully.  Direct elaboration of the production
bridge passed the new declarations and continued beyond line 10,700 with warnings only before it
was stopped; no full-file build is claimed.  The scoped forbidden-feature scan and
`git diff --check` pass.  No `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was
introduced.

The precise next frontier is now narrower: prove the endpoint scan at `r = k`, where the terminal
clause must select coordinate zero, and prove by induction that `replayPath` from the descendant
restriction is definitionally represented by `stackedDistractionScanRestriction k r`.  These two
facts feed `canonicalDT_depth_ge_replay` for the `k+1` lower bound.  A separate symbolic proof that
the root-built stored residual has depth one, together with the standard live-variable fuel upper
bound, will then yield the arbitrary exact-depth separation.  The independent density/fiber
obstructions remain open.  No P-versus-NP conclusion follows.

### The symbolic active scan now reaches its endpoint

`stackedDistraction_activeTermLit_endpoint k` proves uniformly that after all `k` distraction
coordinates have been fixed true, the canonical selector reaches the final clause and selects
its free negative literal on coordinate zero.  The proof identifies the terminal clause at exact
gate index `k+1`, establishes its active predicate, and rules out the guard plus every preceding
`List.ofFn` distraction.  It also covers the empty distraction block `k = 0` without a separate
assumption.

Together with `stackedDistraction_activeTermLit_scan`, this kernel-checks the complete symbolic
selector sequence: distraction coordinates `0,...,k-1`, followed by coordinate zero.  A direct
production-file elaboration passed the new theorem and continued through line 11,204 with warnings
only before the expensive tail was stopped; this is not a full-file build claim.  A separate
prefix-only check through the theorem completed successfully and printed exactly `propext`,
`Classical.choice`, and `Quot.sound`.  The executable stacked-distraction calibration through
`k = 64`, the scoped forbidden-feature scan, and `git diff --check` pass.  No `sorry`, `admit`,
custom axiom, `unsafe`, or `native_decide` was introduced.

The precise next frontier is to prove the transition identity between consecutive scan states:
fixing the selected distraction literal to its all-true branch must turn
`stackedDistractionScanRestriction k r` into `stackedDistractionScanRestriction k (r+1)`.
Induction can then identify the first `k+1` steps of `replayPath`, yielding the symbolic depth
lower bound through `canonicalDT_depth_ge_replay`.  The stored-depth-one lemma and matching
live-variable fuel upper bound remain separate obligations.  The independent density/fiber
obstructions remain open.  No P-versus-NP conclusion follows.

### The symbolic scan state now advances operationally

`stackedDistractionScanRestriction_falFix_coord k r hr` proves for every `r < k` that
falsifying the negative literal selected at distraction stage `r` changes the explicit state
exactly from `stackedDistractionScanRestriction k r` to
`stackedDistractionScanRestriction k (r+1)`.  The proof is extensional: at the selected
coordinate `falFix` writes `true`, while away from it the two interval predicates can differ only
at value `r+2`, which is precisely the excluded selected coordinate.

A source-prefix elaboration through the theorem completed successfully.  Its printed axioms are
exactly `propext`, `Classical.choice`, and `Quot.sound`; `git diff --check` and the scoped
forbidden-feature scan pass.  This verification is deliberately prefix-scoped and is not a full
production build claim.

The precise next frontier is the replay induction itself: prove for `r ≤ k` that `replayPath`
from the guard-disabled descendant after `r` steps equals
`stackedDistractionScanRestriction k r`, using the interior selector theorem and this transition.
Then combine the endpoint selector at step `k` with one final replay step to discharge the
nonterminal premise of `canonicalDT_depth_ge_replay` at length `k+1`.  The stored-depth-one lemma
and matching live-variable fuel upper bound remain separate obligations.  The independent
density/fiber obstructions remain open.  No P-versus-NP conclusion follows.

### The operational replay follows the symbolic scan exactly

`stackedDistraction_replayPath_scan k r hr` now proves for every `r ≤ k` that the all-falsify
`replayPath` starting at the guard-disabled descendant is exactly
`stackedDistractionScanRestriction k r`.  The base case identifies the descendant restriction
extensionally with scan state zero, including the distinct guard and terminal coordinates.  The
successor case uses the symbolic interior selector and the proved `falFix` transition, so the
actual replay cannot skip or repeat a distraction stage.

A source-prefix elaboration through the theorem completed successfully.  The printed axioms are
exactly `propext`, `Classical.choice`, and `Quot.sound`.  This is a prefix-scoped verification, not
a full production build claim.  The scoped forbidden-feature scan and `git diff --check` pass; no
`sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was introduced.

The precise next frontier is to package the replay lower-bound premise for all `i < k+1`: use the
replay invariant for `i ≤ k`, `stackedDistraction_anyTermSat_false`, the interior selector for
`i < k`, and the endpoint selector for `i = k`.  Feeding that premise to
`canonicalDT_depth_ge_replay` will prove fresh canonical depth at least `k+1`.  The matching fuel
upper bound and the symbolic stored-depth-one theorem remain separate obligations before the
arbitrary exact-depth separation is complete.  The independent density/fiber obstructions remain
open.  No P-versus-NP conclusion follows.

### The symbolic replay now forces canonical depth `k + 1`

`stackedDistraction_replay_nonterminal k i hi` packages the complete lower-bound premise for every
`i < k + 1`.  Rewriting the operational state with `stackedDistraction_replayPath_scan` shows that
no term is satisfied.  For `i < k`, the interior selector supplies the next distraction literal;
the only remaining case is `i = k`, where the endpoint selector supplies coordinate zero.  Hence
none of the first `k + 1` replay states is terminal.

`stackedDistraction_canonicalDT_depth_ge k fuel hfuel` feeds this uniform premise directly to
`canonicalDT_depth_ge_replay` and proves, for every `fuel ≥ k + 1`,

```text
k + 1 ≤ depth (canonicalDT (stackedDistractionGate k) fuel descendant).
```

This upgrades the finite `k ≤ 64` calibration to a symbolic lower bound for arbitrary `k`; the
stored-tree comparison is not yet complete because equality still needs a matching upper bound and
the root-built stored residual still needs a symbolic depth-one proof.  The precise next frontier
is the fuel upper bound: compute the descendant's live-variable count (expected `k + 1`) and apply
`canonicalDT_depth_le_stars` to obtain exact fresh depth.  Then prove the separate stored-depth-one
lemma and combine the results into the arbitrary-gap theorem.  The independent density/fiber
obstructions remain open.  No P-versus-NP conclusion follows.

### The stacked-distraction fresh depth is exact at the live-variable fuel

`freeVars_stackedDistraction_descendant k` identifies the descendant's live coordinates exactly:
the terminal coordinate and guard coordinate one are removed from the ambient universe, leaving
coordinate zero and the `k` distraction coordinates.  Consequently
`stars_stackedDistraction_descendant k` proves that its live-variable count is `k + 1`.

`stackedDistraction_canonicalDT_depth_exact k` combines the symbolic replay lower bound with the
unconditional fuel upper bound at that exact live-variable budget, yielding

```text
depth (canonicalDT (stackedDistractionGate k) (k+1) descendant) = k+1.
```

Direct elaboration of the production bridge passed all three new declarations and continued
beyond line 11,300 with warnings only before the expensive unchanged tail was stopped; this is
not a full-file build claim.  The precise next frontier is now the stored side: prove symbolically
that reading the root-built canonical tree under the guard-disabled descendant has depth one at a
common adequate fuel, then package that result with exact fresh depth and
`stackedDistraction_one_new_fixing` into an arbitrary-gap theorem.  The independent density/fiber
obstructions remain open.  No P-versus-NP conclusion follows.

### One new fixing now gives a proved arbitrary canonical-depth gap

The stored side of the stacked-distraction construction is now symbolic.  The theorem
`stackedDistraction_canonicalDT_root_shape k fuel` proves that at every positive fuel the tree
built at the root is exactly

```text
query 0 (leaf true) (leaf false).
```

The first guard clause selects coordinate zero.  On the false branch, the already-false terminal
coordinate makes the terminal clause satisfied; on the true branch, the negative zero literal
falsifies every clause.  Thus no part of the `List.ofFn` distraction block survives in the stored
tree.  Restricting this tree by the descendant retains its free coordinate-zero query, and
`stackedDistraction_stored_depth_exact k fuel` proves stored depth exactly one for arbitrary `k`
and every positive common fuel.

`stackedDistraction_arbitrary_additive_gap B` combines that result with uniform normalization,
`stackedDistraction_one_new_fixing`, and the exact fresh-depth theorem at common fuel `k+1`, where
`k = B+1`.  It proves that the restrictions differ only at coordinate one, stored depth is one,
fresh canonical depth is `B+2`, and

```text
fresh depth > stored depth + B.
```

Consequently no uniform additive comparison can bound recomputed canonical depth using only the
stored residual depth and a constant allowance for this single new fixing, even for normalized
width-two gates.  A source-prefix elaboration through the new capstone completed successfully;
the earlier full-file diagnostic continued without errors until its time limit.  The isolated
root-shape proof also compiled before integration.  `git diff --check`, the scoped forbidden-
feature scan, and the executable stacked-distraction audit through `k = 64` pass.  No `sorry`,
`admit`, custom axiom, `unsafe`, or `native_decide` was introduced.

The precise next frontier is now forced away from stored-versus-recomputed canonical-depth
comparison.  Define a semantic residual terminal certificate for a stored common trunk, prove
that it is monotone under restriction, and bridge it separately to the `leafCollapse`/layered
collapse semantics.  The first high-information test is whether the exact root-shape family is
already semantically terminal at the stored depth-one leaves despite its arbitrarily deep fresh
canonical scan; that determines the weakest viable certificate.  The independent density/fiber
obstructions remain open.  No P-versus-NP conclusion follows.

### The arbitrary-depth gap disappears at stored semantic leaves

The first semantic-terminal test is positive, uniformly in the size of the counterexample.
`stackedDistraction_stored_leaf_terminal k fuel` proves that every assignment extending the
guard-disabled descendant reaches a `CanonicalTerminal` restriction after following the tree
built at the original root.  On the false coordinate-zero branch the terminal clause is already
satisfied; on the true branch no active clause remains.  The single guard fixing is then handled
by the existing theorem `CanonicalTerminal.mono`.

Consequently `stackedDistraction_stored_leaf_rebuild_depth_zero` proves that rebuilding the gate
at either stored leaf has depth zero for every new fuel.  This coexists with
`stackedDistraction_canonicalDT_depth_exact`: at the intermediate guard-disabled restriction the
fresh canonical tree has depth `k+1`, but its stored depth-one tree still routes every assignment
to a genuinely terminal leaf.  Thus the arbitrary stored-versus-fresh depth separation does not
refute a semantic terminal certificate; it isolates why such a certificate must be path/leaf
based rather than an inequality at the intermediate restriction.

A bounded production-file elaboration passed both new theorems and continued beyond line 11,200
with warnings only before its five-minute time limit.  This is not a full-file build claim.
`git diff --check` and the scoped forbidden-feature scan pass.  No `sorry`, `admit`, custom axiom,
`unsafe`, or `native_decide` was introduced.

The precise next frontier is to package this surviving notion generically: define a stored common
trunk whose reached payload restrictions are `CanonicalTerminal` for every indexed gate, prove
that certificate stable when the root restriction is extended (using terminal monotonicity and
path-endpoint extension), and convert it to `CommonShallowAt ... residualDepth 0`.  The existing
`canonicalDT_depth_eq_zero_of_terminal` should then feed the current `leafCollapse`/layered bridge
without changing collapse semantics.  The remaining nontrivial point is the generic compatibility
between extending a root and the stored trunk's reached endpoint, not canonical depth.  The
independent density/fiber obstructions remain open.  No P-versus-NP conclusion follows.

### Stored semantic terminality is now a reusable monotone certificate

The path/leaf notion surviving the stacked-distraction counterexample is now packaged as
`StoredCommonTerminalAt`.  It stores one Boolean common tree, bounds its read-once depth at the
current root, and requires every reached path endpoint to be `CanonicalTerminal` for every indexed
gate.

The generic endpoint lemma
`CommonTree.pathEndpoint_restrictionExtends_of_restrictionExtends` proves the compatibility that
was previously open: if `sigma` is extended to `tau` and `x` extends `tau`, then the endpoint of a
fixed stored tree from `sigma` is restriction-extended by its endpoint from `tau`.  A query skipped
at the stronger root is either already fixed there or, if still free, remains on the normalized
path.  Combining this with stored-tree depth antitonicity and `CanonicalTerminal.mono` yields
`StoredCommonTerminalAt.mono`.

`StoredCommonTerminalAt.toCommonShallowAt` decorates the stored tree with complete
`prefixEndpoints` and converts the certificate, for arbitrary rebuild fuel, to
`CommonShallowAt ... trunkDepth 0`.  Thus the existing `leafCollapse` and layered bridge can consume
the certificate without comparing a stored residual depth to a freshly recomputed intermediate
depth.

The stacked-distraction family now instantiates the abstraction explicitly:
`stackedDistraction_stored_common_terminal` gives the singleton family a depth-one stored
certificate at the guard-disabled descendant, and
`stackedDistraction_stored_commonShallowAt_zero` converts it to the residual-depth-zero collapse
interface.  This coexists with fresh depth `k+1`, so the repaired bridge addresses the exact
arbitrary-gap witness rather than assuming it away.

Both reusable modules compile.  Their printed capstone axioms are exactly `propext`,
`Classical.choice`, and `Quot.sound`.  Production elaboration of the large TwoSAT bridge passed the
two concrete theorems and continued beyond line 11,188 with warnings only before the five-minute
limit; this is not a full-file build claim.  No `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was introduced.

The precise next frontier is to thread `StoredCommonTerminalAt.mono` through an actual layered
survivor transition: retain the counted bounded trunk as stored state, extend its root by the next
round's restriction, convert the transported certificate to `CommonShallowAt ... 0`, and invoke
the existing `leaf_collapseRound_family_bounds`.  The key audit is whether the counting theorem
currently exposes terminality of that bounded stored trunk (as opposed to shallowness only after
fresh rebuilding); if it does not, that production lemma is the next genuine obligation.  The
independent density/fiber obstructions remain open.  No P-versus-NP conclusion follows.

### The realized-density counting output already contains a stored terminal trunk

The production counting interface does not need a stronger bad event.  The new converse theorem
`canonicalTerminal_of_canonicalDT_depth_eq_zero_of_stars_le_fuel` proves that canonical depth zero
at ample fuel is genuine semantic terminality, rather than a fuel-exhaustion leaf.

`CommonShallowAt.toStoredCommonTerminalAt_zero` then converts any residual-depth-zero common
certificate into `StoredCommonTerminalAt`.  It retains the query shape while erasing irrelevant
leaf payloads.  The main compatibility lemma proves that the path endpoint of this stored shape
extends the original certificate leaf: queried coordinates agree with the followed assignment,
while the existing global leaf-agreement theorem rules out hidden fixings of unqueried live
coordinates.  Terminality therefore transfers monotonically to the stored endpoint.

Finally, `exists_normalizedLayered_storedCommonTerminalAt_of_realized_density` specializes the
existing circuit counting theorem at residual depth zero.  Under the same width-two, term-count,
fuel, shell, and realized-density hypotheses, it returns a `20*r`-star root carrying a stored
terminal trunk of depth at most `10*r`.  Hence the exact counted object can be transported through
later restriction extensions by `StoredCommonTerminalAt.mono` and reconverted to the layered
collapse interface; fresh rebuilding at the intermediate restriction is unnecessary.

The reusable fuel-safe module and the circuit support-survivor module elaborate successfully.
The dependency target build completed 8,240 jobs.  Printed axioms for the new capstones are exactly
`propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was introduced.

The precise next frontier is an actual stateful round theorem: extend the selected stored
certificate to the survivor restriction, invoke `toCommonShallowAt` there, and feed that exact
transported certificate to `leaf_collapseRound_family_bounds`, retaining the stored trunk (or its
successor certificate) in the round state for iteration.  The remaining audit is now state
plumbing and the next-round family change, not production terminality of the counted trunk.  The
independent density/fiber obstructions remain open.  No P-versus-NP conclusion follows.

### The stored certificate now crosses one real layered survivor transition

`StoredCommonTerminalAt.extended_leaf_collapseRound_family_bounds` is the first explicit stateful
round wrapper.  Starting from a stored terminal certificate for the normalized two-polarity family
of `C`, it accepts an arbitrary survivor restriction extending the certificate root, retains the
transported `StoredCommonTerminalAt` object at that restriction, converts that same object to
residual-depth-zero `CommonShallowAt`, and feeds it directly to
`leaf_collapseRound_family_bounds`.

At every reached trunk leaf the resulting collapse keeps at most `M` bottom gates and has clause
bound `M * 2^(0+1)`.  This verifies that certificate transport, rebuild-fuel independence, family
coverage, and the existing layered collapse interface compose without another semantic lemma.
The theorem deliberately retains terminality only for the old family.  Its output circuit has a
new normalized bottom-gate family, and semantic terminality of the old gates says nothing about
those newly synthesized clauses.

The full layered-bridge source elaborates successfully.  The precise next frontier is therefore
the successor-state constructor: combine the collapsed circuit and its survivor restriction with
the next realized-density selection, prove the selected next root extends the reached leaf, and
return a fresh `StoredCommonTerminalAt` for
`normalizedLayeredBottomFamily (collapseRound ...)`.  That step must audit the next density premise
against the proved `M * 2` residual-zero clause bound; reusing the old certificate across the family
change would be unsound.  The independent density/fiber obstructions remain open.  No P-versus-NP
conclusion follows.

### The fresh successor certificate is constructed conditionally on the actual next density

`StoredCommonTerminalAt.exists_localized_collapse_successor_of_realized_density` now crosses the
family-change boundary soundly.  It consumes the stored residual-zero certificate at a reached
leaf, applies `collapseRound`, and relabels the collapsed circuit to that leaf's live-coordinate
cube.  The old certificate is not reused for the synthesized clauses.

The auxiliary theorem `localizeLiveLayered_BottomCount` proves that live-coordinate localization
cannot increase any bottom gate's clause count.  Together with the residual-zero collapse bounds,
the localized successor has bottom width at most two and `BottomCount (2*M)`.  Consequently, if a
scheduled `20*r` shell fits inside the reached leaf and this actual localized circuit satisfies
the verified rectangular realized-density inequality with term cap `2*M`, the production selector
returns a fresh `StoredCommonTerminalAt` of depth `10*r` for the successor's normalized two-polarity
family.  `liftLiveRestriction_extends` proves that the selected local root lifts to a genuine
ambient restriction extension of the reached leaf.

This closes the semantic and coordinate-plumbing part of the successor constructor, while leaving
the quantitative premise explicit.  In particular, the next family charge is its actual
`layeredBottomFamilyList` length times `2*M`; nothing here assumes the same shell parameter can be
reused after a nontrivial trunk.  Focused elaboration of the full quantitative-iteration module
passed, and the new capstones use only `propext`, `Classical.choice`, and `Quot.sound`.  No `sorry`,
`admit`, custom axiom, `unsafe`, or `native_decide` was introduced.

The precise next frontier is to discharge the conditional next-density inequality from the proved
bottom-gate and live-shell recurrences, using a decreasing schedule satisfying
`20*r_next <= stars leaf` (for example the existing backward survivor schedule).  The first task is
to replace the successor theorem's actual family-length factor by a recurrence bound derived from
the retained `M` bottom-gate bound, then test the resulting inequality against the available live
dimension.  The independent density/fiber obstructions remain open.  No P-versus-NP conclusion
follows.

### The successor family factor is bounded, but the current backward schedule misses its product

`localizeLiveLayered_bottomGates_length` now proves that live-coordinate localization preserves
the number of syntactic bottom gates exactly.  Combined with `collapseRound_count_le`, the stored
successor constructor now records

```text
length(layeredBottomFamilyList D) <= 2*M.
```

Together with its already proved `BottomCount (2*M) D`, this replaces the formerly circuit-owned
rectangular key factor by the explicit worst-case recurrence `(2*M)*(2*M) = 4*M^2`.  Thus the
family-length interface is no longer open.

The resulting schedule test fails before any further semantic construction is needed.
`finiteBackwardSchedule_obligations_do_not_imply_successor_rectangular_density` kernel-checks the
smallest concrete mismatch: for residual depth zero, `M = 1`, current survivor parameter `4`, and
next parameter `1`, both inequalities stored by the present backward schedule hold,

```text
20*R_next <= 10*R_current
nextRoundActualMargin 0 1 <= 10*R_current,
```

but the successor's width-two rectangular density demand is `1220 <= 41`, hence false.  The issue
is structural: `nextRoundActualMargin` stores only the density base, while the realized-density
premise multiplies that base by the next shell size before comparing it with the current live
dimension.  Treating shell fit and base fit as two independent inequalities loses this product.

The precise next frontier is to replace `FiniteBackwardSurvivorSchedule` with a product-aware
condition (preferably using the already proved linear ragged-alphabet cap rather than the quadratic
rectangular cap), construct its least backward budget, and test whether that corrected budget fits
the original ambient shell.  The existing schedule must not be used to discharge the successor
density premise.  The independent density/fiber obstructions remain open.  No P-versus-NP
conclusion follows.

### The successor now uses the exact ragged product, with its least one-step budget calibrated

The family-change handoff no longer routes through the quadratic rectangular envelope.
`localizeLiveLayered_bottomClauseCount_le` proves that live-coordinate transport cannot increase
the total bottom-clause occurrence count.  Combining it with
`collapseRound_bottomClauseCount_le` and duplicate normalization shows that the actual localized
successor satisfies

```text
sum_g length(normalizedLayeredBottomFamily D g)
  <= layeredRoundActualKeyCap M 0 = 4*M.
```

`exists_normalizedLayered_storedCommonTerminalAt_of_actual_density` is the strict production form
of the ragged-alphabet contraction.  The stored successor constructor now consumes that theorem
directly: its conditional density premise charges the actual sum of normalized clause
occurrences, not `family length * maximum gate length`.  This removes the spurious quadratic
`4*M^2` recurrence from the successor interface while retaining the necessary product with the
next shell size.

The corrected arithmetic interface is recorded by `nextRoundProductDemand` and
`FiniteProductAwareSurvivorSchedule`.  For one fixed transition,
`leastProductAwarePredecessor` is proved both sufficient and minimal.  The smallest nontrivial
calibration is already decisive: with `M = 1`, residual depth zero, and next survivor parameter
one, the ragged cap is four and the least current survivor parameter is exactly `122`.  Thus the
least current shell is `20*122 = 2440`, whereas the rejected old schedule used only `20*4 = 80`.
The linear ragged cap repairs the extra factor of `M`, but it does not make the omitted shell
product inexpensive.

Focused elaboration of the quantitative-iteration module passed.  The new capstones use only the
standard logical axioms already present (`propext`, `Classical.choice`, and `Quot.sound`); no
`sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was introduced.  Earlier
counterexamples and failed routes remain in place.

The precise next frontier is to lift the exact one-step predecessor into an attained and minimal
finite backward recurrence whose terminal survivor remains positive, substitute the forward
`M_i`/ragged-key recurrence, and compare its initial `20*R_0` shell and fuel floor with the original
ambient dimension.  The independent density/fiber obstructions remain open.  No P-versus-NP
conclusion follows.

### The exact finite product-aware recurrence is attained, minimal, and already explosive

`leastFiniteProductAwareBudget` now iterates the corrected one-step predecessor backwards from an
explicit terminal survivor.  Its key indexing is occurrence-sensitive: transition `i` charges
`actualKeys (i+1)`.  `exists_finiteProductAwareSurvivorSchedule_least` constructs a schedule whose
initial value is exactly this recurrence and whose final value is exactly the requested terminal.
Conversely, `leastFiniteProductAwareBudget_le_initial` proves that every product-aware schedule
ending at or above that terminal starts at or above the recursive value.  Thus the finite budget
is both attained and minimal.  A positive terminal also gives a positive initial budget.

The forward specialization `shallowForwardActualKeys` substitutes the cheapest verified slot
recurrence `M_i = M_0*3^i` and charges transition `i` by the proved ragged cap `4*M_i`.  The first
two-round calibration is stark.  For `M_0 = 1` and terminal survivor one, the exact backward
values are

```text
R_2 = 1,
R_1 = 314,
R_0 = 38308,
20*R_0 = 766160.
```

The one-round value was `R_0 = 122` and shell `2440`.  Hence the omitted shell product does not
merely change a constant: even the smallest two-round forward instance multiplies the requested
next survivor by the current ragged density base, causing rapid recurrence growth.  The earlier
non-product schedule and its counterexample remain in the file as a rejected route.

The quantitative-iteration target builds successfully (8451 jobs), and the full build passes
(8068 jobs).  The new capstones use only
the standard logical axioms already present; no `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was introduced.

The precise next frontier is to derive symbolic lower bounds for the forward-specialized
product recurrence over arbitrary fixed depth and initial `M_0`, then compare `20*R_0` and the
same fuel floor with the actual round-zero ambient `n`.  In particular, determine whether the
recurrence is polynomial of depth-dependent degree for fixed depth and whether any intended
initial gate envelope can fit it; if not, the present whole-family realized-density iteration is
quantitatively closed as a route.  The independent density/fiber obstructions remain open.  No
P-versus-NP conclusion follows.

### The forward product recurrence has an exact affine form and fixed-depth degree `d`

The ceiling and maximum in the corrected predecessor are now eliminated symbolically:

```text
leastProductAwarePredecessor A R = (24*A + 26)*R.
```

For the cheapest verified shallow forward recurrence `M_i = M_0*3^i`, the ragged key cap is
`A_i = 4*M_i`.  Therefore `shallowProductBudget` records the exact arbitrary-depth recurrence

```text
B(0,M,T)     = T,
B(d+1,M,T)   = (96*M + 26)*B(d,3*M,T),
leastFiniteProductAwareBudget d (shallowForwardActualKeys M) T = B(d,M,T).
```

The new lower and upper bounds are

```text
(96*M)^d*T <= B(d,M,T) <= (96*M*3^d + 26)^d*T.
```

Thus for every fixed `d` and positive fixed terminal survivor, the current whole-family schedule
is polynomial of degree exactly `d` in the initial bottom-slot envelope `M`; its obstruction is
not hidden super-polynomial growth in `M`, but the degree-`d` shell that must fit the ambient
dimension and rebuild fuel.  The formal shell corollary proves that any
`n < 20*(96*M)^d*T` cannot host the schedule.

The next concrete calibration continues the rapid constant growth.  With `M=1`, `T=1`, and three
rounds, the exact affine factors are `122`, `314`, and `890`, giving

```text
R_0 = 34094120,
20*R_0 = 681882400.
```

The earlier non-product schedule, its explicit counterexample, and the exact one- and two-round
calibrations remain preserved.  Focused elaboration of the quantitative-iteration module passed.
The new capstones use only the standard logical axioms already present; no `sorry`, `admit`,
custom axiom, `unsafe`, or `native_decide` was introduced.

The precise next frontier is to instantiate the proved degree-`d` floor with the actual
round-zero relation between `M_0` and ambient `n` in the intended circuit envelope.  If
`20*(96*M_0)^d*T > n` there, the present whole-family realized-density iteration is
quantitatively ruled out and the next route must amortize or avoid the family-wide key product;
if it fits, construct the corresponding fuel-compatible initial state and iterate the stateful
successor theorem.  The independent density/fiber obstructions remain open.  No P-versus-NP
conclusion follows.

### A uniform polynomial slot envelope cannot fit the product-aware schedule

The degree comparison is now instantiated at the first standard circuit-envelope boundary.
`shallowProductAwareSchedule_not_fit_of_ambient_le_slots` proves that for positive iteration depth
and positive terminal survivor, the initial shell cannot fit whenever the round-zero slot envelope
used by the schedule satisfies `n <= M_0`.  The zero-dimensional edge case is handled separately,
so the theorem has no hidden positivity premise on `n`.

The direct specialization
`shallowProductAwareSchedule_not_fit_of_polynomial_slot_envelope` shows that on every nonempty
ambient cube, every positive exponent `k`, positive depth `d`, and positive terminal `T`, choosing
the usual uniform polynomial envelope

```text
M_0 = n^k
```

makes

```text
20 * leastFiniteProductAwareBudget d (shallowForwardActualKeys M_0) T <= n
```

false.  Thus the present whole-family realized-density iteration cannot establish a uniform result
by simply plugging a standard `n^k` bottom-slot bound into its verified schedule.  This is an
envelope obstruction, not a circuit lower bound: it does not say that every circuit in the class
has `n^k` actual bottom gates, and it leaves circuit-specific sublinear or fixed-size bottom layers
open.  The earlier exact recurrence, calibrations, and rejected non-product schedule remain in
place.

The precise next frontier is to decide whether the intended family admits a semantics-preserving
reduction to a circuit-specific `M_0 < n` (strong enough that `20*(96*M_0)^d*T <= n`), or whether
uniformity over all circuits of size at most `n^k` genuinely forces use of the incompatible
envelope.  If the latter, the whole-family product route is closed for that uniform theorem and the
next mechanism must amortize or avoid the family-wide key charge.  The independent density/fiber
obstructions remain open.  No P-versus-NP conclusion follows.

### A fitting circuit-specific envelope must be strictly `d`th-root sparse

The possible circuit-specific escape window is now stated as a necessary condition rather than
the weaker comparison `M_0 < n`.  The strengthened obstruction
`shallowProductAwareSchedule_not_fit_of_ambient_le_slots_pow` proves that, for positive depth and
positive terminal survivor, the schedule cannot fit whenever

```text
n <= M_0^d.
```

Equivalently, `slots_pow_lt_ambient_of_shallowProductAwareSchedule_fit` proves that every fitting
schedule must satisfy

```text
M_0^d < n.
```

This is only a necessary condition; the omitted constants in the exact lower shell
`20*(96*M_0)^d*T` make the true window smaller.  In particular, merely proving a
semantics-preserving reduction from `M_0 <= n^k` to some unspecified `M_0 < n` would not reopen a
multi-round route.  At depth `d`, the reduction must cross the `d`th-root scale before the
stateful successor construction can possibly fit.

The existing ideal semantic-slot API does not currently supply such a reduction.  Its preserved
live-literal examples show that semantic cleanup removes neither every baseline slot nor the
aggregate component charge, so duplicate elimination alone cannot establish the required
root-scale sparsity.  This is an obstruction for the verified schedule, not a lower bound against
all circuit representations.

The precise next frontier is to test the intended initial circuit family against this root-scale
threshold: either prove a width- and alternation-preserving representative with `M_0^d < n` and
then discharge the stronger exact constant bound, or exhibit a family member whose minimum
admissible bottom-slot envelope is at least the root scale.  If neither is available, the present
whole-family product route remains quantitatively unusable and the next mechanism must amortize or
avoid the family-wide key charge.  The independent density/fiber obstructions remain open.  No
P-versus-NP conclusion follows.

### Width-two parity closes the circuit-specific escape window

The intended dense-support parity family can now be tested against the actual circuit-owned slot
count, without substituting a worst-case polynomial envelope.  The theorem
`widthTwoParity_ambient_le_two_mul_bottomSlotCount` combines the already proved full-support
necessity for parity with the width-to-clause-occurrence bound and proves that every width-two
layered circuit computing parity, possibly XOR a fixed output phase, satisfies

```text
n <= 2 * bottomSlotCount C.
```

This semantic lower bound applies to every width-two layered representative, so duplicate removal
or another semantics-preserving cleanup cannot create a root-sparse representative inside the
same width class.  It is stronger than merely exhibiting one syntactically dense circuit.

The capstone `widthTwoParity_shallowProductAwareSchedule_not_fit` substitutes the *actual*
`bottomSlotCount C` into the exact forward product-aware recurrence.  For every positive iteration
depth and positive terminal survivor it proves

```text
not (20 * leastFiniteProductAwareBudget d
       (shallowForwardActualKeys (bottomSlotCount C)) terminal <= n).
```

Thus constants close even the one-round escape window: the schedule's homogeneous first factor is
already `96 * bottomSlotCount C`, while width-two parity gives `n <= 2 * bottomSlotCount C`.
The earlier polynomial-envelope and `d`th-root obstructions remain useful general regression
theorems, but for the intended width-two parity route the conclusion is now circuit-specific and
decisive.  This rules out the present whole-family realized-density/product schedule for that
family; it is not a parity lower bound and does not rule out other switching encoders.

Focused elaboration of the quantitative-iteration module passed.  Both new capstones print only
the standard logical axioms already present (`propext`, `Classical.choice`, and `Quot.sound`); no
`sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was introduced.

The precise next frontier is no longer representative sparsification for width-two parity.  A
viable dense-support iteration must remove or amortize the whole-family key product—most directly,
prove a restriction- or survivor-conditioned charge whose round-zero cost is not linear in every
bottom clause occurrence, and test it against the preserved scheduled counterexamples.  Absent
such a theorem, the product-aware route should remain recorded as quantitatively closed for the
width-two parity target.  The independent density/fiber obstructions remain open.  No P-versus-NP
conclusion follows.

### Any replacement product alphabet must beat the exact 240-to-one first-round threshold

The required amortization is now quantified independently of the later-round key recurrence.
`widthTwoParity_firstKey_compression_of_productAwareSchedule_fit` accepts an arbitrary key sequence
`actualKeys`, a positive number of rounds, and a positive terminal survivor.  If the exact
product-aware shell fits a width-two parity representative with actual bottom-slot count `M`, then
its first charged alphabet `A = actualKeys 1` necessarily satisfies

```text
240*A + 260 <= M.
```

The proof uses only the first exact predecessor factor `(24*A+26)`, positivity of the remaining
backward budget, the initial shell multiplier `20`, and the circuit-specific support bound
`n <= 2*M`.  Consequently the result does not assume the current forward key cap, and no amount of
later-round amortization repairs a first alphabet above this threshold.

The contrapositive
`widthTwoParity_productAwareSchedule_not_fit_of_firstKey_undercompressed` records the operational
form: if `M < 240*A+260`, the schedule cannot fit.  Thus replacing the present `A=4*M` charge by
`A=M`, or even by one key per any fixed block of at most 239 occurrences, remains quantitatively
insufficient.  A viable product-form encoder must already compress the first round beyond roughly
240 slot occurrences per key (and then still satisfy all later factors).  This does not exclude a
different density theorem whose demand is not proportional to `A` times the survivor shell.

Focused elaboration of the quantitative-iteration module passed, and the full `lake build` passed
(8,068 jobs).  Both new capstones print only `propext`, `Classical.choice`, and `Quot.sound`; no
`sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was introduced.

The precise next frontier is to test a genuinely restriction- or survivor-conditioned alphabet
against this threshold: construct a sound first-round code with `240*A+260 <= bottomSlotCount C`
for the dense-support parity family, then audit its later-round recurrence.  If every sound code
still needs more than `(M-260)/240` first-round keys, prove that lower bound and close the entire
present product-demand form; otherwise thread the compressed alphabet through the realized-density
decoder and the preserved scheduled counterexamples.  The independent density/fiber obstructions
remain open.  No P-versus-NP conclusion follows.

### The exact tail makes the first-round threshold exponential in round count

The first-round audit now retains the tail budget discarded by the preceding positivity argument.
`leastFiniteProductAwareBudget_baseline_lower` proves, for every alphabet sequence (including an
identically zero sequence), that `e` remaining product-aware transitions and terminal survivor
`T` cost at least

```text
26^e * T.
```

The exact circuit-specific theorem
`widthTwoParity_firstKey_tail_budget_of_productAwareSchedule_fit` shows that if the schedule fits a
width-two parity representative, first alphabet `A`, actual bottom-slot count `M`, and remaining
least budget `B`, then

```text
(240*A + 260) * B <= M.
```

Consequently `widthTwoParity_firstKey_depth_compression_of_productAwareSchedule_fit` proves the
alphabet-independent depth form

```text
(240*A + 260) * 26^(d-1) * T <= M
```

for every positive `d`.  Thus the earlier 240-to-one target is exact only for one round with
terminal survivor one.  Two rounds already require the first-round charge, including its additive
constant, to fit after a factor 26; each additional round imposes another factor 26 even under the
unrealistically favorable assumption that every later alphabet is empty.  Later-round
amortization therefore tightens rather than merely preserves the first-round obstruction.

Focused elaboration passed, and the new capstones print only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was introduced.  The
earlier normalization results, counterexamples, and rejected schedules remain preserved.

The precise next frontier is to compare a concrete sound restriction- or survivor-conditioned
first-round code against the depth-sensitive bound, not the one-round bound: for intended depth
`d` and terminal `T`, prove its alphabet satisfies
`(240*A+260)*26^(d-1)*T <= bottomSlotCount C` and then audit its actual (necessarily more expensive)
tail.  Alternatively, prove a lower bound on every sound conditioned alphabet that violates this
inequality, closing the current product-demand form at that depth.  A non-product density theorem
remains outside this obstruction.  No P-versus-NP conclusion follows.

### Even a zero-label conditioned alphabet has an exact depth floor

The first concrete conditioned-alphabet test now takes the strongest possible optimistic limit:
it allows the first charged alphabet to be empty.  The capstone
`widthTwoParity_productAwareSchedule_not_fit_of_depth_baseline` proves that the product-demand
schedule cannot fit whenever

```text
bottomSlotCount C < 260 * 26^(d-1) * T.
```

This obstruction is independent of every alphabet in the schedule.  It is the additive `+26`
transition cost, propagated through the unavoidable tail, so no restriction-conditioned decoder
can repair a circuit below this slot threshold while retaining the current product-demand
recurrence.  The two-round, terminal-one specialization is kernel checked explicitly: fewer than
`6760` actual bottom slots cannot fit even with `A = 0`.

The companion theorem
`widthTwoParity_productAwareSchedule_not_fit_of_positive_firstKey` assumes only that the first
alphabet is nonempty and raises the necessary floor to

```text
500 * 26^(d-1) * T <= bottomSlotCount C.
```

This does not assert that every sound conditioned code is nonempty; that semantic connection must
be supplied by the eventual code interface.  It cleanly separates two obligations: circuits below
the `260` floor are already impossible for the recurrence itself, while circuits above it still
require an actual sound code and, if that code has a label, must pay the stronger `500` floor.
Existing counterexamples, normalization results, and rejected schedules remain unchanged.

Focused elaboration and the full `lake build` passed (8,068 jobs).  All three new capstones print
only `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, custom axiom, `unsafe`,
or `native_decide` was introduced.

The precise next frontier is to define the circuit-level soundness interface for a conditioned
first-round code and prove its minimal nonemptiness consequence on a nonempty bad fiber.  Then test
its actual label count against the `500 * 26^(d-1) * T` threshold and audit the more expensive
later alphabets.  If the intended circuit lies below the `260` baseline, the current product-demand
form is already closed without that construction.  Non-product density theorems remain outside
this obstruction.  No P-versus-NP conclusion follows.

### Decoder soundness turns realized bad fibers into label lower bounds

The conditioned-code semantic interface is now explicit.  `ConditionedFirstRoundCode bad` stores
an endpoint and finite label for each root in the actual finite bad set, together with a decoder
that reconstructs the root from that pair.  It does not assume a particular prefix encoder or
density estimate, so future candidate encoders can be compared through one common obligation.

Decoder soundness now proves three kernel-checked consequences:

* `(endpoint root, encode root)` is injective on all actual bad roots;
* labels alone are injective on every fixed endpoint fiber, and hence
  `card(endpoint fiber) <= labelCard`;
* a nonempty actual bad set forces `0 < labelCard`.

The capstone `widthTwoParity_conditionedCodeSchedule_not_fit_of_nonempty_bad` connects this last
fact to the exact recurrence.  If the first charged key count is the code's finite label
cardinality, then any decoder-sound code on a nonempty bad set inherits the already audited floor

```text
500 * 26^(d-1) * T <= bottomSlotCount C.
```

Thus the optimistic empty-alphabet possibility is no longer available once an actual bad root and
a decoder-sound conditioned code are supplied.  More quantitatively, the maximum realized
endpoint-fiber cardinality is now a formal lower bound on the alphabet, so a large fiber can be
tested directly against the full `(240*A+260)` threshold.  This remains an obstruction for the
present product-demand recurrence, not a lower bound against other density mechanisms.

Focused elaboration of the quantitative-iteration module passed.  The new interface capstones
print only `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, custom axiom,
`unsafe`, or `native_decide` was introduced.  Existing normalization results, counterexamples,
and failed schedules remain preserved.

The precise next frontier is to instantiate `ConditionedFirstRoundCode` with the existing
circuit-owned prefix/successor construction and identify its actual bad-root endpoint fibers.
Prove either a sufficiently small uniform fiber/label construction satisfying
`(240*A+260)*26^(d-1)*T <= bottomSlotCount C`, or a concrete realized fiber whose cardinality
violates that bound.  After the first alphabet passes, the necessarily more expensive later
alphabets still require a separate audit.  Non-product density theorems remain outside this
obstruction.  No P-versus-NP conclusion follows.

### The ragged symmetric-prefix encoder now implements the conditioned-code interface

The abstract decoder obligation is now discharged by the existing circuit-owned prefix
construction.  `ConditionedFirstRoundCode.ofInjectivePair` packages any finite endpoint/label map
whose pair is injective, using finite search to decode the unique source root.
`commonShallowBadPrefixCode` applies this constructor to the actual semantic bad set, with:

* endpoint `freshTaggedPrefixEndpoint` selected by `commonShallowBadAssignment`;
* label `canonicalPrefixActualSymLabel`, consisting of fresh literal positions and the symmetric
  multiset of realized ragged `(gate, term)` keys;
* soundness supplied by the already proved endpoint-plus-label reconstruction theorem on the
  ample-fuel shell.

The charged ambient alphabet is therefore exact:

```text
(w+1)^prefixDepth
  * (choose(totalClauseOccurrences + prefixDepth - 1, prefixDepth) + 1).
```

The capstone `widthTwoParity_commonShallowBadPrefixCode_firstKey_bound` substitutes this concrete
cardinality into the depth-sensitive product schedule.  Any fitting width-two parity schedule
whose first key count is this code's label cardinality must satisfy

```text
(240 * ambientPrefixAlphabet + 260) * 26^(d-1) * T
  <= bottomSlotCount C.
```

This completes the requested semantic instantiation, but it also makes clear that the ambient
ragged symmetric alphabet is not yet the hoped-for conditioned compression: it charges every
possible label, while the earlier endpoint-image theorem counts only labels actually realized in
each bad-root fiber.  No claim that this ambient alphabet fits the schedule is made.

Focused elaboration of the quantitative-iteration module passed.  The new definitions and
capstones print only `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, custom
axiom, `unsafe`, or `native_decide` was introduced.  Existing counterexamples and failed schedules
remain preserved.

The precise next frontier is to replace the ambient `PrefixActualSymLabel` charge by a single
finite type representing the union (or dependent sum with an amortized endpoint charge) of the
actual endpoint-local realized label images.  Prove decoder soundness for that smaller alphabet
and compare its exact cardinality with
`(bottomSlotCount C / (26^(d-1)*T) - 260) / 240`.  If this still fails, extract a concrete realized
endpoint fiber exceeding the threshold; if it fits, thread the realized alphabet into the later
round recurrence.  Non-product density theorems remain outside this obstruction.  No
P-versus-NP conclusion follows.

### The first-round code now charges only globally realized labels

The ambient-label gap is now removed at the code interface.  For every decoder-sound
`ConditionedFirstRoundCode`, `realizedLabelImage` is the finite image of its encoder on the actual
bad-root domain, and `restrictToRealizedLabels` replaces the ambient label type by the subtype of
that image.  The restricted code remains decoder-sound because endpoint-plus-label injectivity is
preserved under the subtype embedding.

Kernel-checked cardinality theorems prove exactly

```text
restricted labelCard = card(realizedLabelImage),
card(realizedLabelImage) <= ambient labelCard,
card(realizedLabelImage) <= card(actual bad roots).
```

`commonShallowBadRealizedPrefixCode` applies this construction to the ragged symmetric-prefix
encoder.  Hence it is a concrete sound code for the semantic common-shallow bad set with every
unused stars-and-bars label removed.  The capstone
`widthTwoParity_commonShallowBadRealizedPrefixCode_firstKey_bound` now tests its exact global
realized-image cardinality against the full depth-sensitive obligation:

```text
(240 * card(realizedLabelImage) + 260) * 26^(d-1) * T
  <= bottomSlotCount C.
```

This is a genuine improvement over the ambient alphabet, but it is not yet the optimal
endpoint-conditioned charge.  The same abstract label symbol may be reused independently at
different endpoints; the global union does not perform such renaming, so it can exceed the
largest endpoint-fiber cardinality.  No numerical claim that the realized image fits the parity
schedule is made, and all earlier counterexamples and rejected schedules remain preserved.

Focused elaboration of the quantitative-iteration module passed.  The new definitions and
capstones use only `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, custom
axiom, `unsafe`, or `native_decide` was introduced.

The precise next frontier is to construct a common alphabet of size exactly the maximum realized
endpoint-fiber cardinality, reindexing labels separately inside each endpoint fiber, and prove
decoder soundness.  Then compare that optimal conditioned first-round count with
`(bottomSlotCount C / (26^(d-1)*T) - 260) / 240`.  If it fails, extract a concrete oversized
endpoint fiber; if it fits, audit the actual later-round fiber maxima.  A non-product density
theorem remains outside this obstruction.  No P-versus-NP conclusion follows.

### The optimal endpoint-conditioned alphabet is now realized exactly

The endpoint-local reindexing step is complete.  `maxRealizedEndpointFiberCard` takes the finite
supremum of the cardinalities of all endpoint fibers actually reached by bad roots.  Unrealized
endpoint fibers are proved empty and hence bounded by that same maximum.  For each endpoint,
`maxFiberEmbedding` chooses a single injection of its fiber into
`Fin maxRealizedEndpointFiberCard`; `maxFiberEncode` uses that injection, allowing independent
endpoints to reuse every rank.

`endpoint_maxFiberEncode_injective` proves that endpoint plus local rank reconstructs the root,
and `restrictToMaxEndpointFiber` packages this map as a decoder-sound conditioned code.  Its exact
charged cardinality is

```text
labelCard = maxRealizedEndpointFiberCard.
```

This is optimal, not merely an upper bound: `maxRealizedEndpointFiberCard_le_labelCard` proves that
the maximum realized fiber is a lower bound for every decoder-sound code with that endpoint map.
Thus the gap between a global realized-label union and endpoint-local reuse is completely removed
at the abstract code interface.

`commonShallowBadMaxFiberPrefixCode` instantiates the optimal construction for the actual ragged
symmetric-prefix endpoint map.  The exact depth-sensitive schedule theorem
`widthTwoParity_commonShallowBadMaxFiberPrefixCode_firstKey_bound` now says that any fitting
product-aware width-two parity schedule using this optimal first-round alphabet must satisfy

```text
(240 * maxRealizedEndpointFiberCard + 260) * 26^(d-1) * T
  <= bottomSlotCount C.
```

Focused elaboration passed.  The new definitions and capstones print only `propext`,
`Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was introduced.  Earlier counterexamples and rejected schedules remain preserved.

The precise next frontier is now quantitative rather than representational: bound or calculate the
maximum realized endpoint fiber for the intended dense-support parity first round and compare it
with `(bottomSlotCount C / (26^(d-1)*T) - 260) / 240`.  If it exceeds the threshold, retain a
specific endpoint and its oversized bad-root fiber as the obstruction; if it fits, construct the
same endpoint-optimal alphabets after collapse and audit their actual later-round maxima.  A
non-product density theorem remains outside this obstruction.  No P-versus-NP conclusion follows.

### Endpoint fibers have a fixed-coordinate binomial ceiling

The first quantitative bound on the optimal endpoint-conditioned alphabet is now kernel checked.
For a fixed endpoint `kappa`, every root in its canonical bad-prefix fiber is recovered from the
set of `d` variables that the prefix fixed.  Those variables form a `d`-subset of the coordinates
already fixed at `kappa`, so the fiber injects into that endpoint-local powerset and satisfies

```text
endpointFiberCard kappa <= choose (n - stars kappa) d.
```

On the exact `K`-live bad shell, every realized endpoint has exactly `K-d` live coordinates.
Consequently both the maximum realized fiber and the exact optimal code alphabet satisfy

```text
maxRealizedEndpointFiberCard <= choose (n - (K-d)) d,
optimal labelCard            <= choose (n - (K-d)) d.
```

This removes the circuit's gate count, clause count, width, and ambient symmetric label space from
the first-round upper bound.  It is only a ceiling: it does not assert that every candidate subset
is realized, and therefore does not by itself show that the product-aware schedule fits or fails.
All earlier obstructions and failed schedules remain preserved.

Focused elaboration of the quantitative-iteration module passed.  The new capstones print only
`propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was introduced.

The precise next frontier is to exploit the semantic badness condition inside one endpoint fiber,
which the purely combinatorial powerset injection deliberately ignores.  Prove a smaller realized
subset bound for the intended width-two dense-support parity first round, or exhibit a concrete
endpoint realizing enough of the `choose (n-(K-d),d)` candidates to violate
`(240*A+260)*26^(depth-1)*T <= bottomSlotCount C`.  If the first-round count fits, repeat the same
fiber audit after collapse.  No P-versus-NP conclusion follows.

### Endpoint fibers are now exact filtered powerset counts

The semantic information discarded by the fixed-coordinate binomial ceiling is now exposed as an
exact finite counting problem.  For each endpoint `kappa`,
`commonShallowBadPrefixCandidateSets` filters the endpoint-local `d`-subsets by all conditions
needed for realization.  For a candidate set `S`, it reconstructs the only possible root
`freeOn kappa S` and requires:

* that reconstructed root belongs to the semantic common-shallow bad set;
* its canonical bad assignment selects exactly `S` as the fresh prefix variables;
* running that prefix returns to `kappa`.

The kernel-checked equivalence
`commonShallowBadPrefixCandidateSets_card_eq_endpointFiberCard` proves that this filtered family's
cardinality is exactly the endpoint fiber cardinality, not merely an upper bound.  Consequently,
`commonShallowBadMaxFiberPrefixCode_labelCard_eq_sup_candidateSets` identifies the optimal charged
alphabet exactly with the supremum of these filtered cardinalities over realized endpoints.

This does not yet improve the numerical ceiling: in the dense-support regime the unfiltered
ambient family can still have size `choose (n-(K-d),d)`.  It does, however, isolate the only
remaining source of a strict saving—the acceptance rate of the explicit semantic/canonical
filter—and supplies a finite object that can be specialized or evaluated for a concrete circuit
family.  Earlier counterexamples, failed schedules, and the binomial obstruction remain intact.

Focused elaboration of the quantitative-iteration module passed.  The new capstones print only
`propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was introduced.

The precise next frontier is to instantiate the filtered candidate family for the intended
normalized width-two dense-support parity first round.  Prove a uniform acceptance bound strong
enough for `(240*A+260)*26^(depth-1)*T <= bottomSlotCount C`, or retain a specific realized
endpoint and enough accepted `d`-subsets to violate it.  If the first-round maximum fits, apply the
same exact filtered count after collapse.  No P-versus-NP conclusion follows.

### Normalized width-two parity endpoints now have an exact witness test

The filtered candidate count is now connected to the intended circuit family rather than left at
the generic gate-family interface.  For a width-two layered circuit `C` computing parity up to a
fixed output phase, the theorem `widthTwoParity_normalizedCandidateSets_firstKey_bound` instantiates
the code with `normalizedLayeredBottomFamily C`.  Duplicate-freedom and width transfer are supplied
by the existing normalization bridge, so no extra clause-list invariant is assumed.

For every root in the actual semantic bad set, let `kappa` be its canonical prefix endpoint and let
`accepted(kappa)` be the exact filtered family of endpoint-local `prefixDepth`-subsets.  If the
depth-sensitive product-aware schedule fits and charges the optimal endpoint-conditioned first
alphabet, the kernel-checked conclusion is

```text
(240 * card(accepted(kappa)) + 260) * 26^(rounds-1) * terminal
  <= bottomSlotCount C.
```

The companion theorem `widthTwoParity_normalizedCandidateSets_not_fit_of_oversized` packages the
contrapositive.  A single explicitly realized endpoint violating this inequality refutes the
present product schedule.  This is stronger operationally than the preceding supremum formula:
future finite evaluations or structural arguments can retain one root and its accepted subsets,
without first calculating the maximum over all endpoints.

No acceptance-rate saving is claimed.  Parity semantics forces full bottom-variable support but
does not by itself specify the normalized clause representation or the canonical bad-prefix
selection, so the current hypotheses cannot manufacture a numerical candidate count.  The new
theorems instead isolate exactly the additional representation-specific evidence required and
preserve the oversized-fiber route as a formal obstruction.

Focused elaboration of the quantitative-iteration module and the full `lake build` passed (8,068
jobs).  The two new capstones print only `propext`, `Classical.choice`, and `Quot.sound`; no
`sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was introduced.  Earlier
counterexamples, normalization results, and failed schedules remain preserved.

The precise next frontier is to supply one concrete normalized width-two parity representative
and evaluate or bound `accepted(kappa)` at a realized root.  Either prove every realized endpoint
meets the displayed slot budget, then repeat the endpoint audit after collapse, or retain one root
and a certified family of accepted subsets large enough to invoke the new obstruction theorem.
A representation-independent acceptance estimate would require an additional structural theorem
beyond full semantic support.  No P-versus-NP conclusion follows.

### The smallest normalized parity endpoint is an explicit obstruction

The endpoint test has now been instantiated on a concrete circuit rather than left conditional.
`xorTwoLayered` is the duplicate-free two-clause DNF for parity on two variables.  It computes
parity exactly, has bottom width two, and has bottom-slot count two.  Its normalized layered bottom
family contains both polarities through the existing coverage bridge.

At `fuel = K = 2`, prefix depth one, and residual depth zero, the fully live root is proved to be
in the actual semantic bad event.  The proof is structural: a depth-one common trunk leaves at
least one coordinate live on every followed leaf, while the positive bottom gate still computes
parity on that leaf and therefore has positive canonical depth.  Thus the witness is not an
external family substituted for the normalized circuit interface.

For that root's canonical endpoint, the exact filtered candidate family satisfies

```text
card(accepted(kappa)) = 1.
```

Positivity is supplied by the realized root itself.  The already proved endpoint-fiber binomial
ceiling gives the matching upper bound `choose(2-(2-1),1) = 1`.  The capstone
`xorTwo_productAwareSchedule_not_fit_of_optimal_normalized_firstKey` then invokes the oversized-
endpoint theorem with one round and terminal survivor one.  The required first-key budget is

```text
(240 * 1 + 260) * 26^0 * 1 = 500,
```

but the representative has only two bottom slots.  Consequently this concrete optimal
endpoint-local product schedule does not fit.

This is a calibrated obstruction, not a large-`n` acceptance-rate lower bound.  It shows that
normalization and endpoint-local label reuse do not make the present product schedule universally
valid, even at the smallest positive-prefix parity instance.  It does not decide whether the
intended dense-support asymptotic regime has sufficiently small realized fibers.

Focused elaboration and the full project build passed.  The new capstones use only the standard
logical axioms already present (`propext`, `Classical.choice`, and `Quot.sound` where finite
endpoint choices enter); no `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was added.
Earlier counterexamples and failed routes remain preserved.

The precise next frontier is to determine whether this one-candidate obstruction scales.  Build a
parameterized normalized width-two parity representative with positive prefix depth and prove
either (i) a realized endpoint-fiber lower bound that outgrows
`(bottomSlotCount / (26^(rounds-1)*terminal) - 260) / 240`, or (ii) a uniform upper bound showing
that all realized endpoints fit in the intended large-`n` schedule.  If (ii) holds, repeat the
exact endpoint audit after the first collapse.  No P-versus-NP conclusion follows.

### Residual-depth-zero parity badness scales to the entire shell

The semantic part of the two-bit obstruction is now parameterized and representation-independent.
The new theorem `parity_mem_normalized_commonShallowBad_zero` applies to every layered circuit `C`
computing parity XOR a fixed phase.  If an exact shell root has `stars sigma = K`, ample fuel
`K <= fuel`, and the common trunk budget satisfies `trunkDepth < K`, then

```text
sigma ∈ commonShallowBad (normalizedLayeredBottomFamily C)
  fuel K trunkDepth 0.
```

The proof exposes the missing semantic invariant.  A common trunk shorter than the live dimension
leaves a live coordinate on a followed leaf.  Residual depth zero makes the canonical tree of both
polarities of every bottom gate constant on that leaf subcube.  A structural induction through the
layered circuit then makes the whole circuit invariant under flipping the surviving coordinate,
contradicting parity's sensitivity.  The supporting lemmas
`dnfValue_eq_of_canonicalDT_depth_eq_zero` and
`Layered.eval_eq_of_bottom_canonicalDT_depth_eq_zero` record those two constant-subcube steps.

Consequently `parity_normalized_commonShallowBad_zero_eq_shell` identifies the bad event exactly
with the whole `K`-star shell, and `parity_normalized_commonShallowBad_zero_card` gives

```text
card(commonShallowBad ...) = choose(n,K) * 2^(n-K).
```

Thus the semantic badness predicate in `commonShallowBadPrefixCandidateSets` accepts every shell
root in the intended residual-zero parity regime.  Any strict endpoint-fiber saving must come from
the canonical-prefix selection and endpoint equations, not from an acceptance-rate estimate for
common-shallow badness.  This strengthens the two-bit calibration without yet proving that one
endpoint receives an asymptotically oversized fraction of the shell.

Focused elaboration and the full `lake build` passed (8,068 jobs).  The four new printed capstones
depend on no axioms; no `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was introduced.
Earlier counterexamples and failed schedules remain preserved.

The precise next frontier is now a canonical-map fiber theorem on the full shell.  For a
parameterized normalized width-two parity representative, prove a lower bound on the largest
fiber of `commonShallowBadPrefixCode.endpoint` (for example by dividing the exact full-shell count
by a proved endpoint-image bound), then compare it with the product-aware slot threshold.  If that
lower bound fits instead of obstructing, calculate the corresponding endpoint maximum after the
first collapse.  No P-versus-NP conclusion follows.

### The canonical endpoint map now has an exact shell-balance lower bound

The proposed largest-fiber counting step is now kernel-checked.  The generic theorem
`bad_card_le_maxRealizedEndpointFiberCard_mul_endpointImage_card` proves, for every sound
conditioned code, that the actual bad-root population is at most the largest realized endpoint
fiber times the exact number of realized endpoints.  It retains the exact endpoint image and so
does not prematurely charge the full ambient restriction space.

For the canonical bad-prefix code,
`commonShallowBad_card_le_maxFiber_mul_endpointShell_card` proves that every realized endpoint has
exactly `K-d` live coordinates and relaxes only the endpoint image to that exact shell.  Combining
this with the preceding full-shell parity badness theorem gives
`parity_normalized_maxFiber_mul_endpointShell_lower`:

```text
choose(n,K) * 2^(n-K)
  <= maxRealizedEndpointFiberCard
       * (choose(n,K-d) * 2^(n-(K-d))).
```

This is representation-independent: it requires only a layered parity representative, a bottom-
width bound needed by the canonical code, ample fuel, residual depth zero, and `d < K`.  It is the
requested stars-and-bars shell balance in division-free natural-number form.  It also identifies
the quantitative issue precisely: the useful lower bound is the ratio of consecutive or separated
restriction-shell sizes.  No unproved claim is made that this ratio already exceeds the product-
aware slot threshold for the intended multi-round parameters.

Focused elaboration and the full project build passed.  The three new printed capstones use only
the existing standard logical axioms (`propext`, `Classical.choice`, and `Quot.sound`); no `sorry`,
`admit`, custom axiom, `unsafe`, or `native_decide` was added.  Earlier counterexamples, exact
candidate filters, and failed schedules remain preserved.

The precise next frontier is to simplify this shell ratio at the intended parameters.  First prove
a cancellation-friendly lower bound for
`choose(n,K) * 2^(n-K) / (choose(n,K-d) * 2^(n-K+d))`, then compare it with
`(bottomSlotCount / (26^(rounds-1)*terminal) - 260) / 240`.  If the ratio is too small, the exact
realized endpoint image—not the whole `(K-d)` shell—must be bounded next.  No P-versus-NP
conclusion follows.

### The endpoint-shell ratio now cancels exactly and has an intended-density power form

The shell ratio has now been simplified without division.  The theorem
`parity_normalized_endpointShell_ratio_lower` combines the full-shell parity balance with the
exact endpoint/coordinate-set identity and cancels the positive `K`-shell factor.  Under the
necessary nonvacuity hypothesis `K <= n`, it proves

```text
choose(n-(K-d),d)
  <= maxRealizedEndpointFiberCard * choose(K,d) * 2^d.
```

This is the exact cancellation-friendly natural-number statement: the numerator counts the ways
to restore the `d` coordinates lost at an endpoint, while `choose(K,d) * 2^d` is precisely the
within-root choice and Boolean-assignment cost.  The explicit `K <= n` guard prevents cancellation
from an empty source shell.

The companion `parity_normalized_endpointShell_power_lower` combines the same population balance
with the already verified binomial shell-ratio inequality.  It gives the more immediately
comparable cleared-denominator consequence

```text
(n-K+1)^d <= maxRealizedEndpointFiberCard * (2*K)^d.
```

Finally, `parity_normalized_intended_endpointShell_power_lower` instantiates the density used by
the realized-prefix contraction, namely `n = 1000*A*r`, `K = 20*r`, and `d = 10*r`:

```text
(1000*A*r - 20*r + 1)^(10*r)
  <= maxRealizedEndpointFiberCard * (40*r)^(10*r).
```

Thus the ambient endpoint-shell relaxation forces a fiber with an effective per-prefix scale of
roughly `25*A`; it is not merely a qualitative pigeonhole statement.  This still does not by
itself decide the product-aware slot test: the current interface has no proved relation connecting
`A`, `r`, the number of rounds, terminal survivor budget, and `bottomSlotCount C` for a
parameterized normalized width-two parity representative.  In particular, the small two-bit
obstruction cannot simply be extrapolated to this density.

Focused elaboration of the quantitative-iteration module passed.  All three new printed capstones
depend only on `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, custom axiom,
`unsafe`, or `native_decide` was introduced.  Earlier counterexamples, exact candidate filters,
and failed schedules remain preserved.

The precise next frontier is to close the parameter interface to the product-aware threshold.
For a concrete parameterized normalized width-two parity representative, relate
`bottomSlotCount C` and the later-round factor `26^(rounds-1)*terminal` to `A` and `r`, then compare
that bound against the displayed `(25*A)^(10*r)`-scale forced fiber.  If the available circuit
size dominates this lower bound, the ambient `(K-d)` endpoint shell is too coarse and the next
necessary step is a strict bound on the exact realized endpoint image.  No P-versus-NP conclusion
follows.

### The endpoint-shell fiber and product-aware slot threshold now compose exactly

The parameter interface has now been closed in cleared-denominator form.  The theorem
`parity_normalized_intended_productAware_slot_lower` composes the intended-density endpoint-shell
power lower bound with the exact depth-sensitive first-key obligation.  For a normalized
width-two parity representative on `1000*A*r` variables, if the optimal endpoint-local first
alphabet is charged and a positive-round product-aware schedule fits, then

```text
(240*(1000*A*r - 20*r + 1)^(10*r) + 260*(40*r)^(10*r))
  * (26^(rounds-1)*terminal)
<= bottomSlotCount(C) * (40*r)^(10*r).
```

Thus the actual bottom-slot count must dominate the forced roughly `(25*A)^(10*r)` endpoint
fiber after multiplication by the unavoidable later-round factor.  The companion theorem
`parity_normalized_intended_productAware_not_fit_of_slot_gap` proves the exact contrapositive:
strict failure of the displayed slot inequality refutes the present product-aware schedule even
when it uses the optimal endpoint-conditioned canonical-prefix alphabet.

This resolves the previously missing relation among `A`, `r`, `rounds`, `terminal`, and
`bottomSlotCount C`, but it does not decide the comparison without an independent upper bound on
the slot count of a parameterized width-two parity representative.  In particular, the existing
semantic support theorem supplies only the opposite-direction lower bound
`1000*A*r <= 2*bottomSlotCount C`.

Focused elaboration and the full `lake build` passed (8,068 jobs).  Both new printed capstones depend only on `propext`,
`Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide` was introduced.  Earlier counterexamples and failed schedules remain preserved.

The precise next frontier is to construct or identify a parameterized normalized width-two
parity representative with a proved upper bound on `bottomSlotCount`, and test that upper bound
against the displayed necessary scale.  If every available representative is large enough to
pay it, the ambient endpoint shell remains too coarse and the next necessary step is a strict
upper bound on the exact realized endpoint image.  No P-versus-NP conclusion follows.

### An explicit width-one parity representative has exact exponential slot count

The requested parameterized representative now exists in the kernel-checked circuit syntax.
`widthOneParityLayered n` is the OR of the exact-assignment conjunctions for all odd-parity
assignments.  Each assignment conjunction is built from `n` separate one-literal bottom DNFs, so
the construction satisfies `BottomWidth 2` (indeed width one) without hiding a full-width parity
minterm inside one bottom clause.  It also satisfies `BottomClean`, since every bottom gate is a
singleton clause containing one literal.

The semantic and accounting interfaces are exact:

```text
Layered.eval (widthOneParityLayered n) x = parity x
bottomSlotCount (widthOneParityLayered n) = n * 2^(n-1)    (1 <= n).
```

Thus the first available uniform upper bound is exponential in the ambient variable count.  At
`n = 1000*A*r` it is far too coarse to refute the product-aware necessary condition whose forced
fiber has the roughly `(25*A)^(10*r)` scale: this representative has enough syntactic capacity
that the previous slot-gap contrapositive cannot be discharged merely from its exact size formula.
This is a negative audit result about the current representative, not evidence that the schedule
fits; later-round and terminal factors remain part of the exact inequality.

Focused elaboration of the quantitative-iteration module passed (8,452 jobs).  The four new
printed capstones use only `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`,
custom axiom, `unsafe`, or `native_decide` was introduced.  Earlier counterexamples and failed
routes remain preserved.

The precise next frontier is therefore a representation-sensitive fork.  Either construct a
subexponential (ideally parameter-polynomial) normalized width-two parity representative with a
proved slot upper bound and rerun the exact slot-gap test, or prove a strict upper bound on the
exact realized endpoint image for `widthOneParityLayered` that exploits its assignment-conjunction
structure.  The latter is the higher-information route for the existing concrete family.  No
P-versus-NP conclusion follows.

### The explicit parity circuit has a linear two-polarity covering family

The representation-sensitive audit has separated circuit slot count from common-switching family
size.  Although `widthOneParityLayered n` contains `n * 2^(n-1)` bottom-slot occurrences, every
bottom gate is just one of the two singleton polarities on one coordinate.  The new family
`widthOneParityCompactFamily n` indexes those values directly by `Fin (n+n)`.

The kernel-checked interfaces are exact:

```text
forall g, length(widthOneParityCompactFamily n g) = 1
sum_g length(widthOneParityCompactFamily n g) = 2*n
```

Every gate is duplicate-free and width one.  More importantly,
`widthOneParityCompactFamily_covers` proves `CoversLayeredBottoms` for the original exponential-slot
circuit: for every syntactic bottom gate, the compact family contains canonical trees equal to
both that gate and its De Morgan polarity.  Hence the existing common-trunk leaf-collapse bridge
can consume the compact family without changing the circuit semantics.

This removes the exponential indexed-gate/term-key charge from the first-round encoder for this
representative.  It does **not** reduce `bottomSlotCount C`, which remains exponential and is the
capacity appearing on the other side of the product-aware fit test.  It also does not yet identify
the compact family's exact endpoint map with the endpoint map previously audited for
`normalizedLayeredBottomFamily C`; those are different indexed families and may choose different
canonical witnesses.

Focused elaboration and the full project build passed.  The new capstones use only the standard
logical axioms already present; no `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was
introduced.  Earlier counterexamples and failed routes remain preserved.

The precise next frontier is to rerun the conditioned first-round endpoint construction with
`widthOneParityCompactFamily`.  First prove its residual-depth-zero bad event is the full shell
using `widthOneParityCompactFamily_covers`, then characterize its canonical query order (the two
singleton polarities should reduce it to a coordinate-order endpoint map) and compute or tightly
bound the resulting maximum realized endpoint fiber.  Only after that should the exact
product-aware slot comparison be repeated.  No P-versus-NP conclusion follows.

### The compact covering family has exact full-shell residual-zero badness

The semantic half of that frontier is now discharged.  The parity contradiction has been
factored through the actual bridge interface rather than tied to
`normalizedLayeredBottomFamily`.  The new theorem
`parity_mem_covered_commonShallowBad_zero` applies to any finite gate family satisfying
`CoversLayeredBottoms gates C`: if `C` computes parity up to a phase, `K <= fuel`, and
`trunkDepth < K`, every restriction with exactly `K` live variables belongs to
`commonShallowBad gates fuel K trunkDepth 0`.  The matching equality and cardinality theorems are

```text
commonShallowBad gates fuel K trunkDepth 0
  = {sigma | stars sigma = K}
card(commonShallowBad gates fuel K trunkDepth 0)
  = choose(n,K) * 2^(n-K).
```

Instantiating coverage with `widthOneParityCompactFamily_covers` yields
`widthOneParityCompactFamily_commonShallowBad_zero_eq_shell` and its exact-cardinality companion.
Thus replacing the exponential occurrence indexing by the linear `2n` family does not obtain any
semantic acceptance saving at residual depth zero: the conditioned encoder still receives the
entire exact shell.  Any saving must come from how the compact family's canonical witness rule
maps those roots to endpoints, not from fewer roots being bad.

Focused elaboration of the quantitative-iteration module passed.  The new printed capstones use
only `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, custom axiom, `unsafe`,
or `native_decide` was introduced.  Earlier counterexamples and failed routes remain preserved.

The precise next frontier is to characterize the compact family's canonical selector stream.
Prove which of the positive/negative singleton gates is selected at each live coordinate (including
the tie order inherited from `Fin (n+n)`), derive the resulting coordinate-order prefix endpoint,
and compute or tightly bound its maximum realized full-shell fiber.  Then rerun the exact
product-aware slot comparison with that fiber and the representative's unchanged exponential slot
capacity.  No P-versus-NP conclusion follows.

### The compact singleton selector and polarity order are now exact

The local canonical-selector calculation is now kernel-checked.  At every positive fuel, for each
coordinate `i` and either singleton polarity, the assignment-followed witness stream is exactly

```text
runWitSeq [[±i]] (fuel+1) sigma x
  = if sigma i = none then [(0,0)] else [].
```

The result is independent of the extending assignment `x`: a live singleton contributes its sole
query, while a fixed singleton contributes none.  The companion tagged-decoding theorem proves
that the positive and negative entries both decode to the same coordinate `i`.

The index-order ambiguity is also resolved.  The theorem
`widthOneParityCompactFamily_positive_before_negative` proves that every `Fin.castAdd n i`
(positive singleton) precedes every `Fin.natAdd n j` (negative singleton) in `Fin (n+n)`.  Since
`taggedRawWitSeq` concatenates in this order and `freshTaggedAux` is a stable first-occurrence
filter, the positive copy is necessarily the winner whenever the two polarities duplicate a live
coordinate.  There is no polarity-dependent or cross-half tie left in the selector semantics.

Focused elaboration of the quantitative-iteration module passed.  The four new printed capstones
depend only on the standard logical axioms `propext` and `Quot.sound`; no `sorry`, `admit`, custom
axiom, `unsafe`, or `native_decide` was introduced.  Earlier counterexamples and failed routes
remain preserved.

The precise next frontier is to lift these local facts through `List.ofFn`, `List.flatten`, and the
stable freshness filter: prove that the decoded `freshTaggedWitSeq` is exactly the increasing list
of live coordinates, then identify `freshTaggedPrefixEndpoint` with fixing its first `d` entries.
That identity should make the full-shell endpoint fiber count a direct combinatorial calculation,
after which the exact product-aware slot comparison can be rerun.  No P-versus-NP conclusion
follows.

### The compact fresh selector stream is exactly the increasing live-coordinate list

The list-level lift is now kernel-checked.  At every positive fuel,
`widthOneParityCompactFamily_taggedRawWitSeq` expands the raw selector into two explicit passes:
the increasing positive-polarity entries at the live coordinates, followed by the corresponding
increasing negative-polarity entries.  This equality traverses the actual `List.ofFn` and
`List.flatten` definitions and is independent of the extending assignment.

The stable first-occurrence filter has also been computed exactly.  The stronger tagged theorem is

```text
freshTaggedWitSeq (widthOneParityCompactFamily n) (fuel+1) sigma x
  = positive entries at {i | sigma i = none}, in increasing i order.
```

Thus every negative duplicate is removed and the positive entry is the canonical winner.  Decoding
gives the requested coordinate identity:

```text
filterMap taggedWitVar? (freshTaggedWitSeq ...)
  = (List.finRange n).filter (fun i => sigma i = none).
```

This closes the selector-order ambiguity completely; neither polarity nor the extending assignment
affects the decoded stream.  Focused elaboration of the quantitative-iteration module passed, and
the new capstones introduce no prohibited proof mechanism.  Earlier counterexamples and failed
routes remain preserved.

The precise next frontier is to push this exact stream identity through `List.take` and `fixOn`:
identify `freshTaggedPrefixEndpoint` with fixing the first `d` live coordinates in increasing order,
then count the exact full-shell endpoint fibers.  Only after that exact fiber calculation should the
product-aware slot comparison be rerun.  No P-versus-NP conclusion follows.

### The compact prefix endpoint is the ordered live-coordinate fixing map

The selector identity has now been pushed through the actual prefix and endpoint definitions.
The new set-level theorem is

```text
freshTaggedPrefixVars (widthOneParityCompactFamily n) (fuel+1) sigma x d
  = ((finRange n).filter (fun i => sigma i = none)).take(d).toFinset.
```

Consequently `widthOneParityCompactFamily_freshTaggedPrefixEndpoint_eq_fixOn` identifies the
canonical endpoint exactly with `fixOn sigma` on that set.  The selected coordinates depend only
on the root restriction and are the first `d` live coordinates in increasing ambient order; the
extending assignment supplies only the Boolean values written at those coordinates.  Polarity,
duplicated circuit occurrences, and the rest of the assignment do not affect selection.

Focused elaboration of the quantitative-iteration module passed (8,452 jobs).  The two new
printed capstones use only `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`,
custom axiom, `unsafe`, or `native_decide` was introduced.  Earlier counterexamples and failed
routes remain preserved.

The precise next frontier is now the exact full-shell fiber calculation for this ordered fixing
map.  For an endpoint whose residual live set is `E`, characterize every preimage as re-freeing a
`d`-set strictly below `min(E)` (with the endpoint already determining the restored Boolean
values), prove the resulting binomial cardinality including the `E = empty` boundary, and then
rerun the product-aware slot comparison.  No P-versus-NP conclusion follows.

### Ordered endpoint fibers have a sharp coordinate envelope, but not an exact binomial yet

The ordered-prefix calculation has now been transferred to the actual conditioned candidate
sets for `widthOneParityCompactFamily`.  Every candidate over an endpoint `kappa` is a `d`-set
inside

```text
independentStrictBelow (freeVars kappa)
  = {i | forall j in freeVars(kappa), i < j}.
```

Consequently its cardinality is at most

```text
choose(card(independentStrictBelow (freeVars kappa)), d).
```

For a nonempty residual live set `E`, this is exactly the coordinate envelope
`choose(min(E),d)`.  For `E = empty`, the strict-below set is all `n` coordinates and the boundary
envelope is `choose(n,d)`.  On a nonempty `(K-d)`-live endpoint shell, the minimum-coordinate
bound recovers `choose(n-(K-d),d)`, exactly the earlier worst-case fixed-coordinate ceiling.
Thus the product-aware comparison receives no uniform improvement from coordinate order alone,
although individual early-starting endpoints can be much smaller.

The previously proposed exact-binomial conclusion is not defensible for the current endpoint
code.  Besides the selected coordinate set, the endpoint stores the Boolean values supplied by
`commonShallowBadAssignment`, which is a classical choice of a deep residual witness.  An ordered
`d`-set is therefore only a coordinate-compatible preimage candidate; it need not reproduce the
fixed endpoint values.  The proved statement is an inclusion and upper bound, and this failed
equality route is retained explicitly rather than assuming value compatibility.

Focused elaboration of the quantitative-iteration module passed.  The five new printed capstones
depend only on `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, custom axiom,
`unsafe`, or `native_decide` was introduced.  Earlier counterexamples and failed schedules remain
preserved.

The precise next frontier is the value-compatibility predicate.  Characterize the restriction of
`commonShallowBadAssignment` to the ordered re-freed prefix, or replace it with an explicit
parity-specific deep-witness assignment whose values are coherent across roots.  Only such a
theorem can decide whether the ordered binomial envelope is attained, or prove a strictly smaller
maximum realized fiber and improve the product-aware slot test.  No P-versus-NP conclusion follows.

### A coherent parity witness attains the ordered binomial envelope

The value-compatibility fork is now resolved for an explicit parity-specific selector.  On every
all-false independent root, the coherent total assignment `independentAssignment n` extends the
root, and the compact two-polarity family has exactly the same budgeted endpoint as the previously
audited positive-singleton family.  The kernel-checked identity is

```text
freshTaggedPrefixEndpoint (widthOneParityCompactFamily n) (fuel+1)
    (independentRoot S) (independentAssignment n) d
  = freshTaggedPrefixEndpoint (independentLiteralGates n) 1
      (independentRoot S) (independentAssignment n) d.
```

For every nonempty residual set `E`, the theorem
`widthOneParityCompactFamily_orderedFiber_bad_and_endpoint` now proves that all roots obtained by
adjoining a `d`-set strictly below `E` lie in the actual residual-depth-zero compact-family parity
bad event and reach the common endpoint `independentRoot E`.  Their exact number is

```text
choose(card(independentStrictBelow E), d).
```

The terminal-segment specialization
`exists_widthOneParityCompactFamily_orderedFiber_maximum_bad` proves that in the proportional
`K = 2d` shell (with `0 < d` and `2d <= n`) this realized bad subfiber has exact size
`choose(n-d,d)`.  Hence the previous worst-case ordered ceiling is attained by a coherent explicit
assignment; it is not an artifact of the Boolean values hidden by `Classical.choose`.  This does
not assert that the existing opaque `commonShallowBadAssignment` realizes the same fiber, but it
rules out value coherence alone as a source of uniform multiplicity improvement.

Focused Lean elaboration passed.  The new capstones use only the standard logical axioms already
present; no `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was introduced.  Earlier
counterexamples and failed routes remain preserved.

The precise next frontier is to package this coherent assignment into the conditioned first-round
code (or generalize that code to accept any proved extending long-prefix assignment), prove its
maximum label cardinality is exactly `choose(n-d,d)` in the `K = 2d` compact parity shell, and rerun
the product-aware slot inequality against the explicit representative's
`n * 2^(n-1)` bottom-slot capacity.  No P-versus-NP conclusion follows.

### The coherent parity assignment gives an exact conditioned alphabet

The explicit witness has now been packaged into a decoder-sound conditioned first-round code on
the entire compact-parity bad shell.  The assignment `restrictionFalseExtension` preserves every
root-fixed value and assigns false only on live coordinates, so it extends arbitrary shell roots;
it is not restricted to the all-false independent slice.  The compact selector has exactly one
fresh entry per live coordinate, which supplies the long-prefix interface required by the existing
ragged symmetric label reconstruction.

After endpoint-local reindexing, the resulting code has the kernel-checked exact alphabet

```text
labelCard = choose(n-d,d)
```

for `K = 2d`, `0 < d`, `2d <= n`, and sufficient fuel.  The upper bound is the fixed-coordinate
fiber injection.  The matching lower bound embeds the previously constructed coherent ordered
fiber into the code's actual endpoint fiber.  Thus the sharp multiplicity is now present inside
the same `ConditionedFirstRoundCode` interface consumed by the product-aware recurrence, rather
than only as an external bad-event subfiber.

The slot comparison has also been rerun for the explicit parity representative.  Any fitting
`rounds`-round schedule whose first key is this exact alphabet must satisfy

```text
(240*choose(n-d,d)+260) * (26^(rounds-1)*terminal)
  <= n*2^(n-1).
```

The right side is the representative's exact bottom-slot count.  Because that representative is
exponentially large, this necessary slot inequality alone is not a contradiction; it clarifies
that the next decisive comparison must return to the ambient survivor budget, not try to extract
a lower bound merely from this deliberately huge circuit's syntactic slot capacity.

Focused elaboration passed.  Printed axioms for the new construction and capstones are only
`propext`, `Classical.choice`, and `Quot.sound`; an intermediate implicit long-trace proof that
briefly exposed `sorryAx` was replaced by an explicit proved lemma before retaining the result.
No `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was added.  Earlier counterexamples
and failed routes remain preserved.

The precise next frontier is to compare the exact first-round demand
`20*(24*choose(n-d,d)+26)` with the ambient shell size `n` in the intended
`n = 1000*A*r`, `d = 10*r` regime.  Prove the strongest valid binomial lower bound needed to decide
fit there, then propagate that decision to the multi-round recurrence; the exponential slot count
should no longer be used as a proxy for ambient capacity.  No P-versus-NP conclusion follows.

### The exact coherent alphabet does not fit the intended ambient shell

The ambient comparison is now decided, without appealing to the representative's exponential
syntactic slot count.  The kernel-checked elementary bound

```text
0 < k < N  implies  N <= choose(N,k)
```

follows directly from Pascal's recurrence.  At positive `A,r`, taking
`n = 1000*A*r` and `d = 10*r` gives `0 < d < n-d`, and hence

```text
n < 20*(24*choose(n-d,d)+26).
```

Thus the exact first-round demand is already larger than the entire ambient live-variable budget.
The theorem `widthOneParity_coherentCode_productAware_not_fit_intended` propagates this strict
inequality through the actual multi-round recurrence: for every positive round count and positive
terminal survivor, no later alphabet sequence can rescue a schedule whose first key is the proved
coherent alphabet `choose(n-d,d)`.  Positivity of the tail budget is the only fact used about later
rounds.

This is a negative result about the present coherent ordered-prefix code, not about all possible
conditioned encoders.  It also identifies the required scale of any replacement: its first charged
alphabet must be at most approximately `n/480`, whereas the current exact alphabet is already at
least `n-d` in this regime.  The previous exponential-slot comparison remains valid but is no
longer relevant to deciding ambient fit.

Focused elaboration of the quantitative-iteration module passed.  Printed axioms for the three new
capstones remain within the standard logical set `propext`, `Classical.choice`, and `Quot.sound`;
none exposes `sorryAx`.  No `sorry`,
`admit`, custom axiom, `unsafe`, or `native_decide` was introduced.  Earlier counterexamples and
failed routes remain preserved.

The precise next frontier is to determine whether endpoint-local labels can be reused across
different endpoints without charging the global maximum fiber as a single alphabet, or prove an
encoder-independent lower bound on the first charged alphabet for the full compact-parity shell.
Any viable replacement must beat the current `choose(n-d,d)` alphabet by a linear factor of roughly
`480` already in round one before the later-round recurrence matters.  No P-versus-NP conclusion
follows.

### The parity shell balance is now encoder-independent

The remaining endpoint-local escape hatch has been isolated at the correct structural level.
`ConditionedFirstRoundCode.bad_card_le_labelCard_mul_endpointShell_card` now applies to any
decoder-sound conditioned code, regardless of its assignment, selector, or label representation.
If every endpoint has exactly `K'` live coordinates, it proves

```text
card(bad) <= labelCard * card(the K'-live restriction shell).
```

Specializing to the full residual-depth-zero normalized parity bad shell gives
`parity_normalized_labelCard_mul_endpointShell_lower`.  Thus every sound code whose round spends
`d` live coordinates satisfies

```text
choose(n,K) * 2^(n-K)
  <= labelCard * (choose(n,K-d) * 2^(n-(K-d))).
```

The cleared-denominator theorem `parity_normalized_labelCard_power_lower` further proves

```text
(n-K+1)^d <= labelCard * (2*K)^d.
```

This lower bound no longer fixes the canonical endpoint map and no longer charges a global union
of endpoint-local labels.  Labels may be reused arbitrarily across endpoints.  The only retained
condition is the structural iteration invariant that a `d`-step first round ends in the
`(K-d)`-live shell.  Consequently, changing the coherent assignment or replacing the ragged
symmetric label format cannot avoid the shell-growth cost while preserving a decoder-sound round
with that live-variable expenditure.

Focused Lean elaboration passed.  The three new printed capstones use only `propext`,
`Classical.choice`, and `Quot.sound`; none exposes `sorryAx`.  No `sorry`, `admit`, custom axiom,
`unsafe`, or `native_decide` was introduced.  Earlier counterexamples and failed routes remain
preserved.

The precise next frontier is quantitative: instantiate the encoder-independent power bound at
`n = 1000*A*r`, `K = 20*r`, and `d = 10*r`, and decide whether it alone forces
`20*(24*labelCard+26) > n` for all positive `A,r`.  If so, every decoder-sound first round that
spends exactly `10*r` live coordinates is ruled out independently of its encoding; otherwise the
remaining possibility must change the endpoint expenditure or weaken exact root reconstruction,
and that altered interface must be audited against the layered collapse semantics.  No
P-versus-NP conclusion follows.

### The encoder-independent power balance rules out the intended first round

The intended-parameter comparison is now decided.  From

```text
(1000*A*r - 20*r + 1)^(10*r)
  <= labelCard * (40*r)^(10*r)
```

and positive `A,r`, the theorem `intended_power_lower_forces_firstRoundDemand` first compares the
left base with `(24*A)*(40*r)`.  Raising to `10*r` and cancelling the positive
`(40*r)^(10*r)` factor gives

```text
(24*A)^(10*r) <= labelCard.
```

The elementary bound `a*b <= a^b` then yields the deliberately coarse but sufficient consequence

```text
240*A*r <= labelCard,
```

so in particular

```text
1000*A*r < 20*(24*labelCard + 26).
```

`parity_normalized_intended_labelCard_demand_exceeds_ambient` instantiates this arithmetic with
the previously proved full-shell balance.  It applies to every decoder-sound conditioned code on
the residual-depth-zero normalized parity bad shell whose endpoints have exactly `10*r` live
coordinates after starting with `20*r`.  It makes no assumption about the assignment, selector,
label format, global versus endpoint-local label reuse, or canonical prefix map.

`parity_normalized_intended_conditionedCode_productAware_not_fit` propagates the strict first-round
inequality through the exact recurrence.  For any positive number of rounds and positive terminal
survivor, no arbitrary sequence of later alphabets can make such a first key fit in the ambient
`1000*A*r` variables; positivity of the remaining least budget is the only later-round fact used.

Focused elaboration of the quantitative-iteration module passed.  The three new printed capstones
use only `propext`, `Classical.choice`, and `Quot.sound`; none exposes `sorryAx`.  No `sorry`,
`admit`, custom axiom, `unsafe`, or `native_decide` was introduced.  Earlier counterexamples,
failed endpoint-fiber equalities, and failed schedules remain preserved.

The precise next frontier is structural rather than another encoding optimization: characterize
the weakest endpoint interface actually sufficient for the layered collapse.  Any viable route at
the intended density must either spend fewer than `10*r` live coordinates in the first round or
weaken exact root reconstruction/decoder soundness.  The next step is to formulate that weakened
interface and prove—or refute—that it still transports the common-trunk leaf collapse semantics;
only then should its altered shell balance and multi-round recurrence be recomputed.  No
P-versus-NP conclusion follows.

### Layered collapse does not consume bad-root reconstruction

The semantic and counting interfaces are now formally separated.  The new predicate
`LayeredCollapseLeafAt fuel sigma x residualDepth C tau` retains exactly the pointwise leaf data
used across an iteration boundary:

```text
RestrictionExtends sigma tau
Rung4Restriction.Extends tau x
stars tau <= stars sigma
Shallows fuel tau (residualDepth + 1) C.
```

It contains no label, decoder, encoding map, or inverse reconstruction of the bad root.
`CommonShallowAt.exists_leaf_layeredCollapseLeafAt` proves that every covered common trunk
produces this payload at each reached leaf while keeping the shared trunk and its depth charge
outside the payload.  Conversely, `LayeredCollapseLeafAt.collapseRound_altO` proves that this
pointwise payload plus the root fuel bound is sufficient for the existing `collapseRound`:
restriction provenance and assignment compatibility are preserved, the leaf remains within fuel,
the collapsed circuit is equivalent on the leaf subcube, its bottom width is at most
`residualDepth + 1`, and one alternating layer is removed.

This identifies the exact role of decoder soundness in the current route.  It is not required by
the layered-collapse semantics; it is used only to turn a proposed bad-root encoding into an
injective endpoint/label count.  Therefore weakening reconstruction does not threaten the leaf
collapse by itself, but it removes the population bound unless a replacement quantitative
condition controls how many bad roots may share one endpoint/label pair.

Focused elaboration of the layered bridge passed.  Printed axioms for both new capstones are within
the standard logical set `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, custom
axiom, `unsafe`, or `native_decide` was introduced.  Earlier counterexamples, failed routes, and
the encoder-independent exact-decoding obstruction remain preserved.

The precise next frontier is to formulate a bounded-ambiguity (list-decoding) counting interface:
permit at most `L` bad roots per endpoint/label pair, prove the resulting shell balance with the
extra factor `L`, and instantiate the intended parameters to determine the minimum ambiguity
required for fit.  That will decide whether weakening reconstruction merely moves the same
exponential cost into `L`, or leaves a quantitatively viable interface that still supplies the
proved `LayeredCollapseLeafAt` payload.  No P-versus-NP conclusion follows.

### Bounded ambiguity moves the cost; it does not remove it

The list-decoding audit is now complete at the intended first-round parameters.  A
`BoundedAmbiguityFirstRoundCode bad L` permits at most `L` bad roots for each endpoint/label pair.
Its generic shell count is

```text
card(bad) <= L * labelCard * card(endpoint shell).
```

For the full residual-depth-zero parity bad shell, clearing the endpoint-shell denominator gives

```text
(n-K+1)^d <= (L * labelCard) * (2*K)^d.
```

Thus the quantitatively honest first-round alphabet is the effective product
`L * labelCard`.  At `n = 1000*A*r`, `K = 20*r`, and `d = 10*r`, the existing arithmetic audit
applies directly to that product and proves

```text
1000*A*r < 20*(24*(L*labelCard)+26).
```

The theorem `parity_normalized_intended_boundedAmbiguity_productAware_not_fit` propagates this
strict first-round inequality through every positive-round product-aware recurrence with a
positive terminal survivor.  Later alphabets are arbitrary.  Therefore bounded ambiguity has two
possibilities: omit `L` from the recurrence and lose a sound population bound, or charge `L` and
recover the same ambient obstruction.  It cannot provide the missing restriction saving within
this fixed-shell, fixed-expenditure interface.

Focused Lean elaboration passed.  The new capstones use only the standard logical axioms already
present in the module; no `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` was added.
This closes the bounded-ambiguity/list-decoding branch, but it does not prove P versus NP.

The next viable frontier must alter a structural premise of the shell balance: spend fewer than
`10*r` live coordinates, avoid transporting the full parity bad shell through one round, or obtain
a survivor-conditioned counting invariant whose population is genuinely smaller before the
ambiguity charge is applied.  Any such proposal must still compose with `LayeredCollapseLeafAt`
and must be audited against the exact multi-round recurrence.

### Smaller first-round expenditure: the exact threshold

The first structural alternative has now been audited with a variable trunk expenditure `d`.
The obstruction is not peculiar to the original choice `d = 10*r`.  The theorem
`intended_variable_power_lower_forces_firstRoundDemand` shows that whenever `r <= d`, the shell
power balance forces

```text
(24*A)^d <= effectiveCard,
24*A*r <= effectiveCard,
1000*A*r < 20*(24*effectiveCard+26).
```

Specializing the generic bounded-ambiguity parity count gives this conclusion for every

```text
r <= d < 20*r,
effectiveCard = L*labelCard.
```

`parity_normalized_intended_variable_boundedAmbiguity_productAware_not_fit` propagates the result
through arbitrary positive-round schedules.  Therefore reducing the trunk by any constant factor
from `10*r`—including `5*r`, `2*r`, or `r`—does not help.  The only expenditure window not ruled
out by this shell-population argument is `d < r`.

This narrows the structural frontier sharply.  A sub-`r` trunk provides less than the switching
scale used by the existing round construction, so it cannot simply be substituted into the
current proof.  The next meaningful test is whether a genuinely survivor-conditioned bad
population can be proved small enough to compensate for that lost trunk depth; otherwise the
full-parity-shell premise itself must be abandoned.  No P-versus-NP conclusion follows.

### Survivor conditioning requires anti-concentration

The survivor-conditioned alternative has now been tested at its weakest semantic interface, and
assignment coverage alone is insufficient.  For any prescribed `K`-coordinate live set `S`, the
new finite atlas

```text
fixedFreeSetSurvivors(S) = {rho : freeVars(rho) = S}
```

has exact cardinality `2^(n-K)` and covers every total assignment: copy that assignment on the
fixed coordinates and leave exactly `S` live.  Nevertheless, for residual-depth-zero parity,
every member of this atlas is in `commonShallowBad` whenever the trunk is shorter than `K`.

Moreover, whenever `2^d <= choose(n,K)`, this wholly bad atlas is still compatible with the usual
global shell contraction:

```text
card(fixedFreeSetSurvivors(S)) * 2^d
  <= card(the full K-live restriction shell).
```

The capstone `parity_fixedFreeSet_survivor_conditioning_gap` packages all three facts:

1. every assignment is covered;
2. every selected survivor is bad;
3. the global `2^d` shell-count inequality still holds.

Thus a survivor selector can concentrate on a tiny, measure-zero-in-live-set-space portion of the
uniform shell and destroy the probabilistic saving.  The existing generated-path coverage and
fiber bounds cannot rule this out.  A sound survivor-conditioned route must prove an additional
anti-concentration or sampler property tying the selector's live-set distribution to uniform
shell measure; simply counting distinct selected restrictions or covering all assignments is not
enough.

Focused Lean elaboration passed, using only standard logical axioms and adding no `sorry` or custom
axiom.  This is another genuine obstruction, not a P-versus-NP conclusion.  The next precise
frontier is to formulate the minimum live-set sampler condition that transfers a full-shell bad
bound to the selected atlas, then determine whether the canonical switching selector satisfies
it or whether parity provides a counterexample.

### The canonical parity selector is maximally concentrated

The actual selector—not merely an abstract assignment-covering map—has now been audited on the
explicit compact parity family.  Its fresh tagged witness stream is exactly the increasing list of
live ambient coordinates, independent of the extending assignment.  Consequently, on the
fixed-live-set atlas `fixedFreeSetSurvivors(S)`, a depth-`d` prefix always produces the one residual
live set

```text
S \ first_d_in_ambient_order(S).
```

`widthOneParityCompactFamily_fixedFreeSet_endpoint_freeVars` proves this pointwise for every root
in the atlas and every assignment.  The theorem
`widthOneParityCompactFamily_canonicalSelector_concentrates` packages the endpoint live-set image
as a singleton in the strongest pointwise form.

Finally, `parity_canonicalSelector_sampler_gap` combines the whole obstruction:

1. the atlas covers every assignment;
2. every atlas root is parity-bad at residual depth zero;
3. the atlas is compatible with the advertised global shell contraction; and
4. the actual canonical selector maps the entire atlas to one residual live-coordinate set.

Therefore the canonical selector does **not** satisfy any universal anti-concentration/sampler
property over assignment-covering survivor populations.  Its deterministic ambient ordering is
exactly what permits maximal concentration.  A viable route would have to introduce genuine
randomization or a balanced family of coordinate orders and then pay/prove that balancing inside
the recurrence; it cannot be recovered from the current canonical selector.

Focused Lean elaboration passed with standard logical axioms only and no `sorryAx`.  This closes
the canonical-selector sampler repair for the present deterministic construction.  It still does
not prove P versus NP.
