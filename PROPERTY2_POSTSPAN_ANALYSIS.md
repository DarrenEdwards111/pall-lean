# Property 2 Post-Span Analysis — Wτ Obstruction

Date: 2026-05-22
Branch context: `godmove-paper-faithful`, after commit `b7ba5d65`.

## Purpose

This note records the math-level analysis requested before further formalization.
It does **not** claim a new Lean closure theorem.  The goal is to decide whether
`BoundedWithinProfileFinrankClaim` for the allocated Cook--Levin / `Pi+ᵦ`
factors can be discharged in the unquotiented ambient polynomial ring, or
whether the missing object is genuinely a quotient/compiled-coordinate
`W_τ` infrastructure.

## Relevant Lean definitions

In `PallLean/WithinProfileBound.lean`:

```lean
def boundedProfileClassifiedSet
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (h : ProfileHistogram) : Set (MvPolynomial (Fin n) ℚ) :=
  { g | ∃ d : Fin L → List (Fin n),
      (∀ i, ∀ v ∈ d i, v ∈ S) ∧
      g = Finset.univ.prod (fun i => iterDerivList (d i) (factors i)) ∧
      derivCountProfile constraintType d = h ∧
      ∑ i, (d i).length ≤ S.length }
```

and

```lean
noncomputable def allBoundedProfilePostSpan
    (_B : BlockPartition n) (κ _ℓ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (h : ProfileHistogram) : Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  Submodule.span ℚ
    (⋃ (S : List (Fin n)) (_ : S.length ≤ κ)
       (shift : MvPolynomial (Fin n) ℚ) (_ : shift.vars ⊆ S.toFinset),
      (fun g => mlProj (shift * g)) ''
        boundedProfileClassifiedSet factors constraintType S h)
```

The target is:

```lean
def BoundedWithinProfileFinrankClaim ... : Prop :=
  ∀ h,
    Module.Finite ℚ ↥(allBoundedProfilePostSpan ... h) ∧
    Module.finrank ℚ ↥(allBoundedProfilePostSpan ... h) ≤ withinProfileBound κ
```

where:

```lean
withinProfileBound κ = (κ + 1)^8
```

The repo already proves the `Module.Finite` side by containment in the full
multilinear monomial span.  The remaining mathematical content is explicitly
recorded in `WithinProfileBound.lean` as requiring a factorization through

```text
⊗_τ Sym^{h(τ)}(W_τ),    dim W_τ ≤ 3.
```

## What `allBoundedProfilePostSpan` actually spans

For fixed profile `h`, it spans all rows of the form

```text
mlProj(shift * Π_i ∂_{d_i}(factor_i))
```

where:

- all derivative indices in each `d_i` lie in a common list `S`,
- `|S| ≤ κ`,
- `shift.vars ⊆ S.toFinset`,
- the per-factor derivative counts have histogram `h`,
- total derivative mass is ≤ `|S|`.

Important: the span is in the **actual ambient polynomial ring**
`MvPolynomial (Fin n) ℚ`.  It is not a quotient, not a canonical chart, and not
an abstract profile-coordinate space.

Thus any dimension bound must control not only local algebraic shapes but also
which ambient variables/positions occur.

## Single factor type: Booleanity

For a fixed Booleanity position/block `v`, the existing infrastructure gives a
small local residue span.  In Path C this appears as the Booleanity projected
residue machinery, e.g.

```lean
SATBlockBooleanityActualProjectedResidueSpan ... v
```

with a rank bound ≤ 3 and generators morally of the form:

```text
span { 1, X_false(v), X_true(v) }
```

Derivative cases:

- zero-hit: Booleanity factor contributes a local quadratic / normalized residue;
- one-hit: derivative contributes a local linear/constant residue;
- mixed/over-hit: either lands in the same local residue span or vanishes;
- all of this is position-local and already mostly formalized by the Booleanity
  residue payloads.

For a **fixed** position `v`, the local post-span after allowing shifts supported
inside a fixed small `S` remains controlled by the multilinear monomials in the
variables of that local chart.  This is a constant/small-dimensional statement.

However `allBoundedProfilePostSpan` does not fix `v`.  It unions over all
`S : List (Fin n)` and all matching derivatives.  Therefore it contains rows
for Booleanity at many different ambient positions.

Concrete lower-bound intuition:

- for distinct Booleanity positions `v₁, ..., v_r`, the corresponding variables
  `X_false(v_j)` or `X_true(v_j)` are distinct ambient coordinates;
- even with profile mass `h(booleanity)=1`, the span contains many distinct
  one-position local rows;
- these rows are linearly independent in the ambient polynomial ring unless a
  quotient/projection identifies them.

So the dimension grows with the number of available positions/blocks, not only
with `κ`.  This contradicts the desired bound `(κ+1)^8` when the ambient number
of positions is large.

Conclusion for Booleanity: the local `dim ≤ 3` theorem is true only after
fixing a position/chart, or after quotienting positions into a σ-only/canonical
space.  It does not by itself imply the global unquotiented
`allBoundedProfilePostSpan` finrank bound.

## Signed adjacency factors

Path C rewrites adjacency factors into signed-cross atoms, e.g.

```lean
adjacencyFactor_eq_satSignedCrossAtom
satSignedCrossAtom ... c a b
```

Locally a signed-cross atom has constant arity: it uses two endpoint positions
and Boolean tags.  The row certificate machinery proves good behavior under
Boolean normalization, coordinate conjugation, and `mlProj` for the fixed atom.

For a fixed ordered pair `(a,b)`, the local span is again constant-dimensional:
roughly generated by the constant term and the two endpoint coordinates / signed
cross contribution.

But globally `allBoundedProfilePostSpan` ranges over all adjacent pairs.  In the
ambient polynomial ring, the rows attached to different pairs `(a,b)` live on
different variable supports.  A profile with one adjacency hit can therefore
contain one local row for each possible adjacency edge.  The number of such rows
grows with the number of positions/edges in the Cook--Levin tableau.

Conclusion for adjacency: per-position/per-edge post-spans are small, but the
unquotiented global post-span has dimension depending on the number of ambient
adjacency positions unless a quotient identifies all adjacency atoms of the same
interface type.

## Signed transition factors

Transition/skeleton factors are also reduced to signed-cross atoms, with
coefficient `transCoeff M q` or related transition data.  Locally they behave
like the adjacency case: fixed small arity, constant-dimensional row certificates,
and stable signed-cross normal forms.

The global issue is the same but slightly worse: there may be many transition
locations and state/symbol cases.  Unless the transition coefficient/tag data is
part of a finite canonical alphabet and position multiplicity is quotient-collapsed,
the unquotiented ambient span sees distinct variable supports for distinct
transition positions.

Conclusion for transition: the signed-cross local theorem supports a local chart
or quotient-space proof, not an ambient global `(κ+1)^8` finrank proof.

## Why per-factor/per-position post-spans are insufficient

A tempting route is to define one post-span per factor position and then sum them.
This proves polynomiality only if the number of positions is polynomial in the
outer scale with a tolerable exponent.  But it does not prove the existing
`withinProfileBound κ = (κ+1)^8`, which is independent of the ambient number of
factors/positions.

More importantly, the profile-compression argument counts **types and profiles**,
not physical positions.  Its intended dimension is controlled by:

```text
∏_τ dim Sym^{h(τ)}(W_τ)
```

with `dim W_τ ≤ 3`.  This is impossible in the unquotiented ambient ring unless
all position copies of the same type already lie in a common low-dimensional
subspace.  They do not: distinct variables are independent.

## Relation to current allocated-product work

The existing allocated-product work has two useful but different routes:

1. **Direct finite-window/private-chart route**
   - Counts ordered derivative windows and fixed-window shifts.
   - Gives an unconditional polynomial bound at fixed paper scale, e.g.
     `n^1000` at `n = 2^804`.
   - If scaled naively to `n = 2^k`, the exponent grows like `k`, so it cannot
     satisfy the final contradiction condition `k > 4C`.

2. **Lemma-29/profile-compressed route**
   - Gives a small exponent such as `C ≈ 20`.
   - But it is conditional on precisely the missing quotient/profile hrow or
     post-span compression seam.

Therefore the direct route is honest but too weak for the current separation
arithmetic, and the compressed route is arithmetically strong but still missing
the Wτ quotient infrastructure.

## Does `BoundedWithinProfileFinrankClaim` require shared σ-only Wτ?

Yes, for the current statement.

More precisely:

- In unquotiented ambient coordinates, per-position row spaces are small but
  their union over positions has dimension depending on ambient position count.
- The bound `(κ+1)^8` is independent of ambient position count.
- Therefore one needs either:
  1. a genuine shared σ-only `W_τ` inside the actual ambient ring, or
  2. a quotient/projection/compiled-coordinate replacement where all position
     copies of the same type are transported into a canonical `W_τ`.

The first option appears false for the actual ambient ring.  The second option
is the mathematically coherent route.

## Formalization cost of quotient/compiled-coordinate Wτ route

Estimated cost: **1000--2000+ Lean lines**, multi-file.

Likely components:

1. Define canonical/interface coordinate spaces for each constraint type.
2. Define a quotient/projection or transport map from actual rows to canonical
   type coordinates.
3. Prove Booleanity local rows map into the canonical Booleanity `W_booleanity`.
4. Prove signed adjacency rows map into canonical adjacency `W_adjacency`.
5. Prove signed transition rows map into canonical transition `W_transitionLeft`.
6. Prove product/profile aggregation commutes with the transport enough to land
   in `⊗_τ Sym^{h(τ)}(W_τ)` or the repo's `profileSubspace` analogue.
7. Prove the post-shift/`mlProj` closure in the quotient/projected space.
8. Replace or bridge the current Property-2 statement to the projected/quotient
   rank bound.
9. Re-run arithmetic with the generalized exponent infrastructure from
   `IsAmplituhedronGaugeWithExponent`.

This should be treated as a real sub-project, not a final one-lemma patch.

## Alternative paper-faithful bounds

The current repo already has CEW/Theorem207-style surfaces, but the same issue
reappears: any paper-faithful small exponent must collapse position multiplicity
somewhere.  CEW/profile-compression language can change the packaging, but if
it proves a bound independent of ambient positions, it must be using a quotient,
canonicalization, or projection equivalent to Wτ compression.

So alternative bounds may help organize the proof, but they do not avoid the
Wτ-shaped bottleneck.

## Session achievements to keep

- Implemented and pushed exponent-parameterized gauge surface:
  `IsAmplituhedronGaugeWithExponent C`, with old `IsAmplituhedronGauge` retained
  as the `C = 200` compatibility specialization.
- Built and pushed private-chart / admissible-window finite routes.
- Wired profile-compression arithmetic conditionally, showing that if the Wτ
  compression seam is closed, the exponent is easily small enough.
- Identified the direct-window route as honest but asymptotically too weak for
  `k > 4C` because its exponent scales with `k`.
- Isolated the real remaining mathematical object: quotient/compiled-coordinate
  `W_τ` compression for post-spans.

## Recommendation

Do **not** continue iterating reformulations of the same ambient post-span claim.
The feasible next major route is:

```text
Build quotient/compiled-coordinate Wτ infrastructure, then prove the projected
post-span/profile-compression bound there.
```

Until that infrastructure exists, any unconditional claim of the current
`BoundedWithinProfileFinrankClaim` for actual ambient allocated factors would be
mathematically suspect.
