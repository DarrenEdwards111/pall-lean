# Constructive repairs and the exact remaining God-Move obstruction

This work addresses the two requested gaps in the desktop paper directly.
The full separation gaps are **not closed**. There are now explicit checked
constructions, and a checked negation of the original common-span target for
the repository's current raw product compiler. No production invariant,
compiler definition, or theorem hypothesis was changed.

## 1. Common span: retain positions, or account for lost rank

`GodMoveCommonSpanRepair.lean` supplies an actual shared spanning space.
Given finitely many placements, each with `d` generators, it takes the span
of all of those generators in the same ambient coefficient space and proves

    dimension(shared span) <= placementCount * d.

Each per-placement span is contained in this one common space. Thus the
common-span inference is repaired with its necessary placement-count factor.
This does not establish a polynomial bound on the placements needed for all
SPDP rows of the proposed compiler.

The file also constructs a single idempotent linear projection that identifies
coordinate rows. It proves exactly that the original rows span dimension `N`
and the projected rows span dimension `1`. More generally, **any** linear map
identifying two distinct coordinate rows kills their nonzero difference and
fails to be injective on their original span. Identifying all coordinate rows
forces factorization through coordinate summation.

Consequently, forgetting the positions of an independent minor's rows cannot
also preserve their independence. These results constrain that particular
repair mechanism; they do not rule out a construction retaining enough
additional structure.

### The actual existing compiler target is false

`GodMoveExistingCompilerVerdict.lean` checks the repository's named target,
not merely the coordinate-row example. It proves

    not (WithinProfileBound.CookLevinProfileTemplateCollapseLemma
           M n hn2 htb hns)

for `n >= 2^804`, `M.timeBound <= 4`, and `M.numStates <= n`.
No SAT-correctness assumption is used. The proof combines the existing
template-collapse-to-`n^200` upper-bound theorem with the existing strict
lower bound `n^200 < rank(compiledPoly)` for that same raw product compiler.

Therefore filling in that exact premise for the unchanged compiler would
contradict a verified theorem. A valid continuation must change the source
construction or the intended common-span statement and then justify the
required semantic and rank relationships.

This is distinct from observing that upper and lower bounds contradict each
other under a hypothetical polynomial-time SAT decider. Such a conditional
contradiction is the intended structure of a separation proof, not a reason
that every possible God-Move construction is impossible.

## 2. Product encoding: construct it with local accumulator constraints

`GodMoveProductAccumulator.lean` gives a constructive local realization for
arbitrary evaluated factors, including the paper's factors
`f_i = 1 - z_i * V_i^2`:

    w_0 = 1,
    w_(i+1) = w_i * f_i.

It defines the canonical accumulator as prefix products and proves uniqueness
and `w_m = product_i f_i`. It uses `m+1` accumulator values and `m+1` equations.
The local sum-of-squares constraint expression

    E = (w_0-1)^2 + sum_i (w_(i+1)-w_i*f_i)^2

vanishes exactly when those equations hold. In particular,

    (exists w, E(f,w)=0 and w_m=y) iff y=product_i f_i.

This closes the elementary construction of a local constraint system realizing
the product. It does not identify the additive constraint expression `E` with
the product polynomial, and it is not a completed SAT compiler with verified
CEW, bit complexity, or SPDP rank bounds.

### Elimination still needs a rank-transport theorem

`GodMoveAccumulatorEliminationCheck.lean` constructs a concrete algebra
homomorphism eliminating an output wire by substituting the product of two
selector factors. It recovers the product exactly. It also proves that the
selector mixed derivative is zero before elimination and one afterward;
thus this elimination does not commute with those derivatives.

This check identifies an issue a proposed derivative-space transport proof
must handle. Noncommutation alone is not asserted to refute every possible
rank inequality. The important distinction is that existential elimination
of local equations is not automatically the constant/affine restriction
covered by the God-Move rank-monotonicity lemmas.

## Verified scope

All four new files compiled successfully under Lean 4.28.0. Every printed
axiom check contains only `[propext, Classical.choice, Quot.sound]`, with no
`sorryAx` or custom axioms. Their statements retain the conditions described
above; no hard premise was silently discharged or renamed into a solution.

Checks were run from `/home/darre/pall-lean` against the absolute paths in
the isolated checkout:

```sh
lake env lean /tmp/pall-separation-o8uSzb/research-audits/nframe-fixed-invariant/GodMoveCommonSpanRepair.lean
lake env lean /tmp/pall-separation-o8uSzb/research-audits/nframe-fixed-invariant/GodMoveProductAccumulator.lean
lake env lean /tmp/pall-separation-o8uSzb/research-audits/nframe-fixed-invariant/GodMoveAccumulatorEliminationCheck.lean
lake env lean /tmp/pall-separation-o8uSzb/research-audits/nframe-fixed-invariant/GodMoveExistingCompilerVerdict.lean
```

The product and vector constructions use Mathlib directly. For the existing
compiler verdict, the imported `ProfileCompression`, `GodMoveReal`, and
`WithinProfileBound` sources agree between the isolated and cached home
checkouts. This was focused verification, not a rebuild of the entire repo.

The outstanding separation requirement is one explicitly justified source
construction that has the universal polynomial upper bound and a valid
rank-monotone extraction preserving the designated hard minor. These local
repairs do not yet supply that combination. Nothing here proves either
`P = NP` or `P != NP`.
