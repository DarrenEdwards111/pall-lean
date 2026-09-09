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
coordinate rows. For `N > 0` (with a chosen `anchor : Fin N`), it proves that
the original rows span dimension `N` and the projected rows span dimension
`1`. More generally, **any** linear map
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

### The local-equation elimination is not generically rank-monotone

`GodMoveAccumulatorEliminationCheck.lean` constructs a concrete algebra
homomorphism eliminating an output wire by substituting the product of two
selector factors. It recovers the product exactly. It also proves that the
selector mixed derivative is zero before elimination and one afterward;
thus this elimination does not commute with those derivatives.

This check identifies an issue a proposed derivative-space transport proof
must handle. Noncommutation alone is not asserted to refute every possible
rank inequality. The important distinction is that existential elimination
of local equations is not automatically one of the coordinate restrictions
covered by the God-Move rank-monotonicity lemmas.

`GodMoveAccumulatorRankCheck.lean` strengthens that check to a counterexample
using the repository's actual `mlBlockedSpdpRank`. With one block for each of
three variables and strict derivative order `kappa=2`, shift degree `ell=0`,

    rank(X_0) = 0,
    rank((1-X_1)*(1-X_2)) > 0.

The second statement is witnessed by the admissible derivative list `[1,2]`,
whose row is the constant one in the actual multilinear SPDP subspace.
Thus the explicit algebra homomorphism eliminating `X_0` by the product
strictly increases this rank. This disproves a generic monotonicity theorem
for that nonlinear substitution, not every possible source-specific bridge.
The statement uses the strict `|S|=kappa` convention, not the inclusive
`|S|<=kappa` variant. It does not silently replace the paper's convention.

### A constructive rank-monotone extraction for a genuine product source

`GodMoveProductSourceExtraction.lean` supplies a valid extraction under
explicit, checkable support conditions. Let `Q` use only kept variables and
let

    R = product_(j in admin) (1-X_j)

use only dropped variables. Setting the dropped variables to zero is a
single, explicit algebra homomorphism `piZero`; the file proves

    piZero(R) = 1,
    piZero(Q*R) = Q,
    rank(Q) <= rank(Q*R).

The inequality uses the repository's strict multilinear blocked SPDP rank,
at arbitrary derivative order and shift degree, with the same partition on
both sides. Its proof invokes the already verified rank monotonicity of
zero substitution. No rank-transport premise is assumed.

This completes that product-source extraction step. **The source already
contains `Q` multiplicatively.** The theorem does not turn the additive
accumulator constraint energy into this source, or prove that `Q*R` has
polynomial rank. If `Q` carries a large minor, the inequality transfers its
lower bound back to the source; it does not supply the missing upper bound.

### Where this connects to the existing Route B extraction

The repository already proves concrete strict coupled-sheet extraction in
`RouteBPaperFaithfulTPhiExtraction.lean`, notably
`routeBPaperFaithfulTPhi_canonicalTargetExtractionTransfer` and the same-target
minor package `routeBPaperFaithfulTPhi_canonicalTargetIdentityMinorData`.
These use the raw product compiler, whose desired common-span budget is
refuted above. They are not an extraction theorem from the newly introduced
additive accumulator energy.

For a different instrumented source, the exact open pairing is
`GlobalGodMoveGauge.Theorem207PaperSourcePSideUpperBound` with
`GlobalGodMoveGauge.Theorem207PaperSourceToTargetRankBridge`, instantiated
on the **same** constructed source and target and justified from the
hypothetical SAT decider. Those interfaces record the requirements; they
are not proofs that a source satisfying them has been constructed.

## Verified scope

The six gap-repair Lean files compiled successfully under Lean 4.28.0. Every printed
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
lake env lean /tmp/pall-separation-o8uSzb/research-audits/nframe-fixed-invariant/GodMoveAccumulatorRankCheck.lean
lake env lean /tmp/pall-separation-o8uSzb/research-audits/nframe-fixed-invariant/GodMoveProductSourceExtraction.lean
```

The product and vector constructions use Mathlib directly. For the
repository-specific checks, the imported `ProfileCompression`, `GodMoveReal`,
`WithinProfileBound`, `MultilinearSPDP`, and `PiStarConcrete` sources agree
between the isolated and cached home checkouts. This was focused verification,
not a rebuild of the entire repo. The earlier `ConcreteRateDilution.lean` and
`GodMoveAdditiveExtractionCheck.lean` were also rechecked before publication.

To reproduce in a checkout with its own dependencies/build cache, first run
`lake build PallLean.ProfileCompression PallLean.GodMoveReal PallLean.PiStarConcrete`,
then replace the absolute paths above with
`research-audits/nframe-fixed-invariant/<file>.lean` relative to that checkout.
The audit files are standalone checks, not imports into the main separation
entrypoint.

The outstanding separation requirement is one explicitly justified source
construction that has the universal polynomial upper bound and a valid
rank-monotone extraction preserving the designated hard minor. These local
repairs do not yet supply that combination. Nothing here proves either
`P = NP` or `P != NP`.
