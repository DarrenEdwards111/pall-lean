# Concrete compiler finding — 2026-09-08

This follow-up changes the status of the OLD unprojected profile target from
merely unproved to refuted for the existing concrete implementation.

## Existing result located and rechecked

`PallLean/CookLevinFrontierRefutation.lean` already proves
`cookLevinExactWithinProfile_false_at_2pow804`. Running that file with Lean
completed successfully and reported only propext, Classical.choice, Quot.sound.

Its source is `Step4Compiler.bounded_params_at_2pow804_absurd`, combining a
conditional upper bound with an unconditional rank lower bound for the same
concrete compiled polynomial. SAT correctness is NOT needed for that lower
bound. The source comments in parts of this large repository call the target
open elsewhere; theorem statements and checked dependencies take precedence.

## New explicit instantiation

`EasyMachineProfileRefutation.lean` defines a three-state DTM whose transition
always goes to the accept state. It proves:

- Every nonempty input reaches the accept state after one step.
- The machine accepts every nonempty input within its declared polynomial
  clock (time-bound exponent one).
- At n = 2^804, its `CookLevinWithinProfileFinrankFrontier` is false.

The file passed Lean v4.28.0 using the existing Lake environment. The frontier
refutation reports only propext, Classical.choice, Quot.sound. There was a
non-fatal simplifier warning about its exponentiation evaluation threshold;
the proof used power monotonicity, not exhaustive enumeration at that size.

## Scope

This concerns `cook_levin_compilation` in `CookLevinDefs.lean`, containing
Booleanity, adjacency and transition-skeleton constraints. It does not assert
that every possible faithful implementation of the paper is refuted. Nor is
it a counterexample to P != NP or to the crossing-energy conjecture.

It DOES rule out completing the old universal P-side profile theorem for this
unchanged object. A replacement must change the representation/invariant or
establish an appropriate semantic extraction with a new valid upper bound.
Projecting down rank is insufficient unless the hard-sheet lower bound and
rank-monotone extraction survive on the SAME resulting representation.

No missing universal separation theorem was proved; this investigation found
a concrete reason not to spend further search trying to prove the old target.
