# A constructed semantic handshake, not an efficient separation certificate

The three files below construct a genuine correspondence from faithful SAT
correctness. No polynomial identity, row equality, rank bridge, or common-span
containment is supplied as a hypothesis. The construction does **not** close
the requested P-versus-NP separation: its explicit presentation and proved
common-span bound are exponential, and the required hard minor for its new
target has not been established.

The follow-up [characteristic-target calibration](GodMoveCharacteristicCalibration.md)
constructs a linear-operation product program and a binomial identity minor
for the same **easy unit-CNF** target. It also proves that every unsatisfiable
signed CNF gives the zero characteristic target. Neither result supplies the
missing general-SAT extraction/common-span/hard-family combination.
The [subsequent checks](GodMoveCharacteristicNextStep.md) establish free-slack
cancellation and the counting information carried by exact midpoint evaluation.

## What is constructed

1. `GodMovePinnedSATQueries.lean` uses the actual `ComposableMachine`,
   `SeparationTarget.SATLang`, and the round-trip-correct `encodeFormula'`.
   For a signed CNF `phi` whose variables are below `n`, add unit clauses
   fixing all of them to an assignment `a`. It proves

       SAT(phi + units(a)) iff eval(phi,a) = true.

   Therefore a machine genuinely deciding `SATLang` has actual clocked output
   `eval(phi,a)` on that encoded query. This holds for every assignment, not
   only for a chosen satisfying witness. The clock need not be polynomial;
   this semantic theorem applies to any correct clocked decider.

2. `GodMoveBooleanInterpolation.lean` reuses the repository's canonical
   interpolation `Step4Compiler.chi_phi`:

       chi(f) = sum_a bit(f(a)) * product_i (if a_i then X_i else 1-X_i).

   It verifies evaluation on the Boolean cube, multilinearity, and the exact
   count `2^n` of summation indices. It also constructs one ambient span of
   squarefree monomials containing every strict and inclusive SPDP row space
   in these variables, with dimension at most `2^n`.

3. `GodMoveFaithfulHandshake.lean` defines the source from the actual machine
   query outputs, and the target from the signed CNF verifier:

       source = chi(a -> actual_machine_output(encode(phi + units(a)))),
       target = chi(a -> eval(phi,a)).

   Correctness proves `source = target`, hence equality of **every**
   derivative/shift row and both actual strict and inclusive SPDP ranks, using
   the same partition and parameters. The source is not defined to be the
   target, and their equality is not an assumption.

The final file also constructs the ordinary signed clause-product polynomial:
positive literals give `X_i`, negative literals `1-X_i`, a clause gives
`1-product(1-literal)`, and the CNF gives the product of its clause polynomials.
It proves that this product and the characteristic target have identical
values on the Boolean cube.

A checked regression example makes this distinction concrete: for the
contradictory unit clauses `x` and `not x`, the characteristic polynomial is
zero, while the raw clause product is the nonzero polynomial `X*(1-X)`.

## What this does not prove

- Boolean-cube agreement is **not** asserted to identify the raw clause
  product with the characteristic polynomial away from the cube. Repeated
  variables can produce powers in the raw product. Boolean normalization is
  not the repository's projection that drops nonsquarefree monomials.
- No rank-nonincreasing map from the original additive accumulator energy
  into this characteristic source/target has been constructed.
- The source represents a family of different assignment-pinned runs, not
  an extraction from one original fixed-input computation.
- The `2^n` truth-table presentation does not establish a polynomial compiler
  or polynomial SPDP rank. Nor is this index count a lower bound on every
  individual function's smallest possible representation.
- The shared space has a verified **exponential** bound, not the desired
  polynomial common-span bound. Its containment theorem is general algebra
  and does not use SAT correctness.
- The designated hard-family minor lower bound has not been proved for this new
  characteristic target. It is not silently substituted for the paper's raw
  coupled-sheet target.

Consequently this completes a semantic, row-exact handshake for the stated
truth-table construction, **not** the efficient, minor-preserving handshake
needed for the separation. That remaining step is still open.

## Lean checks

The three original handshake files compiled under Lean 4.28.0 without warnings.
Printed axiom checks contain only subsets of `propext`, `Classical.choice`, and `Quot.sound`.
The focused checks used the cached build in `/home/darre/pall-lean`; relevant
imported source files agree with the isolated worktree. This was not a fresh
build of the entire repository.

To reproduce from a checkout with its own dependencies, run from its root:

```sh
lake build PallLean.Step4Compiler PallLean.MlProjFar PallLean.ProductDeriv PallLean.BinomialBound2 PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATVerifierSpec
handshake_audit_dir="$PWD/research-audits/nframe-fixed-invariant"
lake env lean --root="$handshake_audit_dir" -o "$handshake_audit_dir/GodMoveBooleanInterpolation.olean" "$handshake_audit_dir/GodMoveBooleanInterpolation.lean"
lake env lean --root="$handshake_audit_dir" -o "$handshake_audit_dir/GodMovePinnedSATQueries.olean" "$handshake_audit_dir/GodMovePinnedSATQueries.lean"
lake env lean --root="$handshake_audit_dir" -o "$handshake_audit_dir/GodMoveMonomialMinor.olean" "$handshake_audit_dir/GodMoveMonomialMinor.lean"
lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean --root="$1" -o "$1/GodMoveFaithfulHandshake.olean" "$1/GodMoveFaithfulHandshake.lean"' _ "$handshake_audit_dir"
lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean --root="$1" "$1/GodMoveCharacteristicUnsat.lean"' _ "$handshake_audit_dir"
lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean --root="$1" "$1/GodMoveUnitCharacteristic.lean"' _ "$handshake_audit_dir"
```

The auxiliary `.olean` files are ignored build artifacts. None of these
standalone research checks changes the production compiler or invariant.
