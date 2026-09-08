# Audit of Desktop `p vs np1.pdf`

Examined the 280-page PDF, focusing on the load-bearing profile compression,
universal compiler, extraction and final separation arguments. This is a
targeted mathematical audit, not certification of every lemma in the paper.
Page references below are the printed/PDF page numbers, which agree here.

## Verdict

The document claims an unconditional separation, but the supplied proofs do not
establish it. The later God-Move chain does not repair the key rank argument.

## 1. Permutation invariance does not bound a combined row span

Lemma 27 (p. 42) infers that anonymous profiles suffice for SPDP upper bounds
from rank invariance under interface permutations. Lemma 31 (pp. 43–45)
then places the contributions in symmetric tensor powers because the profile
forgets interface identities.

Counterexample to this inference: all standard basis rows e_i of F^N are
coordinate permutations of one another. Every single row has rank one and
the same anonymous pattern. Together they form the identity matrix, rank N.
More strongly, the elementary tensors in (F^2) tensor-powered R times are all
formed from the same local two-dimensional space and span dimension 2^R;
the symmetric power has dimension R+1. Forgetting position labels does not
embed the original labelled span into that smaller space. It can be a
rank-losing quotient, requiring a separate proof that the needed hard minor
survives and that all original rows are controlled.

The stars-and-bars count and symmetric-power dimension formula are not the
problem; their application to the labelled coefficient rows is unsupported.

## 2. The later Width⇒Rank proof repeats the same logical error

Theorem 216 (pp. 203–204) bounds the number of basis monomials for each row
by C^k and concludes that the entire row space has dimension C^k.
Different rows can have different supports. The identity-matrix example
disproves this inference even when every row has support size one. A single
common low-dimensional space containing ALL rows must be proved; per-row
sparsity does not supply it.

This diagnoses the proof inference, not a claim that the identity matrix is
itself an instance of the specified compiler.

## 3. Configuration-graph unfolding does not supply polynomial width

Theorem 203 (p. 195) and Theorem 209 (p. 200) use a polynomial-length,
polynomial-width branching program for every polynomial-time TM, citing
configuration-graph unfolding. A machine using s work-tape bits can have
2^s different tape contents across inputs. A polynomial time bound does not
turn that configuration count into a polynomial. Any different compression
must be proved while accounting for reusable memory; it is not delivered by
the stated unfolding argument.

## 4. Coupled-sheet instrumentation is not automatically low rank

Lemma 204 (p. 196) appends the multiplicative clause sheet and asserts
preservation of the polynomial rank bound. Lemma 222 (p. 206) proves
additive separation of variable supports, while Theorem 223 asserts
extraction of the coupled product. Separability can help isolate a sheet,
but does not bound that sheet's rank. In particular, efficient construction
or evaluation of a polynomial is not a low-SPDP-rank proof.

There is also an object-definition issue requiring resolution: Theorem 218
(p. 205) calls the compiler output degree O(1), and Lemma 222 constructs it
by summing constant-degree gadgets; the extracted multiplicative sheet has
growing degree in general. Affine substitutions, pinning variables, and
ordinary coefficient projections cannot increase total degree. Either the
object or allowed map is different, in which case its claimed rank bounds
must be justified for that actual object/map.

## Consequence for the Lean project

Theorems 207 (pp. 198–199) and 232 (pp. 212–213) would yield a contradiction
if their upper-bound and extraction premises were valid together with the
lower bound. Their final logical step is not the missing discovery. The
universal upper-bound/representation argument above remains unproved, so the
paper cannot discharge the unrestricted crossing-energy `InvHard` target
identified in the current Lean checkout.

N-Frame terminology neither invalidates nor fixes these issues. A repaired
proof must control labelled rows and reusable computation without assuming
the desired collapse or silently quotienting away the hard information.
