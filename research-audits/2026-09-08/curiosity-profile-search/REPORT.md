# Curiosity profile-repair search — 2026-09-08

## Execution

Used the local Mikoshi Curiosity `LLMConjectureGenerator`, `ResearchEvaluator`
and SQLite `ResearchArchive` with the installed Ollama `qwen2:7b` model.
Two generation calls returned five candidates. This was a bounded, supervised
search, not an exhaustive exploration or an unattended background job. Mikoshi
OS was inspected but not launched. No repository changes were pushed.

The second prompt supplied two concrete directions from the supervising
assistant; they should not be described as independent model discoveries.

## Findings

1. First batch (three proposals): wrong-direction rank repair and undefined
   functions. Rejected after mathematical inspection.
2. Second batch A: permutation-invariant rows. A common fixed-point subspace
   could bound the joint span, but the returned statement was ambiguous and
   supplied no proof that compiler rows have the needed symmetry.
3. Second batch B: common-image factorization. Correct after stating an
   explicit common map and factorization of every row. Mere linear dependence,
   as in its assumptions, does not suffice. No compiler applicability proof.

The built-in critics labelled all five `survivor` with no attached proofs.
Those are heuristic screening results, not mathematical certification. Final
assistant reviews are stored in `archive.db`; the original outputs and
automated evaluations remain in the JSON files for auditability.

## Exact finite counterexample checks

`explicit-matrix-tests.json` records constructed labelled basis rows for
R=2 through 8. Rows of fixed Hamming weight have one anonymous histogram but
contain an identity minor of size binomial(R,floor(R/2)). At R=8 this is 70.
These identity-minor entries were checked explicitly using integer equality.

`orbit-tests.json` extends the dimension formulas to R=16. These larger values
are formula evaluations, not explicit matrix enumeration. At R=14, weight 7,
the labelled span has dimension 3432, while the span of its orbit-symmetrized
rows has dimension one. The example is about the proposed inference, not an
assertion that these matrices arise from the paper's exact compiler.

## Lean-checked conditional result

`CommonImageBound.lean` proves: if every row factors through ONE linear map
`decode : U →ₗ[K] V`, then the dimension of the joint row span is at most
`finrank K U`. The theorem has explicit finite-dimensional hypotheses.

Checked with Lean v4.28.0 in the pall-lean-holographic Lake environment:

```
lake env lean research-audits/2026-09-08/curiosity-profile-search/CommonImageBound.lean
```

Exit code 0; reported axioms only `propext`, `Classical.choice`, `Quot.sound`.
This is standard linear algebra formalized for the audit, not a novel SAT
lower bound. It is not marked as a proof of the raw generated candidate.

## What remains

Construct the required shared polynomial-dimensional representation for the
actual compiler's labelled SPDP rows, with the needed extraction properties,
or find a different algorithm-sensitive invariant and prove its SAT lower
bound. No universal bound, `InvHard`, or P ≠ NP proof was obtained in this run.
