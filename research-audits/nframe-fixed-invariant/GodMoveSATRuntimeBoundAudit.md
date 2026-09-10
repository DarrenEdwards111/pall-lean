# SAT runtime-rank bound: the remaining obligation

The requested polynomial bound on SAT source rank in terms of input length and runtime is **not proved**. This work proves a general finite rank upper bound, matches it with the existing SAT source lower bound at the exact paper window, and establishes the logical strength of the remaining conditional estimate. It does not prove `SAT_not_in_P`, a polynomial runtime-rank estimate, or efficient construction of the normalized polynomial.

## A proved upper bound

[`GodMoveShiftedRankUpper.lean`](GodMoveShiftedRankUpper.lean) proves, for every polynomial `p` in `L` variables and every block partition `B`,

$$
\operatorname{rank}_{B,k,\ell}(p)
\leq \binom{L}{k}
       \sum_{j=0}^{\min(k,\ell)}\binom{k}{j}
\leq \binom{L}{k}2^k
\leq (2L)^k.
$$

These are bounds on the repository's **strict** multilinearly projected blocked SPDP rank. Its legal shifts use only variables in the differentiated set. That restriction matters: the displayed count is not a claim about definitions allowing shifts on arbitrary ambient variables.

The proof expands each legal shift into monomials. A nonsquarefree shift contributes zero after multilinear projection. A remaining row is indexed by a differentiated `k`-subset and a shift subset of size at most `min(k, ell)` inside it. These rows span the actual strict SPDP space; counting them bounds its finite dimension. Block admissibility can only remove rows. No multilinearity assumption on `p`, SAT correctness, machine clock, or additional rank hypothesis is needed.

This upper bound depends on variable count and derivative order. For fixed `k` it is polynomial in `L`. When `k` grows logarithmically, its exponent grows as well; it supplies no fixed-degree polynomial bound in runtime.

## The same source at the same paper window

[`GodMoveSATPaperWindowLower.lean`](GodMoveSATPaperWindowLower.lean) puts the actual SAT source minor at precisely the paper parameter, rather than substituting the logarithm of a smaller face dimension. Write

$$
m=\lfloor n/3\rfloor,\qquad
L_n=\texttt{unitInputLength}(m),\qquad
k=\ell=\lfloor\log_2 n\rfloor.
$$

`L_n` is the actual encoded bit length of the unit-formula query family. The polynomial is `machineSource M T (unitFormula m) m`, the normalized output of the unrolled machine on all `L_n`-bit inputs. The partition is `discreteBlocks L_n`. Denote this strict rank by `R(M,T,n)`.

[`GodMoveSATRuntimeFrontier.lean`](GodMoveSATRuntimeFrontier.lean) proves `paperSourceRank_growth_bounds`: for every faithful SAT decider `M` with clock `T` and every `n ≥ 2^20`,

$$
n^{\lfloor\lfloor\log_2 n\rfloor/4\rfloor}
\leq R(M,T,n)
\leq n^{3\lfloor\log_2 n\rfloor}.
$$

Both inequalities concern exactly the same polynomial, encoded length, partition, and derivative/shift window. The upper bound follows from the row count and the proved codec estimate `2 L_n ≤ n^3`; it holds for every machine and clock, without correctness. The lower bound uses SAT correctness and the previously established unit-face extraction. The lower-bound module also rules out every eventual bound `C (L_n + 1)^d`, including at this log/log window.

Thus the rank has superpolynomial, quasipolynomial growth in `n`. A polynomial-size unrolled circuit does not contradict this statement: circuit size is not the dimension of this normalized derivative space. The easy unit face already supplies the minor, so its large rank alone does not establish unavoidable SAT computational difficulty.

## The unresolved estimate and its quantifiers

`SATPolynomialClockRankBound` is a proposition definition, not a proved estimate. It asks that for every machine `M` and clock `T`, **if** `T` is polynomially bounded and `M` decides SAT within `T`, there exist natural constants `C`, `d`, and `n0` such that

$$
\forall n\geq n_0,\quad
R(M,T,n)\leq C\bigl(L_n+T(L_n)+1\bigr)^d.
$$

The constants and cutoff may depend on `M` and `T`, but not on `n`. `encoded_bound_of_runtime_bound` proves that a polynomial clock would convert this supplied estimate into an eventual polynomial bound in `L_n + 1`. The established lower bound excludes that combination of premises.

The theorem `satPolynomialClockRankBound_iff_separation` therefore proves

$$
\texttt{SATPolynomialClockRankBound}
\iff \texttt{SeparationTarget.SAT\_not\_in\_P}.
$$

The forward direction is the valid conditional contradiction. The reverse direction is explicitly vacuous: assuming there is no polynomial-clock SAT decider leaves no machine satisfying the estimate's premises. It produces no numerical estimate for an actual decider and says nothing about clocks that are not polynomially bounded. The equivalence identifies the full strength of this remaining obligation; it does not discharge either side or establish an independent machine-model equivalence.

## Validation

The full focused run on 2026-09-10 passed with Lean 4.28.0: **83 modules, 649 printed axiom checks, zero warnings**, and a matched 501-file source closure. Every printed dependency is among `propext`, `Classical.choice`, and `Quot.sound`. The new modules contain no `sorry`, custom axiom, or `native_decide`.

From the worktree root:

```sh
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py \
  --dependency-checkout /home/darre/pall-lean \
  --log-dir /home/darre/godmove-audit-20260910/sat-runtime-bound-checks
```

The checker matches the imported production sources and Lean/Lake configuration before using the dependency cache, then recompiles the focused audit suite in dependency order. The result record is `/home/darre/godmove-audit-20260910/sat-runtime-bound-checks/results.json`. This is not a build of every historical module in the repository.

The three Lean modules above were independently reviewed for their rank definition, parameters, encoded-length accounting, and quantifier scope. The polynomial SAT runtime-rank estimate and separation remain unproved.
