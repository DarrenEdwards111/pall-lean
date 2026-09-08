# Constructive attempt: decision -> witness -> holographic state

2026-09-08. No separation; not Lean verified.

## Positive bridge

Given a correct SAT decider D and a formula F on n variables, first call D(F). If UNSAT, return UNSAT. Otherwise, for i=1..n, query D on F restricted by the chosen prefix and x_i=0. If satisfiable choose zero; otherwise choose one. The invariant is that the restricted formula remains satisfiable. At the end the n-bit string satisfies F. At most n+1 calls are used. Restrictions are polynomial-time syntactic operations; formula size need not increase beyond a polynomial in original encoding length L. Thus polynomial decision time implies polynomial witness-finding time.

This does not require the original decider itself to produce a witness; it constructs a wrapper around it. It is standard SAT self-reducibility, not a new theorem.

Source: https://www.cs.toronto.edu/~vassos/teaching/c63/handouts/SelfReducibility.pdf

## Where the entanglement argument stops

For each fixed satisfiable F, the resulting witness is one computational-basis string |w(F)>. This is a product state across any partition of its bits, with Schmidt rank one. The wrapper does not prepare the normalized sum of ALL satisfying witnesses. Thus this positive bridge gives witness reconstruction, but does not force high witness-witness entanglement.

For a unique-witness formula even the uniform satisfying state is just a basis string. Therefore any argument requiring high entanglement of that state for every satisfiable instance fails. This is not an efficient solver for uniquely satisfiable SAT and does not exclude worst-case hardness on another family.

Preparing the wrapper coherently on a superposition of formulas can create entanglement between the formula and output registers. That is a different cut and task. Its rank does not automatically lower-bound the cost of evaluating one explicit formula.

## Quantifier correction for the cost target

A sufficient lower-bound target for each correct deterministic decider D is: for every integer k and constant C>0, there is an input x with |x|>=1 such that cost_D(x)>C|x|^k, together with a polynomial runtime upper bound on that same cost. A convenient stronger form permits arbitrarily large such inputs. It does NOT require every formula of a given size to be hard. Our easy-family examples defeat universal pointwise rank-to-cost rules, not a possible hard-family theorem.

A universal superpolynomial witness-finding TIME lower bound would also exclude polynomial SAT decision by the wrapper above. We have not proved that bound. Substituting it as a premise would merely move the gap.

## Verification

self-reduction-check.py checks every Boolean truth table for n=0..4 (including all 65,536 four-variable predicates). It verifies the satisfiable-prefix invariant and n+1 oracle-call limit. Its brute-force oracle is only a correctness test, not an efficient SAT algorithm or runtime proof. The general argument is the induction stated above.
