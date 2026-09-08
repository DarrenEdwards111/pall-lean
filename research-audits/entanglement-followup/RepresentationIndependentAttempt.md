# Attempt: a representation-independent boundary lower bound

2026-09-09. Mathematical audit, not Lean verified. No P != NP proof.

## 1. Replace explicit CNF size by minimum boundary-description size

Let F(x,y) be a CNF of encoded length L and define R_F(x) := EXISTS y F(x,y). Instead of charging an explicit projected CNF, allow any exact finite description of R_F.

There is always an O(L)-length description: the original formula plus its variable partition and existential quantifier convention (the partition can be supplied by O(L) flags in an ordinary explicit encoding). This is an exact description, not an efficient evaluation algorithm. After fixing a prefix of x, store F with that prefix or substitute the fixed values. This remains polynomial-size and admits polynomial-time updates.

Therefore a superpolynomial bound on unrestricted description SIZE alone cannot establish the desired boundary cost. It can only arise after restricting what counts as a representation or charging evaluation.

## 2. Charge evaluation as well

If a uniformly polynomial-time compiler could turn every such F into a polynomial-size representation with a uniform polynomial-time membership evaluator, SAT would be in P: designate no free variables and evaluate R_F at the empty assignment. Conversely, under SAT in P the original formula is already a compact representation with polynomial membership evaluation after substituting x.

Thus this broad uniform compilation/evaluation target is equivalent to SAT in P. Merely defining the energy as the optimal evaluation time does not produce an independent lower-bound proof.

This does not mean every restricted compilation target is equivalent, or that all circuit-size bounds are identical to uniform time bounds. The uniformity qualifications are essential.

## 3. General Boolean circuits defeat a generic projection-size claim

Given a fan-in-two Boolean circuit C(x) with s gates, introduce a variable z_g for every gate and enforce its truth table by width-at-most-three CNF clauses. For example z=a AND b is encoded by (NOT z OR a), (NOT z OR b), (z OR NOT a OR NOT b); NOT gates use two binary clauses. Add a unit clause asserting the output. Existentially quantifying gate variables recovers exactly C(x), using O(s) clauses and polynomial bit encoding size.

So small width-three formulas can project to every small Boolean circuit function, not just parity. Any proposed generic rule that forces their boundary summaries to be superpolynomial for arbitrary representation reasons must allow those original circuits as counterexamples.

A specific family of projected functions with superpolynomial GENERAL circuit size would be a substantive result and could imply stronger nonuniform consequences. None is constructed or proved here.

## 4. Connection to actual observer runs

A run can retain a compact unresolved description without possessing its answer. This explains why the storage-only arguments fail, but does not make the computation easy. The required invariant has to distinguish compact description from costly evaluation while remaining bounded per actual machine step. We have not shown SAT forces such an invariant to exceed all polynomials.

Outcome: broadening the representation removes the exponential CNF storage lower bound. Charging evaluation identifies the original unresolved time problem. This attempt does not close it, and no numerical experiment would validate the missing universal quantifier.
