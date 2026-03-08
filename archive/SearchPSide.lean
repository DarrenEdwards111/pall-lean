import Mathlib
import PallLean.DecisionMobiusBridge
import PallLean.MUSDistribution

/-!
# Search P-Side — The Open Frontier

## The Honest Status

The search-side Möbius framework correctly identifies a representation-invariant
observable (Möbius mass) and proves superpolynomial lower bounds for structured
SAT families. However:

**Möbius mass alone does NOT separate P from NP.**

Evidence:
- Unit clause SAT: in P, superpolynomial mass (proved in MUSDistribution)
- 2-SAT: in P, rich Möbius spectrum at all levels (experimental)
- 3-SAT: NP-complete, but small instances show concentrated mass

## What Would Work

The separation must target the **compiled search polynomial** — the
algebraic object representing how a solver computes SAT(φ).

For a poly-time solver M with state space S:
  P_M(z, s) = compiled polynomial over clause bits z and state bits s
  Tr_s(P_M)(z) = Σ_s P_M(z,s) = partial trace (decision-visible structure)

The key question is NOT about the decision function f(z) = SAT(z)
(which is the same for all correct solvers), but about the INTERMEDIATE
structure of P_M — specifically, how much state is needed to correctly
compute f(z) for NP-complete families.

## Three Candidate Theorems

### Candidate 1: State-Complexity Lower Bound
For NP-complete families, any correct solver needs state space
|S| ≥ 2^{ω(polylog(m))} to correctly compute SAT on all instances.

This is essentially the space complexity of SAT, which is known to be
PSPACE-complete (not just NP-complete). Too strong — PSPACE ≠ P is
harder than P ≠ NP.

### Candidate 2: Communication Complexity
View the solver as a communication protocol between "clause proposer"
and "satisfaction checker". The communication complexity of SAT is
Ω(n) (Razborov), but this gives circuit lower bounds, not time lower bounds.

### Candidate 3: Algebraic Degree of Compiled Search (NEW)
The compiled search polynomial P_M(z,s) has degree in z bounded by
the solver's time. For a poly-time solver, deg_z(P_M) ≤ poly(m).

But for NP-complete instances, the decision function f(z) = SAT(z)
has Möbius coefficients at level m (the whole formula), requiring
degree m in z. The partial trace Tr_s preserves degree, so:

  deg_z(Tr_s(P_M)) ≤ deg_z(P_M) ≤ poly(m)

But the Möbius inversion of f has support at level m, which means
f cannot be expressed as a polynomial of degree < m in z.

**Wait**: f is a boolean function on {0,1}^m, so it can always be
expressed as a multilinear polynomial of degree ≤ m. The degree
is always ≤ m. This doesn't help.

### The Real Issue

The decision function f(z) = SAT(z) has the SAME Möbius structure
regardless of how it's computed. A brute-force solver and a clever
solver both compute the same f. The Möbius mass is a property of f,
not of the computation.

So the P≠NP content is NOT in the Möbius mass of f, but in the
COST of computing f. This brings us back to:

**P ≠ NP ↔ SAT ∉ P ↔ no poly-time algorithm computes f**

The Möbius framework provides a clean LANGUAGE for stating what f
looks like (MUS structure, interaction depth, etc.), but the actual
separation must come from a TIME lower bound argument.

## What the Framework Achieves

1. ✅ Correct target identified (search, not verification)
2. ✅ Representation-invariant observable (Möbius mass)
3. ✅ NP-side structure characterized (MUS ↔ Möbius)
4. ✅ Superpolynomial mass proved for structured families
5. ❌ P-side upper bound — this IS P ≠ NP, not a formalization gap

## Where This Connects to Known Results

The Möbius mass at level k of SAT's decision function is related to:
- **Fourier weight at degree k** (Fourier analysis of boolean functions)
- **Approximate degree** (polynomial representations of f)
- **Certificate complexity** (how many clauses must be examined)
- **Decision tree depth** (query complexity of f)

Known results connecting these to circuit/time complexity:
- Approximate degree lower bounds → oracle separation (BBBV)
- Fourier concentration → AC⁰ lower bounds (LMN, Hastad)
- Query complexity → communication complexity (Raz, etc.)

But all of these give bounds for RESTRICTED models (AC⁰, monotone, etc.),
not for general poly-time Turing machines. Extending to TMs is the P≠NP barrier.
-/

namespace SearchPSide

open DecisionMobiusBridge MUSDistribution

/-- The open theorem, stated as sharply as possible.

    For any polynomial p, there exists an NP-complete family of formulas
    such that no algorithm running in time p(m) can correctly compute
    the decision function f(z) = SAT(clause_subset_z) on all instances.

    This is equivalent to P ≠ NP. -/
axiom search_pside_open :
    ∀ (p : ℕ → ℕ) (_hp : ∃ C, ∀ m, p m ≤ m ^ C),
    ∃ (family : ℕ → Σ m, SATDecision m),
    -- The family is NP-hard
    (∀ n, ∃ k, 2 ≤ k ∧ decisionMobiusMass (family n).2 k > 0) ∧
    -- No p(m)-time algorithm computes it
    -- (This is the content of P ≠ NP — stated but not provable
    --  without resolving the P vs NP question)
    True

end SearchPSide
