import Mathlib

/-!
# Search Bridge — From Verifier Complexity to Decision Complexity

## The Reframing

The previous framework (TracedMobiusBridge) measured the **verifier polynomial**:
given an assignment x, check whether φ(x) = 1. This is the product Π_c c(x),
which is computable in linear time. The bridge failed because every correct
solver trivially achieves verification-level interaction — verification is easy.

P ≠ NP is about the **search/decision** problem: given a formula φ, determine
whether ∃x such that φ(x) = 1. The hard part is the existential quantifier —
the aggregation over 2^n candidate assignments.

This file formalizes three layers:

1. **Verifier polynomial** V_φ(x) = Π_c c(x) — easy, in P
2. **Witness-summed polynomial** D(φ) = Σ_{x ∈ {0,1}^n} V_φ(x) — counts
   satisfying assignments (#SAT), VNP-style sum over exponentially many witnesses
3. **Compiled search polynomial** P_M(φ, s) — the Tseitin encoding of a
   purported poly-time SAT solver M, where s encodes the solver's state/tape

The bridge claim becomes: if M correctly decides SAT, then its compiled
search polynomial must preserve enough of the witness aggregation complexity
of D(φ). This is a claim about search-side interaction, not verifier-side.

## Connection to Fuzzy-Graph Architecture

The fuzzy-graph AGI separates:
- **Proposer**: generates candidate solutions (= search over assignments)
- **Selector**: verifies candidates (= evaluation of V_φ(x))

The previous framework only measured the selector. The correct target
measures the proposer — the search process itself.
-/

namespace SearchBridge

open Finset BigOperators MvPolynomial

/-! ## 1. Formula and Assignment Types -/

/-- A CNF formula: m clauses over n variables.
    Each clause is a set of literals (positive or negative variables). -/
structure CNFFormula where
  numVars : ℕ
  numClauses : ℕ
  -- Each clause maps variables to: +1 (positive), -1 (negative), 0 (absent)
  clauseSign : Fin numClauses → Fin numVars → Int

/-- An assignment of boolean values to variables. -/
abbrev Assignment (n : ℕ) := Fin n → Bool

/-- A clause is satisfied by an assignment if some literal is satisfied. -/
def clauseSatisfied (φ : CNFFormula) (c : Fin φ.numClauses)
    (x : Assignment φ.numVars) : Bool :=
  decide (∃ v : Fin φ.numVars,
    (φ.clauseSign c v = 1 ∧ x v = true) ∨
    (φ.clauseSign c v = -1 ∧ x v = false))

/-- A formula is satisfied by an assignment if all clauses are satisfied. -/
def formulaSatisfied (φ : CNFFormula) (x : Assignment φ.numVars) : Bool :=
  decide (∀ c : Fin φ.numClauses, clauseSatisfied φ c x = true)

/-- A formula is satisfiable if some assignment satisfies it. -/
def isSatisfiable (φ : CNFFormula) : Prop :=
  ∃ x : Assignment φ.numVars, formulaSatisfied φ x = true

/-! ## 2. The Three Polynomial Layers -/

/-- **Layer 1: Verifier polynomial** V_φ(x) = Π_c c(x)

    Given a specific assignment x, evaluates to 1 iff x satisfies φ.
    This is computable in O(n·m) time — verification is easy.

    As a polynomial: product of clause gadgets, each depending on O(1) variables.
    The SPDP/Möbius framework was measuring this object. -/
def verifierIsEasy : Prop :=
  -- For any CNF formula φ and assignment x, checking φ(x) takes O(n·m) time.
  -- This is the definition of NP: verification is polynomial.
  True

/-- **Layer 2: Witness-summed polynomial** D(φ) = Σ_{x ∈ {0,1}^n} V_φ(x)

    Counts satisfying assignments (#SAT). This is the VNP-style
    sum over exponentially many witnesses.

    D(φ) > 0 iff φ is satisfiable.
    Computing D(φ) exactly is #P-complete.
    Even deciding D(φ) > 0 is NP-complete. -/
noncomputable def witnessSumCount (φ : CNFFormula) : ℕ :=
  (Finset.univ : Finset (Assignment φ.numVars)).filter
    (fun x => formulaSatisfied φ x = true) |>.card

/-- SAT decision as a proposition (not computably decidable in general). -/
def satDecides (φ : CNFFormula) : Prop := witnessSumCount φ > 0

/-! ## 3. Compiled Search Polynomial -/

/-- A solver is an abstract decision procedure. -/
structure Solver where
  /-- The solver's state type. -/
  StateType : Type
  /-- Number of time steps as a function of input size. -/
  timeSteps : ℕ → ℕ
  /-- The solver claims SAT or UNSAT. -/
  decides : CNFFormula → Bool

/-- A solver is correct if it agrees with satisfiability. -/
def Solver.isCorrect (M : Solver) : Prop :=
  ∀ φ : CNFFormula, M.decides φ = true ↔ isSatisfiable φ

/-- A solver is poly-time if its time steps are polynomially bounded. -/
def Solver.isPolyTime (M : Solver) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, M.timeSteps n ≤ n ^ c + c

/-! ## 4. The Search-Side Observable

Instead of measuring Möbius mass of the verifier polynomial V_φ(x),
we measure interaction complexity of the decision map φ ↦ SAT(φ).

The key shift: content variables are now **formula description bits**
(which clauses are present), not assignment bits.

For a family of formulas with n variables and m clauses:
- The "content" is the clause structure of φ
- The "search state" is the solver's internal computation
- The decision D(φ) aggregates over 2^n witnesses -/

/-- Search interaction mass: how much k-way interaction between
    clause groups is required to determine satisfiability.

    For disjoint clause groups C₁, ..., C_m:
    - Removing any single group can change satisfiability
    - The interaction structure of SAT requires checking
      all clause groups simultaneously
    - This creates genuine m-way interaction -/
def searchInteractionMass (m k : ℕ) : ℕ :=
  -- The number of k-subsets of m clauses whose joint presence/absence
  -- affects the satisfiability decision.
  -- For random 3-SAT near threshold: essentially ALL subsets matter.
  m.choose k

/-! ## 5. The Search Bridge Claims

These replace the previous verification-side bridge claims.
The key difference: we're now asking about the complexity of
the MAP φ ↦ SAT(φ), not the map x ↦ φ(x). -/

/-- **Weak Search Bridge**: A correct poly-time SAT solver must
    create pairwise search interaction between clause groups.

    Intuition: if adding/removing clause c_i can flip satisfiability,
    and similarly for c_j, then the solver must "know" about both
    simultaneously — creating pairwise interaction. -/
def WeakSearchBridge : Prop :=
  ∀ (M : Solver), M.isCorrect → M.isPolyTime →
    -- The compiled search polynomial has nonzero pairwise interaction
    -- between clause groups in the formula description
    True  -- placeholder: formalize via search-side Möbius observable

/-- **Strong Search Bridge**: A correct poly-time SAT solver's
    search interaction mass at level k must match the combinatorial
    lower bound from the decision function.

    This is the search-side analogue of the previous bridge_claim,
    but now measuring the RIGHT object. -/
def StrongSearchBridge : Prop :=
  ∀ (M : Solver), M.isCorrect → M.isPolyTime →
    -- For all k ≤ log₂ m:
    -- searchInteractionMass(m, k) ≤ M's compiled search interaction at level k
    True  -- placeholder

/-! ## 6. The Honest Gap

### What is now clear:

1. The previous framework correctly separated product form from sum form
   at the VERIFIER level — but this was insufficient because verification
   is easy (P-time) for all representations.

2. The correct target is the DECISION/SEARCH level: the map φ ↦ SAT(φ).
   This is where the existential quantifier lives and where P vs NP
   content resides.

3. The witness-summed polynomial D(φ) = Σ_x V_φ(x) has a natural
   VNP-style representation as a sum over exponentially many witnesses.
   The open question is whether any poly-size compiled representation
   can realize the same decision without incurring the corresponding
   interaction complexity.

### What remains open:

The search-side bridge claims above are stated abstractly. To make them
precise, one needs:

(a) A formal definition of "search interaction mass" for the compiled
    polynomial P_M(φ, s) of a solver M — this should be the Möbius
    inversion applied to the FORMULA DESCRIPTION variables, not the
    assignment variables.

(b) A lower bound on the search interaction mass of the decision
    function SAT itself — this should come from the combinatorial
    structure of satisfiability near the phase transition.

(c) A proof that poly-time computation cannot generate sufficient
    search interaction mass — this is the actual P ≠ NP content,
    now cleanly located.

### The status:

We have shifted from verifier complexity to search/decision complexity.
The missing bridge is no longer a claim about preserving verifier
interaction mass, but about preserving search-side witness aggregation
complexity. This is a strictly better formulation of the open problem. -/

/-! ## 7. Connection to Known Complexity Theory

The search-side formulation connects to several known frameworks:

- **VP vs VNP (Valiant)**: D(φ) is a VNP family (sum over witnesses).
  VP ≠ VNP would imply D(φ) has no poly-size algebraic circuit.
  This is a known open conjecture, widely believed true.

- **Communication complexity**: The search interaction mass relates
  to the multi-party communication complexity of SAT under partition
  of the clause set. Known lower bounds exist for specific partitions.

- **Proof complexity**: The number of "interaction steps" in the
  search process relates to proof length in resolution/cutting-planes.
  Known exponential lower bounds exist for restricted proof systems.

- **SPDP original**: The rank-based framework measures algebraic
  dimension. In the search setting, the relevant dimension is the
  number of independent "search directions" the solver must explore.

The reframing suggests that the SPDP rank should measure the
**search polynomial**'s structure, not the verifier polynomial's. -/

end SearchBridge
