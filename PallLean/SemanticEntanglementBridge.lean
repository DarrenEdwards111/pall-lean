import Mathlib.Data.Nat.Lattice

/-!
# Semantic entanglement: the honest representation-invariant bridge

An algebraic rank or CEW bound on one encoding is not a lower bound on the
Boolean function computed by that encoding.  This file removes that ambiguity
by minimizing the cost over *all* representations computing the same function.

The resulting separation theorem is unconditional as a piece of logic, but it
is deliberately conditional as a complexity result: a superpolynomial lower
bound on `semanticEntanglement` is an explicit hypothesis.  No extraction map,
compiler gauge, or hidden axiom supplies that hypothesis.
-/

namespace SemanticEntanglementBridge

/-- A nonuniform family of Boolean functions, indexed by input length. -/
abbrev BoolFamily (Input : Nat → Type) := (n : Nat) → Input n → Bool

/--
An entanglement model consists of representations, their semantics, and a
natural-valued cost.  `Rep n` may later be instantiated by circuits, compiled
polynomials, or blocked SPDP objects; `cost` may be CEW or SPDP rank.
-/
structure Model (Input : Nat → Type) where
  Rep : Nat → Type
  computes : {n : Nat} → Rep n → (Input n → Bool) → Prop
  cost : {n : Nat} → Rep n → Nat

variable {Input : Nat → Type}

/-- Costs of every representation that computes `f` at length `n`. -/
def realizationCosts (M : Model Input) (f : BoolFamily Input) (n : Nat) : Set Nat :=
  {k | ∃ r : M.Rep n, M.computes r (f n) ∧ M.cost r = k}

/--
Representation-invariant entanglement: the least cost among *all*
representations computing the same Boolean function.
-/
noncomputable def semanticEntanglement
    (M : Model Input) (f : BoolFamily Input) (n : Nat) : Nat :=
  sInf (realizationCosts M f n)

/-- Any concrete realization upper-bounds the semantic minimum. -/
theorem semanticEntanglement_le_cost
    (M : Model Input) (f : BoolFamily Input) {n : Nat} (r : M.Rep n)
    (hr : M.computes r (f n)) :
    semanticEntanglement M f n ≤ M.cost r := by
  apply Nat.sInf_le
  exact ⟨r, hr, rfl⟩

/-- A semantic lower bound applies to every representation, not one encoding. -/
theorem cost_ge_semanticEntanglement
    (M : Model Input) (f : BoolFamily Input) {n lower : Nat}
    (hLower : lower ≤ semanticEntanglement M f n)
    (r : M.Rep n) (hr : M.computes r (f n)) :
    lower ≤ M.cost r :=
  hLower.trans (semanticEntanglement_le_cost M f r hr)

/-- A family has polynomial-cost realizations in the selected model. -/
def HasPolynomialRealizations (M : Model Input) (f : BoolFamily Input) : Prop :=
  ∃ c : Nat, ∀ n : Nat, ∃ r : M.Rep n,
    M.computes r (f n) ∧ M.cost r ≤ (n + 1) ^ c

/-- The representation-invariant cost eventually escapes every polynomial. -/
def HasSuperpolynomialSemanticEntanglement
    (M : Model Input) (f : BoolFamily Input) : Prop :=
  ∀ c : Nat, ∃ n : Nat, (n + 1) ^ c < semanticEntanglement M f n

/-- Polynomial concrete realizations give a polynomial semantic upper bound. -/
theorem polynomial_realizations_bound_semanticEntanglement
    (M : Model Input) (f : BoolFamily Input)
    (hPoly : HasPolynomialRealizations M f) :
    ∃ c : Nat, ∀ n : Nat, semanticEntanglement M f n ≤ (n + 1) ^ c := by
  obtain ⟨c, hc⟩ := hPoly
  refine ⟨c, ?_⟩
  intro n
  obtain ⟨r, hr, hcost⟩ := hc n
  exact (semanticEntanglement_le_cost M f r hr).trans hcost

/--
The exact honest lower-bound bridge: a semantic superpolynomial lower bound
rules out polynomial-cost realizations.  The contradiction compares the same
function and minimizes over all of its representations.
-/
theorem superpolynomial_semanticEntanglement_not_polynomial
    (M : Model Input) (f : BoolFamily Input)
    (hHard : HasSuperpolynomialSemanticEntanglement M f) :
    ¬ HasPolynomialRealizations M f := by
  intro hPoly
  obtain ⟨c, hc⟩ := polynomial_realizations_bound_semanticEntanglement M f hPoly
  obtain ⟨n, hn⟩ := hHard c
  exact (Nat.not_lt_of_ge (hc n)) hn

/--
Abstract P-versus-NP corollary.  An actual application must prove both named
premises for a concrete general-computation model.  In particular, `hSAT` is
the genuine general-circuit lower bound and is not manufactured by this file.
-/
theorem separation_of_semantic_entanglement
    (M : Model Input)
    (InP InNP : BoolFamily Input → Prop)
    (SAT : BoolFamily Input)
    (p_has_poly_realizations : ∀ f, InP f → HasPolynomialRealizations M f)
    (hSATNP : InNP SAT)
    (hSAT : HasSuperpolynomialSemanticEntanglement M SAT) :
    InP ≠ InNP := by
  intro hEq
  have hSATP : InP SAT := by simpa [hEq] using hSATNP
  exact superpolynomial_semanticEntanglement_not_polynomial M SAT hSAT
    (p_has_poly_realizations SAT hSATP)

#print axioms semanticEntanglement_le_cost
#print axioms cost_ge_semanticEntanglement
#print axioms polynomial_realizations_bound_semanticEntanglement
#print axioms superpolynomial_semanticEntanglement_not_polynomial
#print axioms separation_of_semantic_entanglement

end SemanticEntanglementBridge
