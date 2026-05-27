import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSignedCounterfactualEKP

/-!
# Concrete signed 3-CNF model

The signed counterfactual EKP surface is formula-parametric.  This file gives
it a small concrete model with negated literals and an exhibited UNSAT
instance.  The point is non-vacuity: the signed route now ranges over a formula
semantics that contains both satisfiable and unsatisfiable formulas.

This does not prove the paper-instrumented transport theorem.  It only removes
the positive-only `ThreeCNF` blocker from the signed surface.
-/

namespace PallLean.Paper93.DeepMath.PathB

/-! ## Signed 3-CNF syntax -/

/-- A signed Boolean literal over `n` variables. -/
inductive SignedLiteral (n : Nat) where
  | pos : Fin n -> SignedLiteral n
  | neg : Fin n -> SignedLiteral n
deriving DecidableEq

namespace SignedLiteral

/-- Evaluate a signed literal under a Boolean assignment. -/
def eval {n : Nat} (σ : Fin n -> Bool) : SignedLiteral n -> Bool
  | pos i => σ i
  | neg i => !(σ i)

end SignedLiteral

/-- A 3-CNF clause with signed literals.  Repeated variables are allowed; this
lets unit clauses be represented as `(l ∨ l ∨ l)`. -/
structure SignedClause3 (n : Nat) where
  lit1 : SignedLiteral n
  lit2 : SignedLiteral n
  lit3 : SignedLiteral n
deriving DecidableEq

namespace SignedClause3

/-- Boolean clause evaluation. -/
def eval {n : Nat} (σ : Fin n -> Bool) (c : SignedClause3 n) : Bool :=
  c.lit1.eval σ || c.lit2.eval σ || c.lit3.eval σ

/-- Propositional clause satisfaction. -/
def Satisfied {n : Nat} (σ : Fin n -> Bool) (c : SignedClause3 n) : Prop :=
  c.eval σ = true

end SignedClause3

/-- A signed 3-CNF formula. -/
structure SignedThreeCNF where
  numVars : Nat
  clauses : List (SignedClause3 numVars)

namespace SignedThreeCNF

/-- A signed 3-CNF formula is satisfiable if some Boolean assignment satisfies
every signed clause. -/
def IsSatisfiable (φ : SignedThreeCNF) : Prop :=
  ∃ σ : Fin φ.numVars -> Bool,
    ∀ c : SignedClause3 φ.numVars, c ∈ φ.clauses ->
      SignedClause3.Satisfied σ c

/-- A simple size measure compatible with the generic signed encoding surface.
Each signed literal needs a variable reference and one sign bit; the exact
constant is irrelevant for the semantic non-vacuity result. -/
def encodingSize (φ : SignedThreeCNF) : Nat :=
  φ.numVars + 6 * φ.clauses.length

end SignedThreeCNF

/-! ## Tiny satisfiable and unsatisfiable examples -/

def signedUnitPosClause : SignedClause3 1 where
  lit1 := SignedLiteral.pos 0
  lit2 := SignedLiteral.pos 0
  lit3 := SignedLiteral.pos 0

def signedUnitNegClause : SignedClause3 1 where
  lit1 := SignedLiteral.neg 0
  lit2 := SignedLiteral.neg 0
  lit3 := SignedLiteral.neg 0

/-- The satisfiable formula `(x ∨ x ∨ x)`. -/
def signedPositiveUnitFormula : SignedThreeCNF where
  numVars := 1
  clauses := [signedUnitPosClause]

/-- The contradiction `(x ∨ x ∨ x) ∧ (¬x ∨ ¬x ∨ ¬x)`. -/
def signedContradictionFormula : SignedThreeCNF where
  numVars := 1
  clauses := [signedUnitPosClause, signedUnitNegClause]

theorem signedPositiveUnitFormula_satisfiable :
    signedPositiveUnitFormula.IsSatisfiable := by
  refine ⟨fun _ => true, ?_⟩
  intro c hc
  simp [signedPositiveUnitFormula] at hc
  subst c
  simp [signedUnitPosClause, SignedClause3.Satisfied, SignedClause3.eval,
    SignedLiteral.eval]

theorem signedContradictionFormula_unsatisfiable :
    Not signedContradictionFormula.IsSatisfiable := by
  rintro ⟨σ, hσ⟩
  have hpos : SignedClause3.Satisfied σ signedUnitPosClause := by
    exact hσ signedUnitPosClause (by simp [signedContradictionFormula])
  have hneg : SignedClause3.Satisfied σ signedUnitNegClause := by
    exact hσ signedUnitNegClause (by simp [signedContradictionFormula])
  let x : Fin signedContradictionFormula.numVars := ⟨0, by decide⟩
  have hxTrue : σ x = true := by
    simpa [x, signedUnitPosClause, SignedClause3.Satisfied,
      SignedClause3.eval, SignedLiteral.eval] using hpos
  have hxFalse : σ x = false := by
    simpa [x, signedUnitNegClause, SignedClause3.Satisfied,
      SignedClause3.eval, SignedLiteral.eval] using hneg
  rw [hxTrue] at hxFalse
  simp at hxFalse

/-! ## SignedFormulaEncoding instance -/

/-- A concrete signed-formula encoding relation.

This is intentionally semantic rather than parser-specific: any input of
sufficient length may serve as an encoding of a formula.  It is enough for the
counterfactual interface, whose load-bearing issue is signed SAT/UNSAT
semantics, not bit-parser uniqueness. -/
def signedThreeCNFEncoding : SignedFormulaEncoding where
  Formula := SignedThreeCNF
  Encodes := fun {n} _input φ => φ.encodingSize <= n
  Satisfiable := SignedThreeCNF.IsSatisfiable

/-- The concrete signed encoding has at least one satisfiable formula and at
least one unsatisfiable formula. -/
theorem signedThreeCNFEncoding_nonvacuous :
    (exists φ : signedThreeCNFEncoding.Formula,
      signedThreeCNFEncoding.Satisfiable φ) /\
    (exists ψ : signedThreeCNFEncoding.Formula,
      Not (signedThreeCNFEncoding.Satisfiable ψ)) := by
  constructor
  · exact ⟨signedPositiveUnitFormula, signedPositiveUnitFormula_satisfiable⟩
  · exact ⟨signedContradictionFormula, signedContradictionFormula_unsatisfiable⟩

/-- The satisfiable example is encodable at its own size. -/
theorem signedPositiveUnitFormula_encodable_at_size :
    signedThreeCNFEncoding.Encodes
      (n := signedPositiveUnitFormula.encodingSize)
      (fun _ => false)
      signedPositiveUnitFormula := by
  simp [signedThreeCNFEncoding]

/-- The unsatisfiable example is encodable at its own size. -/
theorem signedContradictionFormula_encodable_at_size :
    signedThreeCNFEncoding.Encodes
      (n := signedContradictionFormula.encodingSize)
      (fun _ => false)
      signedContradictionFormula := by
  simp [signedThreeCNFEncoding]

/-- The concrete signed encoding contains encoded examples on both sides of
the SAT/UNSAT divide.  This is the non-vacuity fact needed by the signed
counterfactual surface. -/
theorem signedThreeCNFEncoding_encoded_nonvacuous :
    (exists (n : Nat) (input : Fin n -> Bool)
        (φ : signedThreeCNFEncoding.Formula),
      signedThreeCNFEncoding.Encodes (n := n) input φ /\
      signedThreeCNFEncoding.Satisfiable φ) /\
    (exists (n : Nat) (input : Fin n -> Bool)
        (ψ : signedThreeCNFEncoding.Formula),
      signedThreeCNFEncoding.Encodes (n := n) input ψ /\
      Not (signedThreeCNFEncoding.Satisfiable ψ)) := by
  constructor
  · refine ⟨signedPositiveUnitFormula.encodingSize, fun _ => false,
      signedPositiveUnitFormula, ?_, signedPositiveUnitFormula_satisfiable⟩
    exact signedPositiveUnitFormula_encodable_at_size
  · refine ⟨signedContradictionFormula.encodingSize, fun _ => false,
      signedContradictionFormula, ?_, signedContradictionFormula_unsatisfiable⟩
    exact signedContradictionFormula_encodable_at_size

/-! ## Kernel-only axiom trace -/

#print axioms signedPositiveUnitFormula_satisfiable
#print axioms signedContradictionFormula_unsatisfiable
#print axioms signedThreeCNFEncoding_nonvacuous
#print axioms signedPositiveUnitFormula_encodable_at_size
#print axioms signedContradictionFormula_encodable_at_size
#print axioms signedThreeCNFEncoding_encoded_nonvacuous

end PallLean.Paper93.DeepMath.PathB
