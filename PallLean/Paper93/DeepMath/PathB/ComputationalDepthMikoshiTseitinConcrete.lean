import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMikoshiTseitinBoundary
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthVerifierNormalForm

/-!
# Concrete one-edge signed Tseitin boundary

`ComputationalDepthMikoshiTseitinBoundary` introduced the restricted-family
target.  This file instantiates the first concrete signed parity-flip family
inside the current signed-3CNF syntax.

The instance is deliberately tiny: a one-edge Tseitin system.  The even-charge
formula repeats the same unit edge constraint twice and is satisfiable; flipping
one endpoint charge gives the odd formula `x ∧ ¬x`, which is unsatisfiable.

This is not the asymptotic Tseitin expander family and it is not a P-vs-NP
proof.  It removes one layer of abstraction by showing that the signed
counterfactual boundary interface can be inhabited from an actual signed SAT
decider and an explicit SAT/UNSAT parity-flip pair.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine

/-! ## One-edge signed Tseitin formulas -/

/-- One-edge even-charge Tseitin instance: both endpoint constraints require
the edge variable to be `true`.  It is satisfiable. -/
def signedOneEdgeTseitinEvenFormula : SignedThreeCNF where
  numVars := 1
  clauses := [signedUnitPosClause, signedUnitPosClause]

/-- One-edge odd-charge Tseitin instance: one endpoint requires `true`, the
other requires `false`.  This is exactly the signed contradiction formula. -/
def signedOneEdgeTseitinOddFormula : SignedThreeCNF :=
  signedContradictionFormula

theorem signedOneEdgeTseitinEvenFormula_satisfiable :
    signedOneEdgeTseitinEvenFormula.IsSatisfiable := by
  refine ⟨fun _ => true, ?_⟩
  intro c hc
  simp [signedOneEdgeTseitinEvenFormula] at hc
  subst c
  simp [signedUnitPosClause, SignedClause3.Satisfied, SignedClause3.eval,
    SignedLiteral.eval]

theorem signedOneEdgeTseitinOddFormula_unsatisfiable :
    Not signedOneEdgeTseitinOddFormula.IsSatisfiable := by
  simpa [signedOneEdgeTseitinOddFormula] using
    signedContradictionFormula_unsatisfiable

/-- The common input length used for the one-edge parity-flip pair. -/
abbrev signedOneEdgeTseitinLength : Nat :=
  signedOneEdgeTseitinOddFormula.encodingSize

/-- The binomial floor at the concrete one-edge input length. -/
abbrev signedOneEdgeTseitinDirectionCount : Nat :=
  Nat.choose (signedOneEdgeTseitinLength / 3)
    (Nat.log 2 signedOneEdgeTseitinLength)

theorem signedOneEdgeTseitinLength_ge_one :
    signedOneEdgeTseitinLength >= 1 := by
  decide

theorem signedOneEdgeTseitinDirectionCount_pos :
    0 < signedOneEdgeTseitinDirectionCount := by
  decide

/-- A fixed dummy bitstring at the one-edge Tseitin input length.  The current
`signedThreeCNFEncoding` is semantic/size-based, so the bit contents are not
load-bearing. -/
def signedOneEdgeTseitinInput : Fin signedOneEdgeTseitinLength -> Bool :=
  fun _ => false

theorem signedOneEdgeTseitinEven_encodable :
    signedThreeCNFEncoding.Encodes
      (n := signedOneEdgeTseitinLength)
  signedOneEdgeTseitinInput
      signedOneEdgeTseitinEvenFormula := by
  simp [signedThreeCNFEncoding, SignedThreeCNF.encodingSize,
    signedOneEdgeTseitinOddFormula, signedOneEdgeTseitinEvenFormula,
    signedContradictionFormula]

theorem signedOneEdgeTseitinOdd_encodable :
    signedThreeCNFEncoding.Encodes
      (n := signedOneEdgeTseitinLength)
      signedOneEdgeTseitinInput
      signedOneEdgeTseitinOddFormula := by
  simp [signedThreeCNFEncoding, SignedThreeCNF.encodingSize,
    signedOneEdgeTseitinOddFormula, signedContradictionFormula]

/-! ## Concrete coverage from any signed SAT decider -/

/-- Any signed SAT decider gives signed counterfactual coverage for the
one-edge Tseitin parity flip.  The multiple directions here are the concrete
binomial floor at this fixed small length; they all use the same SAT/UNSAT
formula pair and distinct direction tags.

The asymptotic expander/Tseitin family must replace this seed before any
serious lower-bound claim is made. -/
def signedOneEdgeTseitinCoverage_of_decider
    (M : DTM)
    (hM : SignedDTMDecidesSAT signedThreeCNFEncoding M) :
    SignedCounterfactualEKPDirectionCoverage
      signedThreeCNFEncoding M signedOneEdgeTseitinLength where
  hn := signedOneEdgeTseitinLength_ge_one
  directionCount := signedOneEdgeTseitinDirectionCount
  directionCount_pos := signedOneEdgeTseitinDirectionCount_pos
  direction_floor := Nat.le_refl _
  positiveInput := fun _ => signedOneEdgeTseitinInput
  negativeInput := fun _ => signedOneEdgeTseitinInput
  positiveFormula := fun _ => signedOneEdgeTseitinEvenFormula
  negativeFormula := fun _ => signedOneEdgeTseitinOddFormula
  positive_encoded := fun _ => signedOneEdgeTseitinEven_encodable
  negative_encoded := fun _ => signedOneEdgeTseitinOdd_encodable
  positive_satisfiable := fun _ =>
    signedOneEdgeTseitinEvenFormula_satisfiable
  negative_unsatisfiable := fun _ =>
    signedOneEdgeTseitinOddFormula_unsatisfiable
  positive_accepts := by
    intro d
    exact
      (hM signedOneEdgeTseitinLength_ge_one signedOneEdgeTseitinInput
        signedOneEdgeTseitinEvenFormula
        signedOneEdgeTseitinEven_encodable).2
          signedOneEdgeTseitinEvenFormula_satisfiable
  negative_not_accepts := by
    intro d hacc
    have hs :
        signedThreeCNFEncoding.Satisfiable
          signedOneEdgeTseitinOddFormula :=
      (hM signedOneEdgeTseitinLength_ge_one signedOneEdgeTseitinInput
        signedOneEdgeTseitinOddFormula
        signedOneEdgeTseitinOdd_encodable).1 hacc
    exact signedOneEdgeTseitinOddFormula_unsatisfiable hs
  directionOf := fun d => { tag := d.val }
  direction_injective := by
    intro d e h
    apply Fin.ext
    exact congrArg SignedCounterfactualEKPDirection.tag h

/-- The concrete one-edge coverage is a signed Tseitin parity-flip boundary. -/
def signedOneEdgeTseitinParityFlipBoundary_of_decider
    (M : DTM)
    (hM : SignedDTMDecidesSAT signedThreeCNFEncoding M) :
    SignedTseitinParityFlipBoundary
      signedThreeCNFEncoding M signedOneEdgeTseitinLength where
  coverage := signedOneEdgeTseitinCoverage_of_decider M hM
  parityFlipCoordinate := fun d => d.val
  parityFlipCoordinate_injective := by
    intro d e h
    exact Fin.ext h
  positive_even_charge := fun _ =>
    signedOneEdgeTseitinEvenFormula_satisfiable
  negative_odd_charge := fun _ =>
    signedOneEdgeTseitinOddFormula_unsatisfiable

/-- The one-edge seed supplies the parity-flip SAT/UNSAT semantic facts for
any signed SAT decider. -/
theorem signedOneEdgeTseitinBoundary_semantic_sound
    (M : DTM)
    (hM : SignedDTMDecidesSAT signedThreeCNFEncoding M)
    (d : Fin
      (signedOneEdgeTseitinParityFlipBoundary_of_decider M hM).coverage.directionCount) :
    signedThreeCNFEncoding.Satisfiable
        ((signedOneEdgeTseitinParityFlipBoundary_of_decider M hM).coverage.positiveFormula d) /\
      Not (signedThreeCNFEncoding.Satisfiable
        ((signedOneEdgeTseitinParityFlipBoundary_of_decider M hM).coverage.negativeFormula d)) /\
        TuringMachine.accepts M signedOneEdgeTseitinLength
          (signedOneEdgeTseitinParityFlipBoundary_of_decider M hM).coverage.hn
          ((signedOneEdgeTseitinParityFlipBoundary_of_decider M hM).coverage.positiveInput d) /\
          Not (TuringMachine.accepts M signedOneEdgeTseitinLength
            (signedOneEdgeTseitinParityFlipBoundary_of_decider M hM).coverage.hn
            ((signedOneEdgeTseitinParityFlipBoundary_of_decider M hM).coverage.negativeInput d)) :=
  (signedOneEdgeTseitinParityFlipBoundary_of_decider M hM).semantic_sound d

/-! ## Kernel-only axiom trace -/

#print axioms signedOneEdgeTseitinEvenFormula_satisfiable
#print axioms signedOneEdgeTseitinOddFormula_unsatisfiable
#print axioms signedOneEdgeTseitinLength_ge_one
#print axioms signedOneEdgeTseitinDirectionCount_pos
#print axioms signedOneEdgeTseitinEven_encodable
#print axioms signedOneEdgeTseitinOdd_encodable
#print axioms signedOneEdgeTseitinCoverage_of_decider
#print axioms signedOneEdgeTseitinParityFlipBoundary_of_decider
#print axioms signedOneEdgeTseitinBoundary_semantic_sound

end PallLean.Paper93.DeepMath.PathB
