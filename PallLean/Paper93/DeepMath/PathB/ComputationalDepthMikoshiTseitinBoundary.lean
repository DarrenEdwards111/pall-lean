import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMikoshiContextualFrontier
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSignedThreeCNFModel

/-!
# Mikoshi signed-Tseitin boundary target

The Mikoshi contextual frontier is useful only after its description cost is
made concrete.  This file adds the first concrete restricted-family target:

* descriptions are finite relational programs/context graphs;
* cost is node/edge/rule/evidence size;
* the boundary family is a signed Tseitin parity-flip interface;
* a no-short-description certificate for that family gives the existing
  observer-K^t/metacomplexity target.

This is a restricted-model lower-bound target, not a proof of `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine

/-! ## Concrete relational-program descriptions -/

/-- A finite relational program/context graph in the Mikoshi style.

The fields are intentionally coarse but concrete: the observer pays for
entities, relations, rules, evidence links, and context switches. -/
structure MikoshiRelationalProgramDescription where
  entityNodes : Nat
  relationEdges : Nat
  rewriteRules : Nat
  evidenceLinks : Nat
  contextSwitches : Nat

namespace MikoshiRelationalProgramDescription

/-- Coarse size/cost of a finite relational-program description. -/
def cost (D : MikoshiRelationalProgramDescription) : Nat :=
  D.entityNodes + D.relationEdges + D.rewriteRules +
    D.evidenceLinks + D.contextSwitches

end MikoshiRelationalProgramDescription

/-- A concrete Mikoshi description model using finite relational programs.

`reconstructs` is the semantic reconstruction predicate for the chosen family.
The file does not choose it after the fact in theorems; it is fixed as part of
the model. -/
def mikoshiRelationalProgramDescriptionModel
    (enc : SignedFormulaEncoding)
    (budget : Nat -> Nat)
    (reconstructs :
      forall {M : DTM} {n : Nat},
        SignedCounterfactualEKPDirectionCoverage enc M n ->
          MikoshiRelationalProgramDescription -> Prop) :
    MikoshiContextDescriptionModel enc where
  Description := MikoshiRelationalProgramDescription
  descCost := MikoshiRelationalProgramDescription.cost
  observerBudget := budget
  reconstructsSATBoundary := reconstructs

/-! ## Signed Tseitin parity-flip boundary interface -/

/-- A signed Tseitin parity-flip boundary family.

The `coverage` field is the existing signed counterfactual SAT/UNSAT coverage.
The extra fields state that the directions are intended to be genuine
parity-flip coordinates, with positive/even-charge and negative/odd-charge
semantics.  These fields are semantic obligations for a later concrete Tseitin
instantiation; they are not used to smuggle the lower bound. -/
structure SignedTseitinParityFlipBoundary
    (enc : SignedFormulaEncoding) (M : DTM) (n : Nat) : Type where
  coverage : SignedCounterfactualEKPDirectionCoverage enc M n
  parityFlipCoordinate : Fin coverage.directionCount -> Nat
  parityFlipCoordinate_injective :
    Function.Injective parityFlipCoordinate
  positive_even_charge :
    forall d : Fin coverage.directionCount,
      enc.Satisfiable (coverage.positiveFormula d)
  negative_odd_charge :
    forall d : Fin coverage.directionCount,
      Not (enc.Satisfiable (coverage.negativeFormula d))

namespace SignedTseitinParityFlipBoundary

/-- The underlying signed counterfactual coverage of a parity-flip boundary. -/
def toCoverage
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n) :
    SignedCounterfactualEKPDirectionCoverage enc M n :=
  T.coverage

/-- A parity-flip boundary carries the signed SAT/UNSAT semantic facts already
stored in its coverage object. -/
theorem semantic_sound
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n)
    (d : Fin T.coverage.directionCount) :
    enc.Satisfiable (T.coverage.positiveFormula d) /\
      Not (enc.Satisfiable (T.coverage.negativeFormula d)) /\
        TuringMachine.accepts M n T.coverage.hn
          (T.coverage.positiveInput d) /\
          Not (TuringMachine.accepts M n T.coverage.hn
            (T.coverage.negativeInput d)) :=
  ⟨T.positive_even_charge d, T.negative_odd_charge d,
    T.coverage.positive_accepts d, T.coverage.negative_not_accepts d⟩

end SignedTseitinParityFlipBoundary

/-! ## No-short-description target for the restricted family -/

/-- A no-short-description certificate for a signed Tseitin parity-flip
boundary under a fixed relational-program model. -/
structure NoShortSignedTseitinMikoshiDescription
    {enc : SignedFormulaEncoding}
    (Model : MikoshiContextDescriptionModel enc)
    {M : DTM} {n : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n) : Type 2 where
  certificate :
    NoShortMikoshiSATDescription Model T.coverage

namespace NoShortSignedTseitinMikoshiDescription

/-- Forgetting the Tseitin parity-flip metadata gives the general Mikoshi
no-short-description certificate. -/
def toNoShortMikoshiSATDescription
    {enc : SignedFormulaEncoding}
    {Model : MikoshiContextDescriptionModel enc}
    {M : DTM} {n : Nat}
    {T : SignedTseitinParityFlipBoundary enc M n}
    (H : NoShortSignedTseitinMikoshiDescription Model T) :
    NoShortMikoshiSATDescription Model T.coverage :=
  H.certificate

/-- A no-short-description theorem for a signed Tseitin parity-flip boundary
gives the observer-K^t certificate for the machine. -/
theorem existsObserverKtCertificate
    {enc : SignedFormulaEncoding}
    {Model : MikoshiContextDescriptionModel enc}
    {M : DTM} {n : Nat}
    {T : SignedTseitinParityFlipBoundary enc M n}
    (H : NoShortSignedTseitinMikoshiDescription Model T) :
    exists Cert : ObserverKtBoundaryCertificate enc M, Cert.High :=
  H.toNoShortMikoshiSATDescription.existsObserverKtCertificate

end NoShortSignedTseitinMikoshiDescription

/-- Restricted-family lower bound: every signed SAT decider has some signed
Tseitin parity-flip boundary with no short Mikoshi relational-program
description.

This is the first honest restricted-model target to attack before trying to
lift anything to full SAT/P-vs-NP. -/
structure SignedTseitinMikoshiDescriptionLowerBound
    (enc : SignedFormulaEncoding)
    (Model : MikoshiContextDescriptionModel enc) : Type 2 where
  existsNoShortTseitinBoundary :
    forall M : DTM,
      SignedDTMDecidesSAT enc M ->
        exists n : Nat,
          exists T : SignedTseitinParityFlipBoundary enc M n,
            Nonempty (NoShortSignedTseitinMikoshiDescription Model T)

namespace SignedTseitinMikoshiDescriptionLowerBound

/-- The restricted signed-Tseitin target implies the general Mikoshi
description lower-bound target. -/
def toMikoshiDescriptionLowerBound
    {enc : SignedFormulaEncoding}
    {Model : MikoshiContextDescriptionModel enc}
    (H : SignedTseitinMikoshiDescriptionLowerBound enc Model) :
    MikoshiDescriptionLowerBound enc Model where
  existsNoShortDescription := by
    intro M hM
    rcases H.existsNoShortTseitinBoundary M hM with ⟨n, T, HT⟩
    rcases HT with ⟨HTcert⟩
    exact ⟨n, T.coverage,
      ⟨HTcert.toNoShortMikoshiSATDescription⟩⟩

/-- Therefore, the restricted signed-Tseitin Mikoshi lower bound gives the
observer-K^t frontier theorem. -/
theorem signedSATBoundaryHasHighObserverKt
    {enc : SignedFormulaEncoding}
    {Model : MikoshiContextDescriptionModel enc}
    (H : SignedTseitinMikoshiDescriptionLowerBound enc Model) :
    SignedSATBoundaryHasHighObserverKt enc :=
  H.toMikoshiDescriptionLowerBound.signedSATBoundaryHasHighObserverKt

end SignedTseitinMikoshiDescriptionLowerBound

/-! ## A tiny non-vacuity sanity check for the signed formula layer -/

/-- The signed 3-CNF surface has a satisfiable and an unsatisfiable formula.
This is not the Tseitin family; it is only a sanity check that the signed
semantic layer is nonempty on both sides before a real parity-flip family is
instantiated. -/
theorem signedThreeCNF_has_sat_and_unsat :
    (exists φ : signedThreeCNFEncoding.Formula,
      signedThreeCNFEncoding.Satisfiable φ) /\
    (exists ψ : signedThreeCNFEncoding.Formula,
      Not (signedThreeCNFEncoding.Satisfiable ψ)) :=
  signedThreeCNFEncoding_nonvacuous

/-! ## Kernel-only axiom trace -/

#print axioms MikoshiRelationalProgramDescription.cost
#print axioms mikoshiRelationalProgramDescriptionModel
#print axioms SignedTseitinParityFlipBoundary.semantic_sound
#print axioms NoShortSignedTseitinMikoshiDescription.existsObserverKtCertificate
#print axioms SignedTseitinMikoshiDescriptionLowerBound.toMikoshiDescriptionLowerBound
#print axioms SignedTseitinMikoshiDescriptionLowerBound.signedSATBoundaryHasHighObserverKt
#print axioms signedThreeCNF_has_sat_and_unsat

end PallLean.Paper93.DeepMath.PathB
