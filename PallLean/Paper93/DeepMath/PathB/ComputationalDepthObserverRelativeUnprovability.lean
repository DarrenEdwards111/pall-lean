import PallLean.Paper93.DeepMath.PathB.ComputationalDepthVerifierNormalForm

/-!
# Observer-relative unprovability (schema-level, method-relative)

This file formalizes the *observer-relative* (method-relative) unprovability
schema discussed in PathB:

* not absolute unprovability in ZFC;
* yes: no closure by a specified class of internal `P`-bounded bridge methods.

The theorem is intentionally schema-level: if every internal `P`-bounded
bridge procedure fails to close the boundary, then observer-relative
unprovability holds for that frame.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine

/-- A `P`-observer frame: language/verification/discovery surface plus the
boundary statement to be closed. -/
structure PObserverFrame (_enc : SignedFormulaEncoding) : Type where
  Ver : Prop
  Find : Prop
  Boundary : Prop

/-- Internal `P`-bounded bridge method class for an observer frame. -/
structure InternalPBridgeProcedure
    (enc : SignedFormulaEncoding)
    (_F : PObserverFrame enc) : Type where
  Procedure : TuringMachine.DTM
  pBounded : Prop
  soundIfReturns : Prop
  closesBoundary : Prop

/-- Observer-relative unprovability: the boundary cannot be closed by any
internal `P`-bounded bridge procedure in the frame. -/
def ObserverRelativeUnprovability
    (enc : SignedFormulaEncoding)
    (F : PObserverFrame enc) : Prop :=
  forall B : InternalPBridgeProcedure enc F, Not B.closesBoundary

/-- Method-relative unprovability schema.

If every internal `P`-bounded bridge procedure fails to close the boundary,
then observer-relative unprovability holds for the frame. -/
theorem observerRelativeUnprovability_of_noInternalClosure
    {enc : SignedFormulaEncoding}
    (F : PObserverFrame enc)
    (H : forall B : InternalPBridgeProcedure enc F, Not B.closesBoundary) :
    ObserverRelativeUnprovability enc F :=
  H

/-- Contrapositive form: if observer-relative unprovability fails, then some
internal `P`-bounded bridge closes the boundary. -/
theorem existsInternalClosure_of_not_observerRelativeUnprovability
    {enc : SignedFormulaEncoding}
    (F : PObserverFrame enc)
    (H : Not (ObserverRelativeUnprovability enc F)) :
    exists B : InternalPBridgeProcedure enc F, B.closesBoundary := by
  by_contra hnone
  apply H
  intro B
  exact fun hcl => hnone ⟨B, hcl⟩

/-- Named corollary: Gödel-like observer-boundary form (method-relative only).
This is a label for use in paper text; mathematically it is the same schema
instance as `observerRelativeUnprovability_of_noInternalClosure`. -/
theorem godelLikeObserverBoundarySchema
    {enc : SignedFormulaEncoding}
    (F : PObserverFrame enc)
    (H : forall B : InternalPBridgeProcedure enc F, Not B.closesBoundary) :
    ObserverRelativeUnprovability enc F :=
  observerRelativeUnprovability_of_noInternalClosure F H

/-! ## Kernel-only axiom trace -/

#print axioms observerRelativeUnprovability_of_noInternalClosure
#print axioms existsInternalClosure_of_not_observerRelativeUnprovability
#print axioms godelLikeObserverBoundarySchema

end PallLean.Paper93.DeepMath.PathB
