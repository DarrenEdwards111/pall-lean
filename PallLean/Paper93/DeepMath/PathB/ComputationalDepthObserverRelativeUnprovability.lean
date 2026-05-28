import PallLean.Paper93.DeepMath.PathB.ComputationalDepthVerifierNormalForm

/-!
# Observer-relative unprovability (schema-level, method-relative)

This file formalizes the *observer-relative* (method-relative) unprovability
schema discussed in PathB:

* not absolute unprovability in ZFC;
* yes: no closure by a specified class of internal `P`-bounded bridge methods;
* stronger barrier form: every successful internal bridge must already expose
  the frontier obstruction, so a bridge that does not smuggle that obstruction
  cannot close the boundary.

The first theorem is intentionally schema-level: if every internal `P`-bounded
bridge procedure fails to close the boundary, then observer-relative
unprovability holds for that frame.

The later `PObserverBridgeBarrier` package is the stronger paper-facing form:
it does not merely assume no closure.  It separates two claims:

1. **barrier:** any bridge that closes the boundary exposes the obstruction;
2. **clean/internal:** a proposed bridge does not expose/smuggle that obstruction.

Together they prove that the proposed bridge cannot close the boundary.  If all
internal bridge procedures are clean in this sense, the ordinary
observer-relative unprovability statement follows.
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

/-! ## Stronger bridge-barrier form -/

/-- A paper-facing obstruction predicate for bridge methods.

`ExposesFrontierObstruction B` means that the proposed bridge has already
encoded the load-bearing witness-elimination / no-decider / faithful-decoder
obstruction.  The definition is deliberately parametric: different routes can
instantiate it with God-Move transport, faithful lift semantics, a decoder,
rank-collapse, or any other precise frontier object.
-/
structure PObserverBridgeBarrier
    (enc : SignedFormulaEncoding)
    (F : PObserverFrame enc) : Type where
  ExposesFrontierObstruction : InternalPBridgeProcedure enc F -> Prop
  everyClosureExposes :
    forall B : InternalPBridgeProcedure enc F,
      B.closesBoundary -> ExposesFrontierObstruction B

/-- A bridge is genuinely internal/clean relative to a barrier when it has not
already smuggled the frontier obstruction into its hypotheses or output. -/
def CleanInternalBridge
    {enc : SignedFormulaEncoding}
    {F : PObserverFrame enc}
    (K : PObserverBridgeBarrier enc F)
    (B : InternalPBridgeProcedure enc F) : Prop :=
  Not (K.ExposesFrontierObstruction B)

/-- Strong barrier theorem, single-bridge form.

If every successful bridge must expose the frontier obstruction, then a clean
internal bridge cannot close the boundary.  This is the precise "no proof in
this way" statement for a named bridge method: either it fails, or it already
contains the hard obstruction. -/
theorem noClosure_of_cleanInternalBridge
    {enc : SignedFormulaEncoding}
    {F : PObserverFrame enc}
    (K : PObserverBridgeBarrier enc F)
    (B : InternalPBridgeProcedure enc F)
    (hclean : CleanInternalBridge K B) :
    Not B.closesBoundary := by
  intro hclose
  exact hclean (K.everyClosureExposes B hclose)

/-- Contrapositive: any bridge that does close the boundary is not clean; it
must have exposed/smuggled the frontier obstruction. -/
theorem exposesFrontierObstruction_of_closesBoundary
    {enc : SignedFormulaEncoding}
    {F : PObserverFrame enc}
    (K : PObserverBridgeBarrier enc F)
    (B : InternalPBridgeProcedure enc F)
    (hclose : B.closesBoundary) :
    K.ExposesFrontierObstruction B :=
  K.everyClosureExposes B hclose

/-- Class-level barrier theorem.

If the barrier theorem holds and every internal bridge in the chosen method
class is clean (does not expose/smuggle the obstruction), then the original
observer-relative unprovability statement follows.  Compared with the earlier
schema, this factors the proof through an explicit obstruction-exposure theorem
rather than taking `noInternalClosure` as a black box. -/
theorem observerRelativeUnprovability_of_bridgeBarrier
    {enc : SignedFormulaEncoding}
    (F : PObserverFrame enc)
    (K : PObserverBridgeBarrier enc F)
    (Hclean : forall B : InternalPBridgeProcedure enc F, CleanInternalBridge K B) :
    ObserverRelativeUnprovability enc F := by
  intro B
  exact noClosure_of_cleanInternalBridge K B (Hclean B)

/-- The slogan version used in the paper text.

No absolute independence is claimed.  The result is method/observer-relative:
inside the selected `P`-observer bridge class, any closure must already expose
the frontier obstruction; hence clean internal bridge search cannot close the
boundary. -/
theorem godelLikeBridgeBarrierSchema
    {enc : SignedFormulaEncoding}
    (F : PObserverFrame enc)
    (K : PObserverBridgeBarrier enc F)
    (Hclean : forall B : InternalPBridgeProcedure enc F, CleanInternalBridge K B) :
    ObserverRelativeUnprovability enc F :=
  observerRelativeUnprovability_of_bridgeBarrier F K Hclean

/-! ## Kernel-only axiom trace -/

#print axioms observerRelativeUnprovability_of_noInternalClosure
#print axioms existsInternalClosure_of_not_observerRelativeUnprovability
#print axioms godelLikeObserverBoundarySchema
#print axioms noClosure_of_cleanInternalBridge
#print axioms exposesFrontierObstruction_of_closesBoundary
#print axioms observerRelativeUnprovability_of_bridgeBarrier
#print axioms godelLikeBridgeBarrierSchema

end PallLean.Paper93.DeepMath.PathB
