import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPPACAmplituhedronProjection

/-!
# Dynamic H4 bridge equivalence audit

`ComputationalDepthPvsNPDynamicH4Theorem.lean` proved the useful forward direction:

```text
DynamicH4ForPTimeSAT U -> ¬ SATDecisionInP U.
```

Here `DynamicH4ForPTimeSAT U` is a data-producing `Type 1`, not a `Prop`, so the exact logical audit is about
inhabitation:

```lean
Nonempty (DynamicH4ForPTimeSAT U) ↔ ¬ SATDecisionInP U
```

The reverse direction is vacuity.  Because `DynamicH4ForPTimeSAT U` is stated as

```lean
∀ (D : DecisionMachine U), DecidesSAT U D → DynamicH4Witness
```

it is inhabited when no SAT decider exists: any alleged decider contradicts the no-decider hypothesis, and from that
contradiction we can produce the requested witness.

This is not bad news: it is the clean audit result.  It means the current exact bridge has isolated the theorem, but
proving it cannot be easier than proving `SAT ∉ P` itself unless the definition is refined to expose additional
constructive content.
-/


namespace PallLean.Paper93.DeepMath.PathB.PvsNPDynamicH4Equivalence

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicH4Theorem

/-- If SAT has no polynomial-time decider in the abstract machine model, then the current `DynamicH4ForPTimeSAT` bridge
is inhabited vacuously: any alleged decider contradicts the no-decider hypothesis, and from that contradiction we can
produce the requested witness. -/
def DynamicH4ForPTimeSAT_of_no_SATDecisionInP {U : MachineModel}
    (hNo : ¬ SATDecisionInP U) :
    DynamicH4ForPTimeSAT U := by
  intro D hD
  exact False.elim (hNo ⟨D, hD⟩)

/-- The current dynamic-H4 bridge is exactly equivalent, at the level of inhabitation, to the target lower bound.  The
forward implication is the previously proved dynamic-H4 theorem; the reverse implication is vacuity. -/
theorem nonempty_dynamicH4ForPTimeSAT_iff_no_SATDecisionInP {U : MachineModel} :
    Nonempty (DynamicH4ForPTimeSAT U) ↔ ¬ SATDecisionInP U := by
  constructor
  · intro hH4
    rcases hH4 with ⟨h⟩
    exact no_SATDecisionInP_of_DynamicH4 h
  · intro hNo
    exact ⟨DynamicH4ForPTimeSAT_of_no_SATDecisionInP hNo⟩

/-- Contrapositive audit form: under the current definition, non-inhabitation of dynamic H4 is the same as exhibiting a
SAT decider. -/
theorem not_nonempty_dynamicH4ForPTimeSAT_iff_SATDecisionInP {U : MachineModel} :
    ¬ Nonempty (DynamicH4ForPTimeSAT U) ↔ SATDecisionInP U := by
  constructor
  · intro hnot
    by_contra hNo
    exact hnot ⟨DynamicH4ForPTimeSAT_of_no_SATDecisionInP hNo⟩
  · intro hP hH4
    rcases hH4 with ⟨h⟩
    exact no_SATDecisionInP_of_DynamicH4 h hP

/-!
Consequence for the route:

The already-proved dynamic transcript/fooling machinery is sound, but the named bridge
`DynamicH4ForPTimeSAT` is too extensional: its inhabitation is theorem-equivalent to `¬ SATDecisionInP`.  A non-circular
next theorem must replace it with a more structured extraction statement, for example one that explicitly constructs the
residual family, transcript observer, decoder/projection, and polynomial boundary from a concrete solver model before
deriving the contradiction.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPDynamicH4Equivalence

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicH4Equivalence.DynamicH4ForPTimeSAT_of_no_SATDecisionInP
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicH4Equivalence.nonempty_dynamicH4ForPTimeSAT_iff_no_SATDecisionInP
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicH4Equivalence.not_nonempty_dynamicH4ForPTimeSAT_iff_SATDecisionInP
