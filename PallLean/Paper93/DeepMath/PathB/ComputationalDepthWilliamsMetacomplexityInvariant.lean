import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKtRouteTheorem

/-
# Williams/metacomplexity invariant route socket

This file packages the time-axis strategy in one place:

1. Assume shallow SAT search.
2. Derive a metacomplexity consequence (compression/algorithmic collapse).
3. Contradict an independent metacomplexity barrier theorem.
4. Conclude deep SAT search (hence no SAT decision in P in the canonical model).

It is intentionally a socket: the load-bearing ingredients are explicit fields.
-/

namespace SATDepthMachine

/-- Abstract consequence object produced from a shallow-search hypothesis. -/
structure WilliamsConsequence where
  payload : Prop

/-- A Williams/metacomplexity invariant package for one machine model. -/
structure WilliamsMetacomplexityInvariant
    (U : MachineModel) where
  consequence_of_shallow :
    ShallowSATSearch U -> WilliamsConsequence
  barrier :
    ∀ hshallow : ShallowSATSearch U,
      ¬ (consequence_of_shallow hshallow).payload
  consequence_sound :
    ∀ hshallow : ShallowSATSearch U,
      (consequence_of_shallow hshallow).payload

/-- The invariant discharges deep SAT search. -/
theorem deepSATSearch_of_williamsInvariant
    (U : MachineModel)
    (I : WilliamsMetacomplexityInvariant U) :
    DeepSATSearch U := by
  intro hshallow
  have hpayload : (I.consequence_of_shallow hshallow).payload :=
    I.consequence_sound hshallow
  exact (I.barrier hshallow) hpayload

/-- Canonical closure: Williams invariant implies no SAT decider in P. -/
theorem no_decider_of_williamsInvariant
    (C : CanonicalMachineSurface)
    (I : WilliamsMetacomplexityInvariant C.toMachineModel) :
    ¬ CanonicalSATDecisionInP C :=
  (canonicalDeepSATSearch_iff_no_decider C).mp
    (deepSATSearch_of_williamsInvariant C.toMachineModel I)

/-- For described canonical surfaces, a Williams invariant implies the route's
hard metacomplexity socket. -/
theorem hardSocket_of_williamsInvariant
    (D : DescribedCanonicalSurface)
    (I : WilliamsMetacomplexityInvariant D.surface.toMachineModel) :
    HardMetacomplexitySocket D :=
  (hardMetacomplexitySocket_iff_noCanonicalSATDecisionInP D).mpr
    (no_decider_of_williamsInvariant D.surface I)

/-- End-to-end closure statement mirroring the Kt route theorem surface. -/
theorem ktRoute_finalClosure_of_williamsInvariant
    (D : DescribedCanonicalSurface)
    (I : WilliamsMetacomplexityInvariant D.surface.toMachineModel) :
    (¬ CanonicalSATDecisionInP D.surface) ∧
      NoPolynomialLengthScheduledCompleteGenerators D := by
  exact ktRoute_finalClosure D (hardSocket_of_williamsInvariant D I)

/-! ## Axiom trace -/

#print axioms deepSATSearch_of_williamsInvariant
#print axioms no_decider_of_williamsInvariant
#print axioms hardSocket_of_williamsInvariant
#print axioms ktRoute_finalClosure_of_williamsInvariant

end SATDepthMachine
