import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNonLocalSemanticForce
import PallLean.Paper93.DeepMath.PathB.ObserverFrontierSpecification

/-!
# Observer frontier: concrete instantiation against the program's own objects

**STATUS: SPECIFICATION, NOT A PROOF.**  This file pins the abstract conservation
dilemma of `ObserverFrontierSpecification` onto the program's *actual* objects —
`NonLocalSemanticForce`, `SignedDTMDecidesSAT`, `CanonicalGodMoveBoundaryVisible`
— so the abstract statement is not floating: it is about this program.

Two honest connections are made:

1. The abstract conjecture `ObserverForce` *is* the program's `force` field
   (`observerForce_of_nonLocalSemanticForce`).
2. The abstract `conservation_dilemma`, instantiated at these objects, shows the
   program's own breakthrough object sits exactly on the dilemma: it is
   barrier-evading (non-constructive) iff it is separation-strength
   (`concrete_conservation_dilemma`).

As in the abstract file, the two load-bearing inputs are supplied as
*hypotheses* because neither is available:

* the **discharge** `force ⇒ separation` went through the rank sandwich, which is
  REFUTED (`theorem207Witness_uninhabitable`);
* `rr` is the cited Razborov–Rudich barrier.

Nothing here proves `P ≠ NP`.  A clean `#print axioms` is expected and is *not*
progress.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine
open ObserverFrontier

/-- The abstract `ObserverForce` conjecture, instantiated at the program's own
objects: a real `NonLocalSemanticForce` package yields the abstract observer
force for `SignedDTMDecidesSAT`, with boundary-visibility taken as
`Nonempty (CanonicalGodMoveBoundaryVisible …)`.  This shows the abstract
conjecture in `ObserverFrontierSpecification` *is* the program's `force` field. -/
theorem observerForce_of_nonLocalSemanticForce
    (enc : SignedFormulaEncoding) (H : NonLocalSemanticForce enc) :
    ObserverForce (SignedDTMDecidesSAT enc)
      (fun M => Nonempty (CanonicalGodMoveBoundaryVisible enc M)) :=
  fun M hM => ⟨H.force M hM⟩

/-- Concrete separation for an encoding: no signed SAT decider exists. -/
def ConcreteSeparation (enc : SignedFormulaEncoding) : Prop :=
  ¬ ∃ M : DTM, SignedDTMDecidesSAT enc M

/-- The concrete "useful invariant": the program's breakthrough object exists. -/
def ConcreteUseful (enc : SignedFormulaEncoding) : Prop :=
  Nonempty (NonLocalSemanticForce enc)

/-- **Concrete instantiation of the conservation dilemma** against the program's
own objects.

The two inputs are exactly the open / cited facts, supplied as hypotheses
because neither is available:

* `discharge : ConcreteUseful enc → ConcreteSeparation enc` — the force ⇒
  separation step, which in the program went through the rank sandwich and is
  therefore REFUTED (`theorem207Witness_uninhabitable`).  Assumed, not proved.
* `rr : Constructive → Large → ¬ ConcreteUseful enc` — the cited Razborov–Rudich
  barrier for this invariant.

Given a *useful*, *large* force invariant, the abstract `conservation_dilemma`
yields: the invariant is non-constructive (so it evades natural proofs) **and**
the separation holds (so establishing it is the whole problem).  The program's
own breakthrough object is pinned onto the dilemma: barrier-evading iff
separation-strength. -/
theorem concrete_conservation_dilemma
    (enc : SignedFormulaEncoding)
    (Constructive Large : Prop)
    (discharge : ConcreteUseful enc → ConcreteSeparation enc)
    (rr : Constructive → Large → ¬ ConcreteUseful enc)
    (hU : ConcreteUseful enc) (hL : Large) :
    ¬ Constructive ∧ ConcreteSeparation enc :=
  conservation_dilemma Constructive Large (ConcreteUseful enc)
    (ConcreteSeparation enc) discharge rr hU hL

end PallLean.Paper93.DeepMath.PathB

/-! ## Kernel-only axiom trace (clean = honesty, not progress) -/

#print axioms PallLean.Paper93.DeepMath.PathB.observerForce_of_nonLocalSemanticForce
#print axioms PallLean.Paper93.DeepMath.PathB.concrete_conservation_dilemma
