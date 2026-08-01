import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverLocalGodMoveRouteG
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPDynamicSPDPGlobalGodMove

/-!
# Dynamic SPDP instantiation of observer-local Route G

The repository already contains the operational ingredient needed to make the
observer in Route G dynamic: a positive SPDP event stream on one actual decision
run, its global accumulated rank, and a live boundary that accounts for every
prefix of that same stream.

This file instantiates `ObserverLocalGodMoveRouteG` with exactly that data.
The two compared objects are views of one run through one observer:

* the final live boundary; and
* the global positive-SPDP accumulation.

The local God-Move is explicit and has zero hidden overhead.  It changes the view
from final boundary to global accumulation while retaining the input.  Its rank
inequality is precisely the already-proved operational theorem
`globalGodMove_le_finalBoundary`.

This does **not** prove that SAT correctness emits an exponential global minor.
Moreover, the repository's calibration theorem proves that the older all-size
statement `SATCorrectnessFormsGlobalGodMove` is equivalent to the machine not
deciding SAT, so it is not a legitimate frontier to assume.  What is proved here
is only the local contradiction beam.  The final calibration theorem below makes
explicit that its collapse-relative exponential-emission premise is itself
equivalent to refuting collapse once a contradictory bounded profile is fixed.
-/

namespace PallLean.Paper93.DeepMath.PathB.DynamicSPDPObserverLocalRouteG

open PvsNPDynamicSPDPGlobalGodMove
open PvsNPRunIndexedFaithfulTPhi
open PvsNPBoundedLocalAccessCompiler
open ObserverLocalGodMoveRouteG

variable {Input State : Type*}

/-- The two observer-accessible views used by dynamic Route G. -/
inductive DynamicRankView
  | finalBoundary
  | globalGodMove
  deriving DecidableEq

/-- One observer frame on one actual run.  The input is retained in the object, so
the source and target selected from a collapse witness are measured by the same
dynamic observer at the same input. -/
def dynamicObserverFrame
    {R : ActualDecisionRun Input State}
    (O : DynamicBoundarySPDPObserver R) :
    ObserverFrame (Input × DynamicRankView) where
  accessibleRank p :=
    match p.2 with
    | .finalBoundary => O.boundaryRank R.steps p.1
    | .globalGodMove => O.spdp.globalGodMoveRank p.1

/-- The explicit dynamic local God-Move: retain the input and change from the
final-boundary view to the global-SPDP view.  The move has zero overhead because
the observer accounts for every positive SPDP prefix. -/
def dynamicLocalGodMove
    {R : ActualDecisionRun Input State}
    (O : DynamicBoundarySPDPObserver R) (x : Input) :
    LocalGodMove (dynamicObserverFrame O)
      (x, .finalBoundary) (x, .globalGodMove) 0 where
  transport p := (p.1, .globalGodMove)
  landsOnTarget := rfl
  rankOverhead := by
    simpa [dynamicObserverFrame] using O.globalGodMove_le_finalBoundary x

/-- Collapse-relative emission of a hard positive dynamic-SPDP minor.

For the intended application `Collapse` is `P = NP`; the witness must be derived
from the polynomial solver supplied by that assumption. -/
def CollapseEmitsDynamicMinor
    (Collapse : Prop)
    {R : ActualDecisionRun Input State}
    (O : DynamicBoundarySPDPObserver R) (n : ℕ) : Prop :=
  ∀ _h : Collapse, ∃ x : Input, 2 ^ n ≤ O.spdp.globalGodMoveRank x

/-- Build the abstract observer-local Route G data from a profile-bounded dynamic
observer and a collapse-relative emitted minor. -/
noncomputable def dynamicRouteGData
    (Collapse : Prop)
    {P : BoundedLocalAccessProfile} {n : ℕ}
    {R : ActualDecisionRun Input State}
    (G : ProfileBoundedDynamicGodMove P n R)
    (hminor : CollapseEmitsDynamicMinor Collapse G.observer n)
    (hgap : P.exposedRank n < 2 ^ n) :
    RouteGData Collapse where
  Obj := Input × DynamicRankView
  frame := dynamicObserverFrame G.observer
  source h := (Classical.choose (hminor h), DynamicRankView.finalBoundary)
  target h := (Classical.choose (hminor h), DynamicRankView.globalGodMove)
  sourceCap := P.exposedRank n
  targetFloor := 2 ^ n
  overhead := 0
  gap := by simpa using hgap
  insideLow h := by
    simpa [dynamicObserverFrame] using
      G.finalBoundary_le (Classical.choose (hminor h))
  buildLocalMove h := dynamicLocalGodMove G.observer (Classical.choose (hminor h))
  outsideHigh h := by
    simpa [dynamicObserverFrame] using Classical.choose_spec (hminor h)

/-- Dynamic observer-local Route G closure.

This is the exact contradiction beam for a dynamic SPDP observer.  The remaining
mathematical task is to prove `hminor` from the hypothetical polynomial SAT solver;
the local transport and same-observer accounting are now concrete and proved. -/
theorem dynamic_routeG_refutes_collapse
    (Collapse : Prop)
    {P : BoundedLocalAccessProfile} {n : ℕ}
    {R : ActualDecisionRun Input State}
    (G : ProfileBoundedDynamicGodMove P n R)
    (hminor : CollapseEmitsDynamicMinor Collapse G.observer n)
    (hgap : P.exposedRank n < 2 ^ n) :
    ¬ Collapse :=
  routeG_refutes_collapse (dynamicRouteGData Collapse G hminor hgap)

/-- Exact calibration of the fixed-profile exponential-emission socket.

Once `G` and an exponential gap are fixed, asking collapse to emit the forbidden
minor is logically equivalent to `¬ Collapse`: the forward direction is the Route G
contradiction and the reverse direction is vacuous.  Therefore this socket must not
be advertised as the missing constructive God-Move.  A viable replacement has to
state weaker local event-generation facts that do not already contradict the
profile by themselves. -/
theorem collapseEmitsDynamicMinor_iff_not_collapse
    (Collapse : Prop)
    {P : BoundedLocalAccessProfile} {n : ℕ}
    {R : ActualDecisionRun Input State}
    (G : ProfileBoundedDynamicGodMove P n R)
    (hgap : P.exposedRank n < 2 ^ n) :
    CollapseEmitsDynamicMinor Collapse G.observer n ↔ ¬ Collapse := by
  constructor
  · intro hminor
    exact dynamic_routeG_refutes_collapse Collapse G hminor hgap
  · intro hno h
    exact False.elim (hno h)

end PallLean.Paper93.DeepMath.PathB.DynamicSPDPObserverLocalRouteG

#print axioms PallLean.Paper93.DeepMath.PathB.DynamicSPDPObserverLocalRouteG.dynamicLocalGodMove
#print axioms PallLean.Paper93.DeepMath.PathB.DynamicSPDPObserverLocalRouteG.dynamic_routeG_refutes_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.DynamicSPDPObserverLocalRouteG.collapseEmitsDynamicMinor_iff_not_collapse
