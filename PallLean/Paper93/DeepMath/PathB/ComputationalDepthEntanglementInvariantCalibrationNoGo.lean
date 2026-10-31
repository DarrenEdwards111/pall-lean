import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEntanglementRouteClosure
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEntanglementCertificate
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverInvariantCorridor
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthOrderedMPSBond

/-!
# Entanglement invariant calibration no-go

`ComputationalDepthEntanglementRouteClosure` isolated the surviving target: an
entanglement invariant that is both controlled by every correct machine's time
and superpolynomial on every correct SAT decider.  The strongest tensor results
in the repository already remove fixed variable orderings, so the next question
is whether a representation-independent rank profile can supply that invariant.

This file gives the negative calibration test.

The tensor lower bounds are residual/subfunction-rank lower bounds.  But the
repository's explicit `dIndexLang` is in `P` while its representation-independent
subfunction profile is not polynomially bounded.  Therefore no observer
invariant that is sound on every polynomial-time language can dominate this
rank profile on every implementation.  Quantifying over all tensor cuts or all
MPS orderings removes layout dependence inside that representation class; it
does not turn function rank into a lower bound on arbitrary machine time.

There are consequently only two honest survivors:

* use structural non-separability directly, in which case an entanglement
  certificate exists exactly when there is no flattening -- the certificate is
  the desired lower bound;
* construct a SAT-specific intrinsic flow satisfying time calibration and
  hardness, in which case the package already proves `P != NP`.

Nothing here proves the missing SAT-specific invariant.
-/

namespace PallLean.Paper93.DeepMath.PathB.EntanglementInvariantCalibrationNoGo

open PallLean.Paper93.DeepMath.PathB.ComposableMachine (Machine Decides)
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)
open PallLean.Paper93.DeepMath.PathB.LangRankKill
  (subfunProfile dIndexLang subfunProfile_dIndex_not_polyBounded)
open PallLean.Paper93.DeepMath.PathB.DIndexMachine (dIndexInP)
open PallLean.Paper93.DeepMath.PathB.ObserverInvariantCorridor
open PallLean.Paper93.DeepMath.PathB.ObserverInvariantBridge
open PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics
open PallLean.Paper93.DeepMath.PathB.EntanglementCertificate
open PallLean.Paper93.DeepMath.PathB.EntanglementRouteClosure

/-! ## Universal rank calibration is impossible -/

/-- Domination of the representation-independent subfunction/rank profile on
every implementation of the explicit easy language `dIndexLang`. -/
def DominatesDIndexRank (Inv : Machine -> Nat -> Nat) : Prop :=
  forall (M : Machine) (T : Nat -> Nat), Decides M dIndexLang T ->
    forall n, subfunProfile dIndexLang n <= Inv M n

/-- A proposed universal entanglement observer: time-sound on every language
and strong enough to dominate the residual-rank profile. -/
structure UniversalRankEntanglementObserver where
  inv : Machine -> Nat -> Nat
  sound : ObserverSound inv
  dominatesRank : DominatesDIndexRank inv

/-- No universal time-sound observer can dominate representation-independent
subfunction rank.  The contradiction is witnessed by `dIndexLang in P`, not by
an unproved complexity assumption. -/
theorem no_universalRankEntanglementObserver :
    ¬ Nonempty UniversalRankEntanglementObserver := by
  rintro ⟨E⟩
  exact no_sound_observer_dominates_subfun E.inv E.sound E.dominatesRank

/-- Pointwise form of the same calibration wall. -/
theorem sound_entanglement_cannot_dominate_rank
    (Inv : Machine -> Nat -> Nat) (hsound : ObserverSound Inv) :
    ¬ DominatesDIndexRank Inv :=
  no_sound_observer_dominates_subfun Inv hsound

/-! ## Structural entanglement is exactly the batch lower bound -/

/-- A genuine non-separability certificate is equivalent to absence of batch
flattening.  Naming the certificate "entanglement" does not create the
superadditive inequality; it packages that inequality. -/
theorem structural_entanglement_iff_no_flattening
    (batch : Nat -> Nat) (single : Nat) :
    Nonempty (Entangled batch single) <->
      (forall k, k * single <= batch k) :=
  entanglement_iff_no_flattening batch single

/-! ## Exact surviving corridor -/

/-- The complete calibration verdict.  Universal domination of the available
rank profile is impossible, while a SAT-specific intrinsic package with
Cook--Levin proves the class separation.  Hence the gap between the two clauses
is precisely the missing machine-calibrated SAT entanglement invariant. -/
theorem entanglement_calibration_frontier
    (Inv : Machine -> Nat -> Nat) (hsound : ObserverSound Inv) :
    (¬ DominatesDIndexRank Inv) /\
      (forall (SATV : NPObs),
        IntrinsicEntanglementPackage SATV -> CookLevin SATV -> ¬ PeqNP) := by
  refine ⟨sound_entanglement_cannot_dominate_rank Inv hsound, ?_⟩
  intro SATV E hCL
  exact PneqNP_of_intrinsicEntanglement E hCL

end PallLean.Paper93.DeepMath.PathB.EntanglementInvariantCalibrationNoGo

#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementInvariantCalibrationNoGo.no_universalRankEntanglementObserver
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementInvariantCalibrationNoGo.sound_entanglement_cannot_dominate_rank
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementInvariantCalibrationNoGo.structural_entanglement_iff_no_flattening
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementInvariantCalibrationNoGo.entanglement_calibration_frontier
