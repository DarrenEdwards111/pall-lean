import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEntanglementInvariantCalibrationNoGo
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPDynamicTraceInvariantEquivalence
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTowerCompactRouteClosure
import PallLean.Paper93.DeepMath.PathB.CanonicalDynamicNFrameInvariant

/-!
# Dynamic entanglement endpoint: exact collapse to the SAT lower bound

The rank-calibration no-go leaves a tempting repair: make entanglement dynamic,
SAT-specific, and machine-sensitive.  The repository's trace-label invariant is
exactly such an object.  It attaches labels to a solver's full execution trace
and asks the projected boundary to preserve them on a hard residual family.

This file calibrates that repair against the recently closed compact-quotation
route.  For an unrestricted machine model, the following are equivalent:

* a dynamic trace-label invariant for every certified machine;
* a compact SAT liar compiler;
* uniform semantic answer feedback;
* a finite code-indexed diagonalizer;
* a Book 1 solver-indexed tower diagonalizer;
* `SATDecisionInP` is false.

The reverse construction for the dynamic invariant is the existing vacuous
one: once no SAT decider exists, `DecidesSAT` eliminates every invariant
obligation.  Thus dynamic entanglement has the right machine sensitivity but
does not independently manufacture its hard semantic-preservation field.

The other repair -- a canonical SAT-semantic N-frame rank -- is unconditional,
but its width is superpolynomial by construction, even in the presence of a SAT
decider.  It therefore fails the P-side calibration instead.

This closes the two currently formalized SAT-specific dynamic entanglement
implementations.  Nothing here proves `P != NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.EntanglementDynamicTraceEndpoint

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariant
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariantEquivalence
open PallLean.Paper93.DeepMath.PathB.NFrameTowerKleeneQuotationAudit
open PallLean.Paper93.DeepMath.PathB.NFrameTowerBoundedAnswerFeedbackNoGo
open PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverDiagonalizationFrontier
open PallLean.Paper93.DeepMath.PathB.NFrameGodelTowerSATBridgeAudit
open PallLean.Paper93.DeepMath.PathB.NFrameTowerCompactRouteClosure

/-! ## Dynamic trace and compact quotation are the same unrestricted endpoint -/

/-- Unrestricted dynamic trace-label invariance is equivalent to a compact SAT
liar compiler. -/
theorem dynamicTraceInvariant_iff_compactSATLiarCompiler
    (U : MachineModel) :
    Nonempty (DynamicTraceInvariantFromCorrectnessForAllMachines U) <->
      Nonempty (CompactSATLiarCompiler U) :=
  dynamicTraceInvariant_iff_no_SATDecisionInP.trans
    (compactSATLiarCompiler_iff_no_SATDecisionInP U).symm

/-- Dynamic trace-label invariance is equivalent to uniform semantic feedback. -/
theorem dynamicTraceInvariant_iff_uniformSemanticAnswerFeedback
    (U : MachineModel) :
    Nonempty (DynamicTraceInvariantFromCorrectnessForAllMachines U) <->
      Nonempty (UniformSemanticAnswerFeedback U) :=
  dynamicTraceInvariant_iff_no_SATDecisionInP.trans
    (uniformSemanticAnswerFeedback_iff_no_SATDecisionInP U).symm

/-- Dynamic trace-label invariance is equivalent to a finite code-indexed
counterexample family. -/
theorem dynamicTraceInvariant_iff_codeIndexedFiniteDiagonalizer
    (U : MachineModel) :
    Nonempty (DynamicTraceInvariantFromCorrectnessForAllMachines U) <->
      Nonempty (CodeIndexedFiniteDiagonalizer U) :=
  dynamicTraceInvariant_iff_no_SATDecisionInP.trans
    (codeIndexedFiniteDiagonalizer_iff_no_SATDecisionInP U).symm

/-- Adding the Book 1 tower escape to the finite diagonalizer does not change
the dynamic entanglement endpoint. -/
theorem dynamicTraceInvariant_iff_solverIndexedTowerDiagonalizer
    (U : MachineModel) (T : UniformRosserTower) :
    Nonempty (DynamicTraceInvariantFromCorrectnessForAllMachines U) <->
      Nonempty (SolverIndexedTowerDiagonalizer U T) :=
  dynamicTraceInvariant_iff_no_SATDecisionInP.trans
    (solverIndexedTowerDiagonalizer_iff_no_SATDecisionInP U T).symm

/-- The complete dynamic-entanglement equivalence line. -/
theorem dynamicEntanglement_exact_endpoint
    (U : MachineModel) (T : UniformRosserTower) :
    (Nonempty (DynamicTraceInvariantFromCorrectnessForAllMachines U) <->
      ¬ SATDecisionInP U) /\
    (Nonempty (DynamicTraceInvariantFromCorrectnessForAllMachines U) <->
      Nonempty (CompactSATLiarCompiler U)) /\
    (Nonempty (DynamicTraceInvariantFromCorrectnessForAllMachines U) <->
      Nonempty (CodeIndexedFiniteDiagonalizer U)) /\
    (Nonempty (DynamicTraceInvariantFromCorrectnessForAllMachines U) <->
      Nonempty (SolverIndexedTowerDiagonalizer U T)) := by
  exact ⟨dynamicTraceInvariant_iff_no_SATDecisionInP,
    dynamicTraceInvariant_iff_compactSATLiarCompiler U,
    dynamicTraceInvariant_iff_codeIndexedFiniteDiagonalizer U,
    dynamicTraceInvariant_iff_solverIndexedTowerDiagonalizer U T⟩

/-! ## The canonical semantic-rank alternative fails the opposite side -/

/-- The canonical SAT-semantic rank avoids representation dependence, but any
observer carrying it has non-polynomial width at every proposed exponent. -/
theorem canonicalSemanticRank_not_polyWidth
    {enc : ThreeCNFEncoding}
    (O : CanonicalDynamicNFrameObserver enc) (c : Nat) :
    Not (TrajectoryObserverHasPolyWidthExponent O.toTrajectory c) :=
  not_polyWidth_of_canonicalDynamicNFrameObserver O c

/-- This failure persists under an explicit SAT-decider witness: canonical
extraction remains available, but its saturated width is still non-polynomial.
The semantics has preloaded the hard scale rather than derived it from time. -/
theorem canonicalSemanticRank_decider_does_not_restore_calibration
    {enc : ThreeCNFEncoding}
    (hdec : exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M)
    (O : CanonicalDynamicNFrameObserver enc) (c : Nat) :
    UniversalCanonicalDynamicNFrameExtraction enc /\
      Not (TrajectoryObserverHasPolyWidthExponent O.toTrajectory c) :=
  ⟨universalCanonicalDynamicNFrameExtraction_of_decider hdec,
    not_polyWidth_of_canonicalDynamicNFrameObserver O c⟩

end PallLean.Paper93.DeepMath.PathB.EntanglementDynamicTraceEndpoint

#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementDynamicTraceEndpoint.dynamicTraceInvariant_iff_compactSATLiarCompiler
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementDynamicTraceEndpoint.dynamicTraceInvariant_iff_solverIndexedTowerDiagonalizer
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementDynamicTraceEndpoint.dynamicEntanglement_exact_endpoint
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementDynamicTraceEndpoint.canonicalSemanticRank_not_polyWidth
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementDynamicTraceEndpoint.canonicalSemanticRank_decider_does_not_restore_calibration
