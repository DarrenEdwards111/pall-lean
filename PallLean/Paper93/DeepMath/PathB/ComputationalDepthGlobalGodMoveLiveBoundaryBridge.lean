import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDegreeOrBoundaryStepA
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthConcreteExpansionPredicate

/-!
# Global God-Move bridge to live boundary rank (new infrastructure)

This module isolates the missing load-bearing edge in the corrected Route-B
pipeline: turning boundary/spectral certificates into a concrete lower bound on
`liveBoundaryRank`.

In this infrastructure the edge is represented by a uniform per-payload
certificate builder (`globalGodMove_liveMinorBuilder`) that supplies a concrete
expanded-boundary certificate.  Once that exists, the live-rank lower bound is
mechanical.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Target edge: at scale `n`, every concrete payload carries a certified
binomial lower bound in the live boundary rank. -/
def GlobalGodMoveLiveBoundaryRankLowerBoundAtScale
    (enc : ThreeCNFEncoding)
    (n : Nat) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ W : DynamicMinorPreAmplificationWitness enc L n,
      Nat.choose (n / 3) (Nat.log 2 n) <=
        L.toTrajectory.liveBoundaryRank n W.input W.time

/-- Assumption package for the corrected God-Move bridge.

* `stepA_boundary_floor`: corrected Step-A polarity (growth from boundary side).
* `globalGodMove_liveMinorBuilder`: the actual missing transport edge, stated as
  a uniform concrete expansion certificate builder.
-/
structure GlobalGodMoveLiveBoundaryBridgeAssumptions
    (enc : ThreeCNFEncoding)
    (n : Nat) : Prop where
  stepA_boundary_floor : DegreeOrBoundaryExpansionFloorAtScale enc n
  globalGodMove_liveMinorBuilder :
    ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ W : DynamicMinorPreAmplificationWitness enc L n,
      ConcreteRamanujanAmplituhedronExpansionPredicate enc n L W

/-- The missing edge itself: concrete God-Move live-minor certificates imply
uniform live-boundary-rank lower bound. -/
theorem globalGodMove_liveBoundaryRankLowerBound_of_liveMinorBuilder
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (H :
      ∀ L : DynamicNFrameLagrangianObserver enc,
      ∀ W : DynamicMinorPreAmplificationWitness enc L n,
        ConcreteRamanujanAmplituhedronExpansionPredicate enc n L W) :
    GlobalGodMoveLiveBoundaryRankLowerBoundAtScale enc n := by
  intro L W
  exact rankLower_of_concreteRamanujanAmplituhedronExpansion (H L W)

/-- Packaged corrected Global God-Move bridge theorem in the new
infrastructure.  Step-A boundary floor is kept explicitly in the package for
route-level wiring/audits; the rank lower bound comes from the concrete
live-minor builder. -/
theorem globalGodMove_liveBoundaryRankBridge
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (A : GlobalGodMoveLiveBoundaryBridgeAssumptions enc n) :
    GlobalGodMoveLiveBoundaryRankLowerBoundAtScale enc n :=
  globalGodMove_liveBoundaryRankLowerBound_of_liveMinorBuilder enc n
    A.globalGodMove_liveMinorBuilder

#print axioms globalGodMove_liveBoundaryRankLowerBound_of_liveMinorBuilder
#print axioms globalGodMove_liveBoundaryRankBridge

end PallLean.Paper93.DeepMath.PathB
