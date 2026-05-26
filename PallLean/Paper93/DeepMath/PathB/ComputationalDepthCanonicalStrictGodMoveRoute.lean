import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTheorem207DirectPaperPort
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTheorem207StrictPort

/-!
# Canonical strict God-Move route (restricted class)

This module defines a canonical restricted strict observer class with built-in
polynomial capacity and proves an unconditional no-decider endpoint for that
class from a matching canonical strict port theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Canonical strict SAT observer class used for the restricted unconditional
route: strict observer + low-action polynomial live-boundary capacity. -/
abbrev CanonicalStrictGodMoveSATObserver
    (enc : ThreeCNFEncoding) :=
  LowActionStrictDynamicNFrameLagrangianObserver enc

/-- Canonical strict no-decider statement (restricted model). -/
def NoCanonicalStrictGodMoveSATDecider
    (enc : ThreeCNFEncoding) : Prop :=
  Not (Nonempty (CanonicalStrictGodMoveSATObserver enc))

/-- Canonical strict port theorem shape for the restricted class.
For each calibration exponent `c`, there is a paper-scale `n` where every
canonical strict observer of degree `k <= c` has a direct-paper witness. -/
def CanonicalStrictGodMovePort
    (enc : ThreeCNFEncoding) : Prop :=
  forall c : Nat, exists n : Nat,
    n >= 2 ^ 20 /\
    4 * (c + 1) <= Nat.log 2 n /\
    forall L : CanonicalStrictGodMoveSATObserver enc,
      L.k <= c ->
      Nonempty (Theorem207DirectPaperWitness enc n L.base)

/-- Canonical strict port implies no canonical strict SAT decider.
This is unconditional in the restricted canonical class. -/
theorem noCanonicalStrictGodMoveSATDecider_of_canonicalStrictGodMovePort
    (enc : ThreeCNFEncoding)
    (Hport : CanonicalStrictGodMovePort enc) :
    NoCanonicalStrictGodMoveSATDecider enc := by
  intro hnonempty
  rcases hnonempty with ⟨L⟩
  rcases Hport L.k with ⟨n, hn20, hlog, Hn⟩
  rcases Hn L (Nat.le_refl L.k) with ⟨W⟩
  have hlower :
      Nat.choose (n / 3) (Nat.log 2 n) <=
        L.base.toTrajectory.liveBoundaryRank n W.input W.time :=
    liveBoundary_lower_of_theorem207DirectPaperWitness W
  have hupper :
      L.base.toTrajectory.liveBoundaryRank n W.input W.time <
        Nat.choose (n / 3) (Nat.log 2 n) :=
    lowAction_book1BoundaryObstruction L (Nat.le_refl L.k) hn20 hlog W.input W.time
  exact (Nat.not_le_of_lt hupper) hlower

/-- Standard-bridge packaging for the restricted canonical route.
This is the analogue of the strict-port standard bridge but for the canonical
restricted class endpoint. -/
structure CanonicalStrictStandardBridge
    (enc : ThreeCNFEncoding) where
  standardPvsNP : Prop
  standardPvsNP_iff_no_canonical_strict_decider :
    standardPvsNP ↔ NoCanonicalStrictGodMoveSATDecider enc

/-- If the canonical strict port is proved, then the bridged standard statement
follows for the restricted canonical model. -/
theorem standardPvsNP_of_canonicalStrictGodMovePort
    {enc : ThreeCNFEncoding}
    (B : CanonicalStrictStandardBridge enc)
    (Hport : CanonicalStrictGodMovePort enc) :
    B.standardPvsNP :=
  (B.standardPvsNP_iff_no_canonical_strict_decider).mpr
    (noCanonicalStrictGodMoveSATDecider_of_canonicalStrictGodMovePort enc Hport)

#print axioms noCanonicalStrictGodMoveSATDecider_of_canonicalStrictGodMovePort
#print axioms standardPvsNP_of_canonicalStrictGodMovePort

end PallLean.Paper93.DeepMath.PathB
