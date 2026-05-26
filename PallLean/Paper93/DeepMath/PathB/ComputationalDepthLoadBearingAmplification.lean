import PallLean.Paper93.DeepMath.PathB.ComputationalDepthThresholdUpgradeDecomposition
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDynamicExtractionBlueprint

/-!
# Load-bearing amplification interface

This file fixes the non-load-bearing issue by introducing a lighter
pre-amplification witness (no binomial rank lower bound) and deriving the
existing local amplification socket from a genuine upgrade theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Pre-amplification witness: same SAT/encoding/payload data as core witness,
but with no binomial `rank_lower` field. -/
structure DynamicMinorPreAmplificationWitness
    (enc : ThreeCNFEncoding)
    (L : DynamicNFrameLagrangianObserver enc)
    (n : Nat) where
  input : Fin n -> Bool
  formula : ThreeCNF
  encoded : enc.Encodes input formula
  formula_satisfiable : formula.IsSatisfiable
  time : Nat
  nframe_lagrangian_payload : Prop
  nframe_lagrangian_payload_realized : nframe_lagrangian_payload
  pac_holographic_payload : Prop
  pac_holographic_payload_realized : pac_holographic_payload
  amplituhedron_payload : Prop
  amplituhedron_payload_realized : amplituhedron_payload

/-- Forgetful map from core witness to pre-amplification witness. -/
def DynamicMinorCoreWitness.toPre
    {enc : ThreeCNFEncoding}
    {L : DynamicNFrameLagrangianObserver enc}
    {n : Nat}
    (W : DynamicMinorCoreWitness enc L n) :
    DynamicMinorPreAmplificationWitness enc L n where
  input := W.input
  formula := W.formula
  encoded := W.encoded
  formula_satisfiable := W.formula_satisfiable
  time := W.time
  nframe_lagrangian_payload := W.nframe_lagrangian_payload
  nframe_lagrangian_payload_realized := W.nframe_lagrangian_payload_realized
  pac_holographic_payload := W.pac_holographic_payload
  pac_holographic_payload_realized := W.pac_holographic_payload_realized
  amplituhedron_payload := W.amplituhedron_payload
  amplituhedron_payload_realized := W.amplituhedron_payload_realized

/-- Upgrade a pre-amplification witness to a core witness once rank
amplification is proved. -/
def DynamicMinorPreAmplificationWitness.toCore
    {enc : ThreeCNFEncoding}
    {L : DynamicNFrameLagrangianObserver enc}
    {n : Nat}
    (W : DynamicMinorPreAmplificationWitness enc L n)
    (hRank :
      Nat.choose (n / 3) (Nat.log 2 n) <=
        L.toTrajectory.liveBoundaryRank n W.input W.time) :
    DynamicMinorCoreWitness enc L n where
  input := W.input
  formula := W.formula
  encoded := W.encoded
  formula_satisfiable := W.formula_satisfiable
  time := W.time
  nframe_lagrangian_payload := W.nframe_lagrangian_payload
  nframe_lagrangian_payload_realized := W.nframe_lagrangian_payload_realized
  pac_holographic_payload := W.pac_holographic_payload
  pac_holographic_payload_realized := W.pac_holographic_payload_realized
  amplituhedron_payload := W.amplituhedron_payload
  amplituhedron_payload_realized := W.amplituhedron_payload_realized
  rank_lower := hRank

/-- Local constructor socket at pre-amplification level. -/
def ThresholdLocalPreCandidateBuilder
    (enc : ThreeCNFEncoding) (n : Nat) : Type :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    (∃ W : DynamicMinorPreAmplificationWitness enc L n,
      0 < L.toTrajectory.liveBoundaryRank n W.input W.time) ->
      DynamicMinorPreAmplificationWitness enc L n

/-- Load-bearing local amplification socket at pre-amplification level. -/
def ThresholdLocalRankAmplificationPre
    (enc : ThreeCNFEncoding) (n : Nat)
    (buildPre : ThresholdLocalPreCandidateBuilder enc n) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ hthPre :
      (∃ W : DynamicMinorPreAmplificationWitness enc L n,
        0 < L.toTrajectory.liveBoundaryRank n W.input W.time),
      Nat.choose (n / 3) (Nat.log 2 n) <=
        L.toTrajectory.liveBoundaryRank n
          (buildPre L hthPre).input (buildPre L hthPre).time

/-- Any core-threshold witness yields a pre-threshold witness (forget rank). -/
theorem preThreshold_of_coreThreshold
    {enc : ThreeCNFEncoding}
    {L : DynamicNFrameLagrangianObserver enc}
    {n : Nat}
    (hth :
      ∃ W : DynamicMinorCoreWitness enc L n,
        0 < L.toTrajectory.liveBoundaryRank n W.input W.time) :
    ∃ W : DynamicMinorPreAmplificationWitness enc L n,
      0 < L.toTrajectory.liveBoundaryRank n W.input W.time := by
  rcases hth with ⟨W, hpos⟩
  exact ⟨W.toPre, by simpa using hpos⟩

/-- Build a core-level candidate builder from a pre-level builder and a
load-bearing pre-level amplification theorem. -/
noncomputable def thresholdLocalCandidateBuilder_fromPre
    (enc : ThreeCNFEncoding) (n : Nat)
    (buildPre : ThresholdLocalPreCandidateBuilder enc n)
    (hamplifyPre : ThresholdLocalRankAmplificationPre enc n buildPre) :
    ThresholdLocalCandidateBuilder enc n := by
  intro L hthCore
  let hthPre := preThreshold_of_coreThreshold hthCore
  let Wpre := buildPre L hthPre
  have hRank := hamplifyPre L hthPre
  exact Wpre.toCore hRank

/-- The induced core-level builder satisfies the existing local amplification
socket, and this proof is now genuinely load-bearing via `hamplifyPre`. -/
theorem thresholdLocalRankAmplification_of_preAmplification
    (enc : ThreeCNFEncoding) (n : Nat)
    (buildPre : ThresholdLocalPreCandidateBuilder enc n)
    (hamplifyPre : ThresholdLocalRankAmplificationPre enc n buildPre) :
    ThresholdLocalRankAmplification
      enc n
      (thresholdLocalCandidateBuilder_fromPre enc n buildPre hamplifyPre) := by
  intro L hthCore
  let hthPre := preThreshold_of_coreThreshold hthCore
  have hRank :
      Nat.choose (n / 3) (Nat.log 2 n) <=
        L.toTrajectory.liveBoundaryRank n
          (buildPre L hthPre).input (buildPre L hthPre).time :=
    hamplifyPre L hthPre
  simpa [thresholdLocalCandidateBuilder_fromPre, hthPre]

/-! ## Axiom trace -/

#print axioms preThreshold_of_coreThreshold
#print axioms thresholdLocalCandidateBuilder_fromPre
#print axioms thresholdLocalRankAmplification_of_preAmplification

end PallLean.Paper93.DeepMath.PathB
