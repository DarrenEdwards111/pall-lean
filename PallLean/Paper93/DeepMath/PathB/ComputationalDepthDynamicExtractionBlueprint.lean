import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDynamicExtractionEngine

/-!
# Dynamic extraction blueprint decomposition

This file splits the hardest engine field (`extract_minor`) into a lighter
"core witness" object that avoids duplicated bookkeeping equations.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Minimal constructive data needed to build a
`DynamicNFrameLagrangianLiveMinor` at fixed `n`.

`state` and `liveActionRank` are reconstructed canonically from the trajectory,
so core construction work focuses on the SAT/geometry/rank ingredients. -/
structure DynamicMinorCoreWitness
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
  rank_lower :
    Nat.choose (n / 3) (Nat.log 2 n) <=
      L.toTrajectory.liveBoundaryRank n input time

/-- Canonical promotion from core witness to full live minor. -/
noncomputable def DynamicMinorCoreWitness.toLiveMinor
    {enc : ThreeCNFEncoding}
    {L : DynamicNFrameLagrangianObserver enc}
    {n : Nat}
    (W : DynamicMinorCoreWitness enc L n) :
    DynamicNFrameLagrangianLiveMinor enc L n where
  input := W.input
  formula := W.formula
  encoded := W.encoded
  formula_satisfiable := W.formula_satisfiable
  time := W.time
  state := L.toTrajectory.stateCode n W.input W.time
  state_matches := rfl
  liveActionRank := L.toTrajectory.liveBoundaryRank n W.input W.time
  nframe_lagrangian_payload := W.nframe_lagrangian_payload
  nframe_lagrangian_payload_realized := W.nframe_lagrangian_payload_realized
  pac_holographic_payload := W.pac_holographic_payload
  pac_holographic_payload_realized := W.pac_holographic_payload_realized
  amplituhedron_payload := W.amplituhedron_payload
  amplituhedron_payload_realized := W.amplituhedron_payload_realized
  liveActionRank_eq_boundary := rfl
  rank_lower := W.rank_lower

/-- Core-engine variant: prove bounds on the canonical boundary rank plus
payload realizers; full minors are reconstructed automatically. -/
structure DynamicNFrameLagrangianCoreExtractionEngine
    (enc : ThreeCNFEncoding) where
  lengthForExponent : Nat -> Nat
  length_large : ∀ c : Nat, lengthForExponent c >= 2 ^ 20
  length_log : ∀ c : Nat, 4 * (c + 1) <= Nat.log 2 (lengthForExponent c)
  extract_core :
    ∀ c : Nat,
      ∀ L : DynamicNFrameLagrangianObserver enc,
        DynamicMinorCoreWitness enc L (lengthForExponent c)

/-- Any core engine upgrades to the full extraction engine. -/
noncomputable def DynamicNFrameLagrangianCoreExtractionEngine.toExtractionEngine
    {enc : ThreeCNFEncoding}
    (E : DynamicNFrameLagrangianCoreExtractionEngine enc) :
    DynamicNFrameLagrangianExtractionEngine enc where
  lengthForExponent := E.lengthForExponent
  length_large := E.length_large
  length_log := E.length_log
  extract_minor := by
    intro c L
    exact (E.extract_core c L).toLiveMinor

/-- Therefore any core engine proves universal dynamic extraction. -/
theorem universalDynamicExtraction_of_coreEngine
    (enc : ThreeCNFEncoding)
    (E : DynamicNFrameLagrangianCoreExtractionEngine enc) :
    UniversalDynamicNFrameLagrangianExtraction enc :=
  universalDynamicExtraction_of_engine enc E.toExtractionEngine

/-! ## Axiom trace -/

#print axioms DynamicMinorCoreWitness.toLiveMinor
#print axioms DynamicNFrameLagrangianCoreExtractionEngine.toExtractionEngine
#print axioms universalDynamicExtraction_of_coreEngine

end PallLean.Paper93.DeepMath.PathB
