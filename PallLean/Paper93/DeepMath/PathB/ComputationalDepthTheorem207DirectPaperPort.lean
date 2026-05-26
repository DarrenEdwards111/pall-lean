import PallLean.Paper93.DeepMath.PathB.StrictDynamicNFrameLagrangianInvariant

/-!
# Direct paper-faithful Theorem 207 -> strict live-boundary port

This file encodes the strict Route-B port in a paper-first form (from the
`p vs np1` Theorem-207 semantic spine), without routing through the old static
same-object rank sandwich.

The hard edge is represented exactly where it belongs:

* NP-side lower bound on the extracted coupled-sheet rank, and
* a no-loss realization map from that extracted rank into the strict observer's
  live boundary rank on an actual trajectory state.

Once those two ingredients are supplied at paper scale, strict dynamic
extraction follows mechanically.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Direct per-observer paper witness at fixed length `n`.

This is the strict theorem payload needed from the paper Theorem-207 machinery:
`sheet_rank_lower` is the NP-side lower bound on the extracted target, and
`sheet_rank_le_liveBoundary` is the realization/no-loss bridge into the strict
observer trajectory boundary rank.
-/
structure Theorem207DirectPaperWitness
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (L : StrictDynamicNFrameLagrangianObserver enc) where
  input : Fin n -> Bool
  formula : ThreeCNF
  encoded : enc.Encodes input formula
  formula_satisfiable : formula.IsSatisfiable
  time : Nat
  state : Nat
  state_matches : state = L.toTrajectory.stateCode n input time
  nframe_lagrangian_payload : Prop
  nframe_lagrangian_payload_realized : nframe_lagrangian_payload
  pac_holographic_payload : Prop
  pac_holographic_payload_realized : pac_holographic_payload
  amplituhedron_payload : Prop
  amplituhedron_payload_realized : amplituhedron_payload
  extractedSheetRank : Nat
  sheet_rank_lower :
    Nat.choose (n / 3) (Nat.log 2 n) <= extractedSheetRank
  sheet_rank_le_liveBoundary :
    extractedSheetRank <= L.toTrajectory.liveBoundaryRank n input time

/-- A direct paper witness yields a strict live minor. -/
noncomputable def strictLiveMinor_of_theorem207DirectPaperWitness
    {enc : ThreeCNFEncoding}
    {n : Nat}
    {L : StrictDynamicNFrameLagrangianObserver enc}
    (W : Theorem207DirectPaperWitness enc n L) :
    StrictDynamicNFrameLagrangianLiveMinor enc L n where
  input := W.input
  formula := W.formula
  encoded := W.encoded
  formula_satisfiable := W.formula_satisfiable
  time := W.time
  state := W.state
  state_matches := W.state_matches
  liveActionRank := L.toTrajectory.liveBoundaryRank n W.input W.time
  nframe_lagrangian_payload := W.nframe_lagrangian_payload
  nframe_lagrangian_payload_realized := W.nframe_lagrangian_payload_realized
  pac_holographic_payload := W.pac_holographic_payload
  pac_holographic_payload_realized := W.pac_holographic_payload_realized
  amplituhedron_payload := W.amplituhedron_payload
  amplituhedron_payload_realized := W.amplituhedron_payload_realized
  liveActionRank_eq_boundary := rfl
  rank_lower := Nat.le_trans W.sheet_rank_lower W.sheet_rank_le_liveBoundary

/-- Direct paper theorem surface at fixed `n`: every strict SAT observer has a
Theorem-207 direct witness. -/
def Theorem207DirectPaperAt
    (enc : ThreeCNFEncoding)
    (n : Nat) : Prop :=
  forall L : StrictDynamicNFrameLagrangianObserver enc,
    Nonempty (Theorem207DirectPaperWitness enc n L)

/-- Direct paper theorem surface (exponent-parametric): this is the precise
port contract needed to derive strict dynamic extraction at paper scale. -/
def UniversalTheorem207DirectPaperPort
    (enc : ThreeCNFEncoding) : Prop :=
  forall c : Nat, exists n : Nat,
    n >= 2 ^ 20 /\
    4 * (c + 1) <= Nat.log 2 n /\
    Theorem207DirectPaperAt enc n

/-- Main port theorem: direct paper Theorem-207 contract implies the strict
live-boundary extraction theorem required by the new route. -/
theorem universalStrictDynamicNFrameLagrangianExtraction_of_directPaperPort
    (enc : ThreeCNFEncoding)
    (H : UniversalTheorem207DirectPaperPort enc) :
    UniversalStrictDynamicNFrameLagrangianExtraction enc := by
  intro c
  rcases H c with ⟨n, hn20, hlog, Hat⟩
  refine ⟨n, hn20, hlog, ?_⟩
  intro L
  rcases Hat L with ⟨W⟩
  exact ⟨strictLiveMinor_of_theorem207DirectPaperWitness W⟩

#print axioms strictLiveMinor_of_theorem207DirectPaperWitness
#print axioms universalStrictDynamicNFrameLagrangianExtraction_of_directPaperPort

end PallLean.Paper93.DeepMath.PathB
