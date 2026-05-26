import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTheorem207DirectPaperPort
import PallLean.GlobalGodMoveGauge
import PallLean.MultilinearSPDP

/-!
# Legacy same-sheet SPDP port for Theorem 207

This module contains the older same-sheet SPDP realization bridge.  It is kept
for auditing the legacy Theorem-207 route, but it is intentionally split away
from `ComputationalDepthTheorem207DirectPaperPort` and the strict Book-1 final
route.

Consequence: importing `ComputationalDepthTheorem207StrictPort` no longer
imports `GlobalGodMoveGauge` through the direct-port layer.  The unresolved
semantic transport seam in `GlobalGodMoveGauge` is therefore retired from the
final strict Book-1 obstruction route, while remaining available for legacy
analysis here.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Direct paper realization package using the paper's named same-sheet target
at fixed scale `n`, plus a strict trajectory no-loss map into live boundary
rank.  This is the legacy SPDP same-sheet interface, not part of the final
strict Book-1 obstruction route. -/
structure Theorem207SameSheetStrictRealization
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (L : StrictDynamicNFrameLagrangianObserver enc) where
  hn804 : n >= 2 ^ 804
  hn2 : n >= 2
  htb : L.M.timeBound <= 4
  hns : L.M.numStates <= n
  hdec : DecidesSAT L.M
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
  same_sheet_rank_le_liveBoundary :
    MultilinearSPDP.mlBlockedSpdpRank
      (cook_levin_compilation L.M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (GlobalGodMoveGauge.theorem207_same_sheet_poly
        L.M n hn804 hn2 htb hns hdec) <=
      L.toTrajectory.liveBoundaryRank n input time

/-- A same-sheet strict realization yields a direct paper witness by
instantiating `extractedSheetRank` with the paper's named same-sheet SPDP rank
object and using the paper Theorem-207 NP-side lower bound on that same object.
-/
noncomputable def directPaperWitness_of_sameSheetStrictRealization
    {enc : ThreeCNFEncoding}
    {n : Nat}
    {L : StrictDynamicNFrameLagrangianObserver enc}
    (R : Theorem207SameSheetStrictRealization enc n L) :
    Theorem207DirectPaperWitness enc n L := by
  refine
    { input := R.input
      formula := R.formula
      encoded := R.encoded
      formula_satisfiable := R.formula_satisfiable
      time := R.time
      state := R.state
      state_matches := R.state_matches
      nframe_lagrangian_payload := R.nframe_lagrangian_payload
      nframe_lagrangian_payload_realized :=
        R.nframe_lagrangian_payload_realized
      pac_holographic_payload := R.pac_holographic_payload
      pac_holographic_payload_realized := R.pac_holographic_payload_realized
      amplituhedron_payload := R.amplituhedron_payload
      amplituhedron_payload_realized := R.amplituhedron_payload_realized
      extractedSheetRank :=
        MultilinearSPDP.mlBlockedSpdpRank
          (cook_levin_compilation L.M n R.hn2 R.htb R.hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (GlobalGodMoveGauge.theorem207_same_sheet_poly
            L.M n R.hn804 R.hn2 R.htb R.hns R.hdec)
      sheet_rank_lower :=
        GlobalGodMoveGauge.theorem207_same_sheet_np_side_lower_bound
          L.M n R.hn804 R.hn2 R.htb R.hns R.hdec
      sheet_rank_le_liveBoundary := R.same_sheet_rank_le_liveBoundary }

/-- Paper-first legacy scale discharge contract:
for each exponent, choose a paper-scale length where every strict observer has
a same-sheet strict realization. -/
def UniversalTheorem207SameSheetStrictRealization
    (enc : ThreeCNFEncoding) : Prop :=
  forall c : Nat, exists n : Nat,
    n >= 2 ^ 20 /\
    4 * (c + 1) <= Nat.log 2 n /\
    (forall L : StrictDynamicNFrameLagrangianObserver enc,
      Nonempty (Theorem207SameSheetStrictRealization enc n L))

/-- If the legacy same-sheet strict realization contract is discharged, then
the full direct paper port contract follows. -/
theorem universalDirectPaperPort_of_sameSheetStrictRealization
    (enc : ThreeCNFEncoding)
    (H : UniversalTheorem207SameSheetStrictRealization enc) :
    UniversalTheorem207DirectPaperPort enc := by
  intro c
  rcases H c with ⟨n, hn20, hlog, hreal⟩
  refine ⟨n, hn20, hlog, ?_⟩
  intro L
  rcases hreal L with ⟨R⟩
  exact ⟨directPaperWitness_of_sameSheetStrictRealization R⟩

#print axioms directPaperWitness_of_sameSheetStrictRealization
#print axioms universalDirectPaperPort_of_sameSheetStrictRealization

end PallLean.Paper93.DeepMath.PathB
