import PallLean.Paper93.DeepMath.PathB.ObserverTrajectoryDCEW

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

private def encodeBitsAt : Nat → List Bool → Nat
  | _, [] => 0
  | i, b :: bs => (if b then 2 ^ i else 0) + encodeBitsAt (i + 1) bs

noncomputable def strictConfigCode
    (M : TuringMachine.DTM) {tapeLen : Nat}
    (cfg : TuringMachine.Configuration M tapeLen) : Nat :=
  let tapeBits : List Bool := List.ofFn cfg.tape
  let tapeCode : Nat := encodeBitsAt 0 tapeBits
  cfg.state.val + M.numStates * (cfg.headPos.val + tapeLen * tapeCode)

noncomputable def StrictStateRankAt
    (M : TuringMachine.DTM) (configContextRank : Nat -> Nat)
    (n : Nat) (input : Fin n -> Bool) (t : Nat) : Nat :=
  if hn : n >= 1 then
    if ht : t < TuringMachine.timeSteps M n + 1 then
      let cfg := TuringMachine.run M n t (TuringMachine.initialConfig M n hn input)
      configContextRank (strictConfigCode M cfg)
    else
      0
  else
    0

noncomputable def strictRankAtFin
    (M : TuringMachine.DTM) (configContextRank : Nat -> Nat)
    (n : Nat) (hn : n >= 1) (input : Fin n -> Bool)
    (t : Fin (TuringMachine.timeSteps M n + 1)) : Nat :=
  let cfg := TuringMachine.run M n t.val (TuringMachine.initialConfig M n hn input)
  configContextRank (strictConfigCode M cfg)

noncomputable def StrictTrajectoryWidth
    (M : TuringMachine.DTM) (configContextRank : Nat -> Nat) :
    DynamicCEW.ObserverWidth :=
  fun n =>
    if hn : n >= 1 then
      Finset.univ.sup (fun input : Fin n -> Bool =>
        Finset.univ.sup (fun t : Fin (TuringMachine.timeSteps M n + 1) =>
          strictRankAtFin M configContextRank n hn input t))
    else
      0

theorem StrictStateRankAt_le_width
    (M : TuringMachine.DTM) (configContextRank : Nat -> Nat)
    (n : Nat) (input : Fin n -> Bool) (t : Nat) :
    StrictStateRankAt M configContextRank n input t <=
      StrictTrajectoryWidth M configContextRank n := by
  classical
  unfold StrictStateRankAt StrictTrajectoryWidth
  by_cases hn : n >= 1
  · by_cases ht : t < TuringMachine.timeSteps M n + 1
    · rw [dif_pos hn, dif_pos ht, dif_pos hn]
      let tf : Fin (TuringMachine.timeSteps M n + 1) := ⟨t, ht⟩
      have htime :
          strictRankAtFin M configContextRank n hn input tf <=
            Finset.univ.sup (fun tf' : Fin (TuringMachine.timeSteps M n + 1) =>
              strictRankAtFin M configContextRank n hn input tf') := by
        exact Finset.le_sup (s := Finset.univ)
          (f := fun tf' : Fin (TuringMachine.timeSteps M n + 1) =>
            strictRankAtFin M configContextRank n hn input tf')
          (b := tf) (hb := by simp)
      have hinput :
          Finset.univ.sup (fun tf' : Fin (TuringMachine.timeSteps M n + 1) =>
            strictRankAtFin M configContextRank n hn input tf') <=
            Finset.univ.sup (fun input' : Fin n -> Bool =>
              Finset.univ.sup (fun tf' : Fin (TuringMachine.timeSteps M n + 1) =>
                strictRankAtFin M configContextRank n hn input' tf')) := by
        exact Finset.le_sup (s := Finset.univ)
          (f := fun input' : Fin n -> Bool =>
            Finset.univ.sup (fun tf' : Fin (TuringMachine.timeSteps M n + 1) =>
              strictRankAtFin M configContextRank n hn input' tf'))
          (b := input) (hb := by simp)
      simpa [strictRankAtFin, tf] using le_trans htime hinput
    · rw [dif_pos hn, dif_neg ht, dif_pos hn]
      exact Nat.zero_le _
  · rw [dif_neg hn, dif_neg hn]

noncomputable def strictFaithfulTrajectoryObserver
    (M : TuringMachine.DTM) (configContextRank : Nat -> Nat) :
    TrajectoryObserverMachine where
  width := StrictTrajectoryWidth M configContextRank
  acceptsInput := fun n input =>
    if hn : n >= 1 then TuringMachine.accepts M n hn input else False
  stateCode := fun n input t =>
    if hn : n >= 1 then
      let cfg := TuringMachine.run M n t (TuringMachine.initialConfig M n hn input)
      strictConfigCode M cfg
    else
      0
  liveBoundaryRank := StrictStateRankAt M configContextRank
  liveBoundaryRank_le_width := StrictStateRankAt_le_width M configContextRank

def StrictFaithfulSATObserverClass
    (enc : ThreeCNFEncoding) (T : TrajectoryObserverMachine) : Prop :=
  ∃ M : TuringMachine.DTM, ∃ configContextRank : Nat -> Nat,
    DTMDecidesSATWithEncoding enc M /\
      T = strictFaithfulTrajectoryObserver M configContextRank

end PallLean.Paper93.DeepMath.PathB
