import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameRadiusOneLocalGlobalObstruction

/-!
# Radius-one locality threshold

The parity-triple cell passes every common-centre test involving at most three
semantic messages, but the four distinct messages together expose the failure.
This file packages that strict arity gap.

The result is deliberately one-sided.  It proves that locality three is too
weak and that four is the first arity capable of detecting this obstruction; it
does not assume or claim that four-local consistency is sufficient for arbitrary
codes and fibres.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalityThreshold

open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordListDecodingBridge
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneCenterObstruction
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalGlobalObstruction

/-! ## Four-local centre compatibility -/

/-- Every four semantic messages in one cell have a common radius-`R` encoded
centre.  Repetitions are permitted, so this condition includes all lower
arities. -/
def CellFourwiseRadiusCompatible
    {m N R : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell) : Prop :=
  forall a b c d : Assignment m,
    cellOf a = cellOf b -> cellOf b = cellOf c -> cellOf c = cellOf d ->
    ∃ received : Assignment N,
      hammingDistance received (C.encode a) <= R ∧
      hammingDistance received (C.encode b) <= R ∧
      hammingDistance received (C.encode c) <= R ∧
      hammingDistance received (C.encode d) <= R

/-- A genuine cell received word passes every four-local test. -/
theorem projection_to_fourwise
    {m N R : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (P : CellReceivedWordProjection C cellOf R) :
    CellFourwiseRadiusCompatible C cellOf (R := R) := by
  intro a b c d hab hbc hcd
  refine ⟨P.received (cellOf a), P.trueCodewordNear a, ?_, ?_, ?_⟩
  · simpa [hab] using P.trueCodewordNear b
  · have hac : cellOf a = cellOf c := hab.trans hbc
    simpa [hac] using P.trueCodewordNear c
  · have had : cellOf a = cellOf d := hab.trans (hbc.trans hcd)
    simpa [had] using P.trueCodewordNear d

/-! ## The first detected obstruction has arity four -/

/-- The four distinct parity-triple messages have no common radius-one centre. -/
theorem parityTriple_four_message_obstruction :
    ¬ ∃ received : Assignment 3,
      hammingDistance received (parityTripleCode.encode msg00) <= 1 ∧
      hammingDistance received (parityTripleCode.encode msg01) <= 1 ∧
      hammingDistance received (parityTripleCode.encode msg10) <= 1 ∧
      hammingDistance received (parityTripleCode.encode msg11) <= 1 := by
  intro h
  apply no_common_radiusOne_center
  obtain ⟨received, h00, h01, h10, h11⟩ := h
  refine ⟨received, ?_⟩
  intro a
  rcases assignment_two_cases a with ha | ha | ha | ha
  · simpa [ha] using h00
  · simpa [ha] using h01
  · simpa [ha] using h10
  · simpa [ha] using h11

/-- Therefore the constant parity-triple cell fails four-local radius-one
compatibility. -/
theorem constantCell_not_fourwise_radiusOne :
    ¬ CellFourwiseRadiusCompatible parityTripleCode constantCell (R := 1) := by
  intro hfour
  apply parityTriple_four_message_obstruction
  exact hfour msg00 msg01 msg10 msg11 rfl rfl rfl

/-- Strict locality threshold for the concrete code/cell system: every triple
passes, while one four-message family fails. -/
theorem radiusOne_three_vs_four_strict_gap :
    CellTriplewiseRadiusCompatible parityTripleCode constantCell (R := 1) ∧
      ¬ CellFourwiseRadiusCompatible parityTripleCode constantCell (R := 1) :=
  ⟨constantCell_triplewise_radiusOne, constantCell_not_fourwise_radiusOne⟩

/-- Hence triplewise common-centre consistency cannot universally imply even
fourwise consistency, before asking for a centre coherent on the whole fibre. -/
theorem no_universal_triplewise_to_fourwise :
    ¬ (forall {m N : Nat} {Cell : Type} [DecidableEq Cell]
        (C : RedundantContinuationCode m N)
        (cellOf : Assignment m -> Cell),
        CellTriplewiseRadiusCompatible C cellOf (R := 1) ->
        CellFourwiseRadiusCompatible C cellOf (R := 1)) := by
  intro h
  exact constantCell_not_fourwise_radiusOne
    (h parityTripleCode constantCell constantCell_triplewise_radiusOne)

end PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalityThreshold

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalityThreshold.projection_to_fourwise
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalityThreshold.parityTriple_four_message_obstruction
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalityThreshold.constantCell_not_fourwise_radiusOne
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalityThreshold.radiusOne_three_vs_four_strict_gap
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalityThreshold.no_universal_triplewise_to_fourwise
