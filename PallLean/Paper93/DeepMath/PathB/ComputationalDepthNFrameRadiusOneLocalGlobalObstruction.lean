import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameRadiusOneCenterObstruction

/-!
# Radius-one local-to-global obstruction

The parity-triple obstruction is stronger than a pairwise-diameter counterexample.
Every three of its four codewords have a common radius-one centre, but the full
four-word set does not.  Hence even exact common-centre consistency on every
triple in a cell does not assemble into one cell-wide received word.

This is the finite local-to-global gap relevant to expander-style arguments.
Local checks may provide different centres on different small subfamilies.  A
received-word projection requires one coherent centre for the entire semantic
fibre, and that gluing statement is additional information.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalGlobalObstruction

open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordListDecodingBridge
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneCenterObstruction

/-! ## Local and global centre compatibility -/

/-- Every triple of semantic messages lying in one cell has some common
radius-`R` encoded centre.  The centre may depend on the triple. -/
def CellTriplewiseRadiusCompatible
    {m N R : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell) : Prop :=
  forall a b c : Assignment m,
    cellOf a = cellOf b -> cellOf b = cellOf c ->
    ∃ received : Assignment N,
      hammingDistance received (C.encode a) <= R ∧
      hammingDistance received (C.encode b) <= R ∧
      hammingDistance received (C.encode c) <= R

/-- A genuine cell received-word projection implies triplewise compatibility
by reusing the one centre assigned to the whole cell. -/
theorem projection_to_triplewise
    {m N R : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (P : CellReceivedWordProjection C cellOf R) :
    CellTriplewiseRadiusCompatible C cellOf (R := R) := by
  intro a b c hab hbc
  refine ⟨P.received (cellOf a), P.trueCodewordNear a, ?_, ?_⟩
  · simpa [hab] using P.trueCodewordNear b
  · have hac : cellOf a = cellOf c := hab.trans hbc
    simpa [hac] using P.trueCodewordNear c

/-! ## Every triple of parity words has a centre -/

/-- Any three messages in the two-bit semantic cube, including triples with
repetitions, have parity-triple codewords inside one radius-one ball. -/
theorem every_parityTriple_three_have_radiusOne_center
    (a b c : Assignment 2) :
    ∃ received : Assignment 3,
      hammingDistance received (parityTripleCode.encode a) <= 1 ∧
      hammingDistance received (parityTripleCode.encode b) <= 1 ∧
      hammingDistance received (parityTripleCode.encode c) <= 1 := by
  rcases assignment_two_cases a with ha | ha | ha | ha <;>
    rcases assignment_two_cases b with hb | hb | hb | hb <;>
    rcases assignment_two_cases c with hc | hc | hc | hc <;>
    subst a <;> subst b <;> subst c <;> decide

/-- The one-cell parity-triple quotient is triplewise radius-one compatible. -/
theorem constantCell_triplewise_radiusOne :
    CellTriplewiseRadiusCompatible parityTripleCode constantCell (R := 1) := by
  intro a b c _ _
  exact every_parityTriple_three_have_radiusOne_center a b c

/-! ## Failed local-to-global gluing -/

/-- Exact counterexample: all triplewise common-centre tests pass, yet there is
no cell-wide radius-one received-word projection. -/
theorem triplewise_radiusOne_does_not_imply_projection :
    CellTriplewiseRadiusCompatible parityTripleCode constantCell (R := 1) ∧
      ¬ Nonempty
        (CellReceivedWordProjection parityTripleCode constantCell 1) :=
  ⟨constantCell_triplewise_radiusOne,
    no_radiusOneProjection_parityTriple_constantCell⟩

/-- Therefore the universal implication from triplewise radius-one consistency
to a global cell received word is false. -/
theorem no_universal_triplewise_to_projection :
    ¬ (forall {m N : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
        (C : RedundantContinuationCode m N)
        (cellOf : Assignment m -> Cell),
        CellTriplewiseRadiusCompatible C cellOf (R := 1) ->
        Nonempty (CellReceivedWordProjection C cellOf 1)) := by
  intro h
  exact no_radiusOneProjection_parityTriple_constantCell
    (h parityTripleCode constantCell constantCell_triplewise_radiusOne)

end PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalGlobalObstruction

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalGlobalObstruction.projection_to_triplewise
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalGlobalObstruction.every_parityTriple_three_have_radiusOne_center
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalGlobalObstruction.constantCell_triplewise_radiusOne
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalGlobalObstruction.triplewise_radiusOne_does_not_imply_projection
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalGlobalObstruction.no_universal_triplewise_to_projection
