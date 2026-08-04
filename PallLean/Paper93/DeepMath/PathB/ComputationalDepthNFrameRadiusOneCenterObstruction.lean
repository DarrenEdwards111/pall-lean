import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameRadiusOneDistanceBarrier

/-!
# Radius-one centre obstruction

The radius barrier proves a necessary condition for a received-word projection:
all codewords in one radius-one cell have pairwise distance at most two.  This
file shows that the condition is not sufficient.

The four even-parity words of length three are pairwise at distance at most two,
but no Boolean word is within distance one of all four.  Encoding the two-bit
semantic cube as those words and collapsing it to one cell therefore gives a
concrete code/cell system with diameter two and no radius-one received-word
projection.

Thus a prospective geometric argument cannot stop at a codeword-diameter bound.
It must construct a common cell-correlated Hamming centre, a strictly stronger
semantic statement.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneCenterObstruction

open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordListDecodingBridge
open PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordRadiusBarrier

/-! ## A concrete even-parity continuation code -/

/-- Encode two semantic bits as the length-three even-parity word
`(x, y, x xor y)`. -/
def parityTripleEncode (a : Assignment 2) : Assignment 3 :=
  ![a 0, a 1, Bool.xor (a 0) (a 1)]

/-- The parity-triple encoding is injective because its first two coordinates
are the original semantic message. -/
theorem parityTripleEncode_injective : Function.Injective parityTripleEncode := by
  intro a b hab
  funext i
  fin_cases i
  · simpa [parityTripleEncode] using congrFun hab (0 : Fin 3)
  · simpa [parityTripleEncode] using congrFun hab (1 : Fin 3)

/-- The concrete redundant continuation code used by the obstruction. -/
def parityTripleCode : RedundantContinuationCode 2 3 where
  encode := parityTripleEncode
  injective := parityTripleEncode_injective

/-- Collapse all four semantic messages into one cell. -/
def constantCell (_ : Assignment 2) : Unit := ()

def msg00 : Assignment 2 := ![false, false]
def msg01 : Assignment 2 := ![false, true]
def msg10 : Assignment 2 := ![true, false]
def msg11 : Assignment 2 := ![true, true]

/-- The four named messages exhaust the two-bit semantic cube. -/
theorem assignment_two_cases (a : Assignment 2) :
    a = msg00 ∨ a = msg01 ∨ a = msg10 ∨ a = msg11 := by
  cases ha0 : a 0 <;> cases ha1 : a 1
  · left
    funext i
    fin_cases i <;> simp [msg00, ha0, ha1]
  · right; left
    funext i
    fin_cases i <;> simp [msg01, ha0, ha1]
  · right; right; left
    funext i
    fin_cases i <;> simp [msg10, ha0, ha1]
  · right; right; right
    funext i
    fin_cases i <;> simp [msg11, ha0, ha1]

/-! ## Diameter two -/

/-- Uniform codeword-diameter bound inside exact cells. -/
def CellCodewordDiameterAtMost
    {m N D : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell) : Prop :=
  forall a b : Assignment m, cellOf a = cellOf b ->
    hammingDistance (C.encode a) (C.encode b) <= D

/-- Every pair of parity-triple codewords has Hamming distance at most two. -/
theorem parityTriple_distance_le_two (a b : Assignment 2) :
    hammingDistance (parityTripleCode.encode a)
      (parityTripleCode.encode b) <= 2 := by
  rcases assignment_two_cases a with ha | ha | ha | ha <;>
    rcases assignment_two_cases b with hb | hb | hb | hb <;>
    subst a <;> subst b <;> decide

/-- Hence the one-cell quotient satisfies the strongest pairwise condition
that radius-one proximity could imply. -/
theorem constantCell_diameter_two :
    CellCodewordDiameterAtMost parityTripleCode constantCell (D := 2) := by
  intro a b _
  exact parityTriple_distance_le_two a b

/-! ## No common radius-one centre -/

/-- No length-three Boolean word is within distance one of all four even-parity
codewords. -/
theorem no_common_radiusOne_center :
    ¬ ∃ received : Assignment 3,
      (forall a : Assignment 2,
        hammingDistance received (parityTripleCode.encode a) <= 1) := by
  rintro ⟨received, hnear⟩
  have h00 := hnear msg00
  have h01 := hnear msg01
  have h10 := hnear msg10
  have h11 := hnear msg11
  cases hr0 : received 0 <;> cases hr1 : received 1 <;>
    cases hr2 : received 2
  · have hr : received = ![false, false, false] := by
      funext i; fin_cases i <;> simp [hr0, hr1, hr2]
    subst received
    have hfar : ¬ hammingDistance (![false, false, false] : Assignment 3)
        (parityTripleCode.encode msg01) <= 1 := by decide
    exact hfar h01
  · have hr : received = ![false, false, true] := by
      funext i; fin_cases i <;> simp [hr0, hr1, hr2]
    subst received
    have hfar : ¬ hammingDistance (![false, false, true] : Assignment 3)
        (parityTripleCode.encode msg11) <= 1 := by decide
    exact hfar h11
  · have hr : received = ![false, true, false] := by
      funext i; fin_cases i <;> simp [hr0, hr1, hr2]
    subst received
    have hfar : ¬ hammingDistance (![false, true, false] : Assignment 3)
        (parityTripleCode.encode msg10) <= 1 := by decide
    exact hfar h10
  · have hr : received = ![false, true, true] := by
      funext i; fin_cases i <;> simp [hr0, hr1, hr2]
    subst received
    have hfar : ¬ hammingDistance (![false, true, true] : Assignment 3)
        (parityTripleCode.encode msg00) <= 1 := by decide
    exact hfar h00
  · have hr : received = ![true, false, false] := by
      funext i; fin_cases i <;> simp [hr0, hr1, hr2]
    subst received
    have hfar : ¬ hammingDistance (![true, false, false] : Assignment 3)
        (parityTripleCode.encode msg01) <= 1 := by decide
    exact hfar h01
  · have hr : received = ![true, false, true] := by
      funext i; fin_cases i <;> simp [hr0, hr1, hr2]
    subst received
    have hfar : ¬ hammingDistance (![true, false, true] : Assignment 3)
        (parityTripleCode.encode msg00) <= 1 := by decide
    exact hfar h00
  · have hr : received = ![true, true, false] := by
      funext i; fin_cases i <;> simp [hr0, hr1, hr2]
    subst received
    have hfar : ¬ hammingDistance (![true, true, false] : Assignment 3)
        (parityTripleCode.encode msg00) <= 1 := by decide
    exact hfar h00
  · have hr : received = ![true, true, true] := by
      funext i; fin_cases i <;> simp [hr0, hr1, hr2]
    subst received
    have hfar : ¬ hammingDistance (![true, true, true] : Assignment 3)
        (parityTripleCode.encode msg00) <= 1 := by decide
    exact hfar h00

/-- The constant cell map therefore admits no radius-one received-word
projection. -/
theorem no_radiusOneProjection_parityTriple_constantCell :
    ¬ Nonempty
      (CellReceivedWordProjection parityTripleCode constantCell 1) := by
  rintro ⟨P⟩
  apply no_common_radiusOne_center
  exact ⟨P.received (), fun a => P.trueCodewordNear a⟩

/-! ## Exact failed converse -/

/-- Pairwise cell diameter at most two does not imply the existence of a
radius-one cell-correlated received word, even for an injective redundant code
on the full semantic cube. -/
theorem diameterTwo_does_not_imply_radiusOneProjection :
    CellCodewordDiameterAtMost parityTripleCode constantCell (D := 2) ∧
      ¬ Nonempty
        (CellReceivedWordProjection parityTripleCode constantCell 1) :=
  ⟨constantCell_diameter_two,
    no_radiusOneProjection_parityTriple_constantCell⟩

end PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneCenterObstruction

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneCenterObstruction.parityTripleEncode_injective
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneCenterObstruction.parityTriple_distance_le_two
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneCenterObstruction.no_common_radiusOne_center
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneCenterObstruction.no_radiusOneProjection_parityTriple_constantCell
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneCenterObstruction.diameterTwo_does_not_imply_radiusOneProjection
