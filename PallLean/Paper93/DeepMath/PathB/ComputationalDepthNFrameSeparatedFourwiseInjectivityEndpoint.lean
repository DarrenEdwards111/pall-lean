import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSolverFourwiseRadiusOneEndpoint

/-!
# Separated-code fourwise law equals cell injectivity

For a continuation code of minimum distance at least three, the radius-one
four-label law has no residual coding-theoretic content.  Repeating two labels
in a four-tuple gives a common radius-one centre for their codewords, so their
distance is at most two.  Code separation then forces the labels to be equal.

Conversely, an injective cell map makes every same-cell four-tuple constant and
its codeword itself is a radius-zero, hence radius-one, centre.  Thus fourwise
compatibility, pairwise compatibility, and cell injectivity are equivalent.

This identifies the surviving semantic theorem for a genuinely separated
expander code: correctness must force the amplituhedron cell map to preserve the
entire continuation label injectively.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameSeparatedFourwiseInjectivityEndpoint

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordListDecodingBridge
open PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordRadiusBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneDistanceBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalityThreshold
open PallLean.Paper93.DeepMath.PathB.NFrameSolverFourwiseRadiusOneEndpoint

/-! ## Pairwise centre compatibility -/

/-- Every two semantic messages in one cell have codewords sharing some
radius-one centre. -/
def CellPairwiseRadiusOneCompatible
    {m N : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell) : Prop :=
  forall a b : Assignment m, cellOf a = cellOf b ->
    ∃ received : Assignment N,
      hammingDistance received (C.encode a) <= 1 ∧
      hammingDistance received (C.encode b) <= 1

/-- Fourwise compatibility includes pairwise compatibility by repetition. -/
theorem fourwise_to_pairwise
    {m N : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (hfour : CellFourwiseRadiusCompatible C cellOf (R := 1)) :
    CellPairwiseRadiusOneCompatible C cellOf := by
  intro a b hab
  obtain ⟨received, ha, hb, _, _⟩ :=
    hfour a b a b hab hab.symm hab
  exact ⟨received, ha, hb⟩

/-- With minimum distance three, even the pairwise common-centre condition
forces the cell map to be injective. -/
theorem cellOf_injective_of_pairwise_and_distanceThree
    {m N : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (hpair : CellPairwiseRadiusOneCompatible C cellOf)
    (hsep : MinimumDistanceAtLeastThree C) :
    Function.Injective cellOf := by
  intro a b hab
  by_contra hne
  obtain ⟨received, ha, hb⟩ := hpair a b hab
  have htri := hammingDistance_triangle
    (C.encode a) received (C.encode b)
  rw [hammingDistance_comm (C.encode a) received] at htri
  have hnear : hammingDistance (C.encode a) (C.encode b) <= 2 := by omega
  have hfar := hsep a b hne
  omega

/-- If the cell map is injective, every same-cell four-tuple is constant and
therefore has its codeword as a common radius-one centre. -/
theorem fourwise_of_cellOf_injective
    {m N : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (hinj : Function.Injective cellOf) :
    CellFourwiseRadiusCompatible C cellOf (R := 1) := by
  intro a b c d hab hbc hcd
  have hab' : a = b := hinj hab
  have hbc' : b = c := hinj hbc
  have hcd' : c = d := hinj hcd
  subst b
  subst c
  subst d
  refine ⟨C.encode a, ?_⟩
  have hzero : hammingDistance (C.encode a) (C.encode a) = 0 :=
    hammingDistance_eq_zero_iff.mpr rfl
  omega

/-! ## Exact calibration -/

/-- For a distance-three code, the four-label law is exactly cell injectivity. -/
theorem fourwise_iff_cellOf_injective_of_distanceThree
    {m N : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (hsep : MinimumDistanceAtLeastThree C) :
    CellFourwiseRadiusCompatible C cellOf (R := 1) ↔
      Function.Injective cellOf := by
  constructor
  · intro hfour
    exact cellOf_injective_of_pairwise_and_distanceThree C cellOf
      (fourwise_to_pairwise C cellOf hfour) hsep
  · exact fourwise_of_cellOf_injective C cellOf

/-- Pairwise and fourwise centre compatibility coincide under distance three,
because both are equivalent to injectivity. -/
theorem pairwise_iff_fourwise_of_distanceThree
    {m N : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (hsep : MinimumDistanceAtLeastThree C) :
    CellPairwiseRadiusOneCompatible C cellOf ↔
      CellFourwiseRadiusCompatible C cellOf (R := 1) := by
  constructor
  · intro hpair
    exact fourwise_of_cellOf_injective C cellOf
      (cellOf_injective_of_pairwise_and_distanceThree C cellOf hpair hsep)
  · exact fourwise_to_pairwise C cellOf

/-- Consequently the correctness-derived four-label law is exactly the claim
that correctness makes the solver-induced cell map injective. -/
theorem decides_fourwise_iff_decides_cellInjective
    {U : MachineModel} {D : DecisionMachine U}
    {m N : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (hsep : MinimumDistanceAtLeastThree C) :
    (DecidesSAT U D ->
      CellFourwiseRadiusCompatible C cellOf (R := 1)) ↔
    (DecidesSAT U D -> Function.Injective cellOf) := by
  constructor
  · intro hfour hD
    exact (fourwise_iff_cellOf_injective_of_distanceThree C cellOf hsep).mp
      (hfour hD)
  · intro hinj hD
    exact (fourwise_iff_cellOf_injective_of_distanceThree C cellOf hsep).mpr
      (hinj hD)

/-! ## Direct exponential cell-count consequence -/

/-- A distance-three fourwise law requires at least `2^m` cells directly,
without constructing a decoder or using encoded block length. -/
theorem two_pow_le_cell_card_of_fourwise_distanceThree
    {m N : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (hfour : CellFourwiseRadiusCompatible C cellOf (R := 1))
    (hsep : MinimumDistanceAtLeastThree C) :
    2 ^ m <= Fintype.card Cell := by
  have hinj :=
    (fourwise_iff_cellOf_injective_of_distanceThree C cellOf hsep).mp hfour
  have hcard := Fintype.card_le_of_injective cellOf hinj
  simpa using hcard

/-- The separated solver bundle's semantic field can therefore be read
literally as correctness-derived injectivity. -/
theorem separatedBundle_fourwiseField_iff_injectiveField
    {U : MachineModel} {D : DecisionMachine U}
    (B : SolverSeparatedFourwiseRadiusOneFor U D) :
    (DecidesSAT U D ->
      @CellFourwiseRadiusCompatible B.m B.N 1 B.Cell B.cellDecidableEq
        B.code B.cellOf) ↔
    (DecidesSAT U D -> Function.Injective B.cellOf) := by
  letI : DecidableEq B.Cell := B.cellDecidableEq
  exact decides_fourwise_iff_decides_cellInjective
    B.code B.cellOf B.codeDistanceThree

end PallLean.Paper93.DeepMath.PathB.NFrameSeparatedFourwiseInjectivityEndpoint

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSeparatedFourwiseInjectivityEndpoint.fourwise_to_pairwise
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSeparatedFourwiseInjectivityEndpoint.cellOf_injective_of_pairwise_and_distanceThree
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSeparatedFourwiseInjectivityEndpoint.fourwise_iff_cellOf_injective_of_distanceThree
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSeparatedFourwiseInjectivityEndpoint.decides_fourwise_iff_decides_cellInjective
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSeparatedFourwiseInjectivityEndpoint.two_pow_le_cell_card_of_fourwise_distanceThree
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSeparatedFourwiseInjectivityEndpoint.separatedBundle_fourwiseField_iff_injectiveField
