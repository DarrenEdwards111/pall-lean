import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameReceivedWordRadiusBarrier

/-!
# Hamming-sphere capacity endpoint

List decoding is not needed to obtain the universal capacity bound.  An
injective code maps every semantic message in a received-word list into the
ambient Boolean Hamming ball around that word.  Hence every solver-induced cell
has at most the maximum ambient ball size.

This isolates the quantitative alternative.  If the relevant ambient balls are
polynomial, a polynomial cell quotient is impossible.  If the radius is the
full block length, the ambient capacity is exactly `2^N`, so the statement is
vacuous.  Code structure can improve the ambient bound only through a genuine
list-decoding theorem; it still cannot create the solver/cell proximity map.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameHammingSphereCapacityEndpoint

open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameConflictHypergraphCapacityEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameExpanderListRecoveryEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordListDecodingBridge
open PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordRadiusBarrier

/-! ## Ambient Boolean balls -/

/-- The length-`N` Boolean Hamming ball around `received`. -/
noncomputable def ambientHammingBall
    {N : Nat} (received : Assignment N) (R : Nat) :
    Finset (Assignment N) := by
  classical
  exact (Finset.univ : Finset (Assignment N)).filter
    (fun word => hammingDistance received word <= R)

/-- Maximum size of a radius-`R` ball over all Boolean centres. -/
noncomputable def hammingSphereCapacity (N R : Nat) : Nat := by
  classical
  exact (Finset.univ : Finset (Assignment N)).sup
    (fun received => (ambientHammingBall received R).card)

/-- Every particular ball is bounded by the maximum sphere capacity. -/
theorem ambientHammingBall_card_le_capacity
    {N R : Nat} (received : Assignment N) :
    (ambientHammingBall received R).card <= hammingSphereCapacity N R := by
  classical
  unfold hammingSphereCapacity
  exact Finset.le_sup (f := fun center => (ambientHammingBall center R).card)
    (Finset.mem_univ received)

/-- Injectivity embeds a semantic message ball into its ambient codeword ball. -/
theorem messageBall_card_le_ambientHammingBall
    {m N R : Nat} (C : RedundantContinuationCode m N)
    (received : Assignment N) :
    (messageBall C received R).card <=
      (ambientHammingBall received R).card := by
  classical
  apply Finset.card_le_card_of_injOn C.encode
  · intro a ha
    have hnear : hammingDistance received (C.encode a) <= R :=
      (Finset.mem_filter.mp ha).2
    unfold ambientHammingBall
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnear⟩
  · intro a _ b _ hab
    exact C.injective hab

/-- Every injective code is automatically list decodable with the ambient
sphere capacity as its list bound. -/
theorem hammingListDecodable_ambientCapacity
    {m N R : Nat} (C : RedundantContinuationCode m N) :
    HammingListDecodable C R (hammingSphereCapacity N R) := by
  intro received
  exact (messageBall_card_le_ambientHammingBall C received).trans
    (ambientHammingBall_card_le_capacity received)

/-! ## Exact full-radius calibration -/

/-- At radius `N`, every Boolean word belongs to every ambient ball. -/
theorem ambientHammingBall_length_eq_univ
    {N : Nat} (received : Assignment N) :
    ambientHammingBall received N = Finset.univ := by
  classical
  unfold ambientHammingBall
  apply Finset.filter_eq_self.mpr
  intro word _
  exact hammingDistance_le_length _ _

/-- The full-radius sphere capacity is exactly the entire encoded cube. -/
theorem hammingSphereCapacity_length (N : Nat) :
    hammingSphereCapacity N N = 2 ^ N := by
  classical
  apply Nat.le_antisymm
  · unfold hammingSphereCapacity
    apply Finset.sup_le
    intro received _
    calc
      (ambientHammingBall received N).card
          <= (Finset.univ : Finset (Assignment N)).card := by
        exact Finset.card_le_card (Finset.filter_subset _ _)
      _ = 2 ^ N := by simp
  · let received : Assignment N := fun _ => false
    calc
      2 ^ N = (ambientHammingBall received N).card := by
        rw [ambientHammingBall_length_eq_univ]
        simp
      _ <= hammingSphereCapacity N N :=
        ambientHammingBall_card_le_capacity received

/-! ## Cell capacity and the exponential count -/

/-- A received-word projection bounds every exact cell fibre by the maximum
ambient Hamming-ball capacity. -/
theorem receivedWordProjection_to_fiberCapacity
    {m N R : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (P : CellReceivedWordProjection C cellOf R) :
    FiberCapacityAtMost cellOf (hammingSphereCapacity N R) := by
  let L := listRecoveryOfReceivedWords C cellOf
    (hammingListDecodable_ambientCapacity C) P
  exact L.toFiberCapacity

/-- Sphere capacity gives the unconditional cells-times-ball-size count. -/
theorem assignment_card_le_cells_mul_hammingSphereCapacity
    {m N R : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (P : CellReceivedWordProjection C cellOf R) :
    2 ^ m <= Fintype.card Cell * hammingSphereCapacity N R :=
  assignment_card_le_cell_card_mul_capacity cellOf
    (receivedWordProjection_to_fiberCapacity C cellOf P)

/-- Polynomially many cells and polynomial ambient sphere capacity contradict
the semantic continuation cube beyond the exponential gap. -/
theorem no_polynomial_cells_and_hammingSphereCapacity
    {m N R k d : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (P : CellReceivedWordProjection C cellOf R)
    (hcells : Fintype.card Cell <= m ^ k)
    (hball : hammingSphereCapacity N R <= m ^ d)
    (hgap : m ^ (k + d) < 2 ^ m) : False := by
  have hcount := assignment_card_le_cells_mul_hammingSphereCapacity C cellOf P
  have hpoly : Fintype.card Cell * hammingSphereCapacity N R <= m ^ (k + d) := by
    calc
      Fintype.card Cell * hammingSphereCapacity N R
          <= m ^ k * m ^ d := Nat.mul_le_mul hcells hball
      _ = m ^ (k + d) := by rw [pow_add]
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameHammingSphereCapacityEndpoint

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameHammingSphereCapacityEndpoint.messageBall_card_le_ambientHammingBall
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameHammingSphereCapacityEndpoint.hammingListDecodable_ambientCapacity
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameHammingSphereCapacityEndpoint.hammingSphereCapacity_length
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameHammingSphereCapacityEndpoint.assignment_card_le_cells_mul_hammingSphereCapacity
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameHammingSphereCapacityEndpoint.no_polynomial_cells_and_hammingSphereCapacity
