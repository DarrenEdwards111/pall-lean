import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameRadiusOneSphereEndpoint

/-!
# Radius-one minimum-distance barrier

The radius-one sphere bound gives the universal estimate `N + 1` without using
any property of the continuation code.  A genuinely separated code makes the
semantic requirement much stronger.  Two codewords assigned to one cell are
both within distance one of the cell's received word, and hence are within
distance two of each other.

Consequently every collision of the solver-induced cell map is a concrete
certificate that the code has two distinct codewords at distance at most two.
If the code has minimum distance at least three, a radius-one received-word
projection already forces the cell map to be injective.  The cells must then
number at least `2^m`; no polynomial cell quotient survives.  Thus expander-code
distance does not help derive the missing semantic projection: in the first
useful radius regime it upgrades that projection to complete preservation of
the semantic continuation label.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneDistanceBarrier

open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordListDecodingBridge
open PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordRadiusBarrier

/-! ## Collision certificates -/

/-- Two semantic messages collapsed into one radius-one cell have codewords at
Hamming distance at most two. -/
theorem codeword_distance_le_two_of_same_radiusOne_cell
    {m N : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (P : CellReceivedWordProjection C cellOf 1)
    {a b : Assignment m} (hab : cellOf a = cellOf b) :
    hammingDistance (C.encode a) (C.encode b) <= 2 := by
  have h := codeword_distance_le_two_mul_radius C cellOf P hab
  norm_num at h ⊢
  exact h

/-- Any failure of cell injectivity under a radius-one projection exposes two
distinct semantic messages whose codewords are at distance at most two. -/
theorem close_codeword_witness_of_not_cellOf_injective
    {m N : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (P : CellReceivedWordProjection C cellOf 1)
    (hnot : ¬ Function.Injective cellOf) :
    ∃ a b : Assignment m,
      a ≠ b ∧ cellOf a = cellOf b ∧
        hammingDistance (C.encode a) (C.encode b) <= 2 := by
  rw [Function.Injective] at hnot
  push_neg at hnot
  obtain ⟨a, b, hab, hne⟩ := hnot
  exact ⟨a, b, hne, hab,
    codeword_distance_le_two_of_same_radiusOne_cell C cellOf P hab⟩

/-! ## Distance three forces complete semantic preservation -/

/-- Minimum code distance at least three, stated without subtraction or an
explicit minimum operator. -/
def MinimumDistanceAtLeastThree
    {m N : Nat} (C : RedundantContinuationCode m N) : Prop :=
  forall a b : Assignment m, a ≠ b ->
    3 <= hammingDistance (C.encode a) (C.encode b)

/-- The distance-three formulation is exactly the existing strict-above-two
condition. -/
theorem minimumDistanceAtLeastThree_iff_above_two
    {m N : Nat} (C : RedundantContinuationCode m N) :
    MinimumDistanceAtLeastThree C ↔ MinimumDistanceAbove C 2 := by
  constructor <;> intro h a b hab
  · have := h a b hab
    omega
  · have := h a b hab
    omega

/-- With minimum distance at least three, radius-one proximity makes the
solver-induced cell map injective. -/
theorem cellOf_injective_of_radiusOne_and_distanceThree
    {m N : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (P : CellReceivedWordProjection C cellOf 1)
    (hsep : MinimumDistanceAtLeastThree C) :
    Function.Injective cellOf := by
  rw [minimumDistanceAtLeastThree_iff_above_two] at hsep
  have h := cellOf_injective_of_minDistanceAbove_two_mul C cellOf P
  norm_num at h
  exact h hsep

/-! ## Cell-count endpoint -/

/-- A distance-three radius-one projection requires at least one distinct cell
for each of the `2^m` semantic continuation messages. -/
theorem two_pow_le_cell_card_of_radiusOne_and_distanceThree
    {m N : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (P : CellReceivedWordProjection C cellOf 1)
    (hsep : MinimumDistanceAtLeastThree C) :
    2 ^ m <= Fintype.card Cell := by
  have hinj := cellOf_injective_of_radiusOne_and_distanceThree C cellOf P hsep
  have hcard := Fintype.card_le_of_injective cellOf hinj
  simpa using hcard

/-- Therefore no cell space smaller than the semantic cube can support both a
distance-three code and a radius-one received-word projection. -/
theorem no_small_cells_with_radiusOne_and_distanceThree
    {m N : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (P : CellReceivedWordProjection C cellOf 1)
    (hsep : MinimumDistanceAtLeastThree C)
    (hsmall : Fintype.card Cell < 2 ^ m) : False := by
  have := two_pow_le_cell_card_of_radiusOne_and_distanceThree C cellOf P hsep
  omega

/-- Polynomially many cells are impossible past the usual exponential gap.
Unlike the ambient sphere argument, this conclusion does not depend on the
encoded block length `N`: distance three has already forced singleton fibres. -/
theorem no_polynomial_cells_with_radiusOne_and_distanceThree
    {m N k : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (P : CellReceivedWordProjection C cellOf 1)
    (hsep : MinimumDistanceAtLeastThree C)
    (hcells : Fintype.card Cell <= m ^ k)
    (hgap : m ^ k < 2 ^ m) : False := by
  apply no_small_cells_with_radiusOne_and_distanceThree C cellOf P hsep
  exact lt_of_le_of_lt hcells hgap

end PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneDistanceBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneDistanceBarrier.codeword_distance_le_two_of_same_radiusOne_cell
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneDistanceBarrier.close_codeword_witness_of_not_cellOf_injective
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneDistanceBarrier.minimumDistanceAtLeastThree_iff_above_two
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneDistanceBarrier.cellOf_injective_of_radiusOne_and_distanceThree
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneDistanceBarrier.two_pow_le_cell_card_of_radiusOne_and_distanceThree
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneDistanceBarrier.no_polynomial_cells_with_radiusOne_and_distanceThree
