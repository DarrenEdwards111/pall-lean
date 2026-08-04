import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameHammingSphereCapacityEndpoint

/-!
# Radius-one Hamming sphere endpoint

The first useful received-word regime is radius one.  A length-`N` Boolean word
within distance one of a centre is determined by a disagreement set of size at
most one.  There are at most `N + 1` such sets: the empty set and the `N`
singletons.

This file proves that bound directly and feeds it into the sphere-capacity
endpoint.  Thus radius-one proximity plus polynomially many solver cells already
gives the exponential contradiction.  The remaining issue is not sphere
combinatorics; it is deriving radius-one proximity from SAT correctness.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneSphereEndpoint

open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordListDecodingBridge
open PallLean.Paper93.DeepMath.PathB.NFrameHammingSphereCapacityEndpoint

/-! ## Disagreement-set encoding -/

/-- Coordinates on which a word disagrees with a fixed centre. -/
def disagreementSet
    {N : Nat} (received word : Assignment N) : Finset (Fin N) :=
  (Finset.univ : Finset (Fin N)).filter (fun i => received i ≠ word i)

/-- Words are determined by their disagreement set from a fixed Boolean centre. -/
theorem disagreementSet_injective
    {N : Nat} (received : Assignment N) :
    Function.Injective (disagreementSet received) := by
  intro x y hsets
  apply funext
  intro i
  have hmem : i ∈ disagreementSet received x ↔
      i ∈ disagreementSet received y := by rw [hsets]
  simp only [disagreementSet, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  cases hr : received i <;> cases hx : x i <;> cases hy : y i <;>
    simp [hr, hx, hy] at hmem ⊢

/-- Finite coordinate subsets of size at most `R`. -/
def lowCardSubsets (N R : Nat) : Finset (Finset (Fin N)) :=
  (Finset.univ : Finset (Finset (Fin N))).filter (fun s => s.card <= R)

/-- A radius-`R` ambient ball injects into coordinate subsets of size at most
`R`. -/
theorem ambientHammingBall_card_le_lowCardSubsets
    {N R : Nat} (received : Assignment N) :
    (ambientHammingBall received R).card <= (lowCardSubsets N R).card := by
  classical
  apply Finset.card_le_card_of_injOn (disagreementSet received)
  · intro word hword
    have hnear : hammingDistance received word <= R :=
      (Finset.mem_filter.mp hword).2
    simpa [lowCardSubsets, disagreementSet, hammingDistance] using hnear
  · intro x _ y _ hxy
    exact disagreementSet_injective received hxy

/-! ## Counting empty and singleton disagreement sets -/

/-- Subsets of size at most one are exactly the union of the zero- and
one-element powerset layers. -/
theorem lowCardSubsets_one_eq
    (N : Nat) :
    lowCardSubsets N 1 =
      (Finset.univ : Finset (Fin N)).powersetCard 0 ∪
      (Finset.univ : Finset (Fin N)).powersetCard 1 := by
  classical
  ext s
  simp only [lowCardSubsets, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_powersetCard]
  constructor
  · intro hs
    have hcard : s.card = 0 ∨ s.card = 1 := by omega
    rcases hcard with hzero | hone
    · exact Or.inl ⟨Finset.subset_univ _, hzero⟩
    · exact Or.inr ⟨Finset.subset_univ _, hone⟩
  · rintro (⟨_, hzero⟩ | ⟨_, hone⟩)
    · omega
    · omega

/-- There are at most `N + 1` coordinate subsets of size at most one. -/
theorem lowCardSubsets_one_card_le
    (N : Nat) : (lowCardSubsets N 1).card <= N + 1 := by
  classical
  rw [lowCardSubsets_one_eq]
  calc
    ((Finset.univ : Finset (Fin N)).powersetCard 0 ∪
        (Finset.univ : Finset (Fin N)).powersetCard 1).card
        <= ((Finset.univ : Finset (Fin N)).powersetCard 0).card +
          ((Finset.univ : Finset (Fin N)).powersetCard 1).card :=
      Finset.card_union_le _ _
    _ = N + 1 := by
      rw [Finset.card_powersetCard, Finset.card_powersetCard]
      simp
      omega

/-- Every radius-one ambient Boolean sphere has at most `N + 1` words. -/
theorem ambientHammingBall_one_card_le
    {N : Nat} (received : Assignment N) :
    (ambientHammingBall received 1).card <= N + 1 :=
  (ambientHammingBall_card_le_lowCardSubsets received).trans
    (lowCardSubsets_one_card_le N)

/-- The maximum radius-one sphere capacity is at most `N + 1`. -/
theorem hammingSphereCapacity_one_le
    (N : Nat) : hammingSphereCapacity N 1 <= N + 1 := by
  classical
  unfold hammingSphereCapacity
  apply Finset.sup_le
  intro received _
  exact ambientHammingBall_one_card_le received

/-! ## Radius-one compression contradiction -/

/-- Radius-one proximity, polynomially many cells, and a polynomial bound on
`N + 1` cannot cover the semantic continuation cube past the exponential gap. -/
theorem no_polynomial_cells_with_radiusOneProjection
    {m N k d : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (P : CellReceivedWordProjection C cellOf 1)
    (hcells : Fintype.card Cell <= m ^ k)
    (hlength : N + 1 <= m ^ d)
    (hgap : m ^ (k + d) < 2 ^ m) : False :=
  no_polynomial_cells_and_hammingSphereCapacity C cellOf P hcells
    ((hammingSphereCapacity_one_le N).trans hlength) hgap

end PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneSphereEndpoint

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneSphereEndpoint.disagreementSet_injective
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneSphereEndpoint.ambientHammingBall_card_le_lowCardSubsets
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneSphereEndpoint.lowCardSubsets_one_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneSphereEndpoint.hammingSphereCapacity_one_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneSphereEndpoint.no_polynomial_cells_with_radiusOneProjection
