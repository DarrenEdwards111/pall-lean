import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameConflictHypergraphCapacityEndpoint

/-!
# Ramanujan/local expansion does not imply continuation-fibre capacity

The conflict-hypergraph endpoint reduced the desired amplituhedron lower bound to
a polynomial bound on every cell fibre.  This file tests whether ordinary local
Ramanujan geometry can supply that bound.

It cannot.  Parity separates every one-bit continuation edge, and more generally
every edge in any bipartite/parity-crossing subgraph.  Nevertheless each of its
two cells contains exactly `2^(m-1)` continuation labels.  Thus arbitrarily strong
local expansion can coexist with exponential monochromatic fibres.

The missing input is consequently higher-order: SAT correctness must bound the
number of mutually compatible continuation labels inside one solver-induced cell.
Spectral expansion or edge separation alone does not provide that law.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameRamanujanFiberCapacityBarrier

open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameLocalChargeChromaticBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameConflictHypergraphCapacityEndpoint

/-! ## Exact size of the parity cells -/

/-- For positive dimension, the true-parity cell contains exactly half of the
Boolean cube. -/
theorem parityLocalCharge_true_fiber_card
    {m : Nat} (hm : 1 <= m) :
    ((Finset.univ : Finset (Assignment m)).filter
      (fun a => parityLocalCharge a = true)).card = 2 ^ (m - 1) := by
  classical
  let i0 : Fin m := ⟨0, hm⟩
  let flip0 : Assignment m -> Assignment m := fun a => flipAssignment a i0
  have flip0_involutive : forall a, flip0 (flip0 a) = a := by
    intro a
    funext j
    by_cases hj : j = i0
    · subst j
      simp [flip0, flipAssignment]
    · simp [flip0, flipAssignment, Function.update_of_ne hj]
  have flip0_injective : Function.Injective flip0 := by
    intro a b hab
    have h := congrArg flip0 hab
    simpa [flip0_involutive] using h
  have himage :
      (Finset.univ : Finset (Assignment m)).filter
          (fun a => parityLocalCharge a = false) =
        ((Finset.univ : Finset (Assignment m)).filter
          (fun a => parityLocalCharge a = true)).image flip0 := by
    ext a
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ha
      refine ⟨flip0 a, ?_, flip0_involutive a⟩
      simp [flip0, parityLocalCharge_flip, ha]
    · rintro ⟨b, hb, rfl⟩
      simp [flip0, parityLocalCharge_flip, hb]
  have hequal :
      ((Finset.univ : Finset (Assignment m)).filter
        (fun a => parityLocalCharge a = false)).card =
      ((Finset.univ : Finset (Assignment m)).filter
        (fun a => parityLocalCharge a = true)).card := by
    rw [himage, Finset.card_image_of_injective _ flip0_injective]
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Assignment m)))
    (fun a => parityLocalCharge a = true)
  have hnot :
      (Finset.univ : Finset (Assignment m)).filter
          (fun a => ¬ parityLocalCharge a = true) =
        (Finset.univ : Finset (Assignment m)).filter
          (fun a => parityLocalCharge a = false) := by
    apply Finset.filter_congr
    intro a _
    simp [Bool.not_eq_true]
  rw [hnot, hequal] at hsum
  have huniv : (Finset.univ : Finset (Assignment m)).card = 2 ^ m := by
    simp
  rw [huniv] at hsum
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    ring
  omega

/-- The false-parity cell has the same exact half-cube size. -/
theorem parityLocalCharge_false_fiber_card
    {m : Nat} (hm : 1 <= m) :
    ((Finset.univ : Finset (Assignment m)).filter
      (fun a => parityLocalCharge a = false)).card = 2 ^ (m - 1) := by
  classical
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Assignment m)))
    (fun a => parityLocalCharge a = true)
  have hnot :
      (Finset.univ : Finset (Assignment m)).filter
          (fun a => ¬ parityLocalCharge a = true) =
        (Finset.univ : Finset (Assignment m)).filter
          (fun a => parityLocalCharge a = false) := by
    apply Finset.filter_congr
    intro a _
    simp [Bool.not_eq_true]
  rw [hnot, parityLocalCharge_true_fiber_card hm] at hsum
  have huniv : (Finset.univ : Finset (Assignment m)).card = 2 ^ m := by
    simp
  rw [huniv] at hsum
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    ring
  omega

/-- Both cells of the parity quotient have exponential cardinality. -/
theorem parityLocalCharge_fiber_card
    {m : Nat} (hm : 1 <= m) (c : Bool) :
    ((Finset.univ : Finset (Assignment m)).filter
      (fun a => parityLocalCharge a = c)).card = 2 ^ (m - 1) := by
  cases c
  · exact parityLocalCharge_false_fiber_card hm
  · exact parityLocalCharge_true_fiber_card hm

/-! ## Local expansion is orthogonal to fibre capacity -/

/-- Any graph whose edges cross the parity bipartition is perfectly separated by
the two-valued parity action.  No expansion parameter is needed. -/
def ParityCrossingGeometry {m : Nat}
    (edge : Assignment m -> Assignment m -> Prop) : Prop :=
  forall a b, edge a b -> parityLocalCharge a ≠ parityLocalCharge b

theorem parityLocalCharge_separates_parityCrossingGeometry
    {m : Nat} {edge : Assignment m -> Assignment m -> Prop}
    (hcross : ParityCrossingGeometry edge) :
    EdgeSeparated edge (parityLocalCharge (m := m)) :=
  hcross

/-- If the requested fibre bound is below half the cube, parity refutes it even
though parity separates every local continuation edge. -/
theorem parityLocalCharge_not_fiberCapacity_below_half
    {m r : Nat} (hm : 1 <= m) (hr : r < 2 ^ (m - 1)) :
    ¬ FiberCapacityAtMost (parityLocalCharge : Assignment m -> Bool) r := by
  intro hcap
  have htrue := hcap true
  rw [parityLocalCharge_true_fiber_card hm] at htrue
  omega

/-- Concrete endpoint: at width four the local continuation geometry is perfectly
two-coloured, but a linear fibre bound already fails (`8 > 4`). -/
theorem hypercube_local_separation_with_large_fiber :
    EdgeSeparated (HypercubeEdge (m := 4))
        (parityLocalCharge : Assignment 4 -> Bool) ∧
      ¬ FiberCapacityAtMost
        (parityLocalCharge : Assignment 4 -> Bool) 4 := by
  refine ⟨parityLocalCharge_edgeSeparated 4, ?_⟩
  exact parityLocalCharge_not_fiberCapacity_below_half (by norm_num) (by norm_num)

/-- Therefore no generic theorem can promote local continuation-edge separation
to even a linear higher-order fibre bound. -/
theorem no_localSeparation_to_linearFiberCapacity :
    ¬ (forall m : Nat, 1 <= m ->
      forall cellOf : Assignment m -> Bool,
        EdgeSeparated (HypercubeEdge (m := m)) cellOf ->
          FiberCapacityAtMost cellOf m) := by
  intro H
  exact hypercube_local_separation_with_large_fiber.2
    (H 4 (by norm_num) parityLocalCharge
      hypercube_local_separation_with_large_fiber.1)

end PallLean.Paper93.DeepMath.PathB.NFrameRamanujanFiberCapacityBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRamanujanFiberCapacityBarrier.parityLocalCharge_fiber_card
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRamanujanFiberCapacityBarrier.parityLocalCharge_separates_parityCrossingGeometry
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRamanujanFiberCapacityBarrier.hypercube_local_separation_with_large_fiber
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRamanujanFiberCapacityBarrier.no_localSeparation_to_linearFiberCapacity
