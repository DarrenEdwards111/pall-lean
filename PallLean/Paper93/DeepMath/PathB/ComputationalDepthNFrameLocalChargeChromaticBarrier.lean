import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameContinuationTranscriptEndpoint
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameKhrapchenko

/-!
# N-frame local-charge chromatic barrier

The complete continuation charge is SAT-relevant but has exponential range.  A
natural next attempt is to retain only a weaker local action: distinguish the
Ramanujan/self-reduction transitions that differ by one branch bit, while allowing
unrelated labels to merge into polynomially many amplituhedron cells.

This file proves the exact obstruction to that move.  Local edge separation is a
graph-colouring condition, not global label preservation.  On the Boolean cube,
ordinary parity distinguishes every single-bit transition using only two charge
values, yet it merges exponentially many labels.  More abstractly, the side map of
any bipartite graph separates every edge with two colours, independently of any
spectral expansion property.

Thus a Ramanujan edge-energy conservation theorem cannot by itself recover the
complete fooling-label law.  The missing hard statement must prove that the
solver-relevant conflict graph has superpolynomial chromatic number (the complete
fooling relation gives `2^m`), not merely many edges or strong expansion.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameLocalChargeChromaticBarrier

open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ## Local edge separation is only colouring -/

/-- A charge separates the endpoints of every edge in a relevance relation. -/
def EdgeSeparated {Vertex Charge : Type}
    (edge : Vertex -> Vertex -> Prop) (charge : Vertex -> Charge) : Prop :=
  forall x y, edge x y -> charge x ≠ charge y

/-- Every bipartite relevance graph has a two-valued edge-separating charge:
its side bit.  Expansion, degree, and graph size do not enter the proof. -/
theorem bipartite_side_is_edgeSeparated
    {Vertex : Type} (edge : Vertex -> Vertex -> Prop) (side : Vertex -> Bool)
    (hcross : forall x y, edge x y -> side x ≠ side y) :
    EdgeSeparated edge side :=
  hcross

/-! ## Concrete hypercube counterexample -/

/-- Flip one continuation/orientation coordinate. -/
def flipAssignment {m : Nat} (a : Assignment m) (i : Fin m) : Assignment m :=
  Function.update a i (!(a i))

/-- The local continuation graph joins assignments differing by one bit. -/
def HypercubeEdge {m : Nat} (a b : Assignment m) : Prop :=
  exists i : Fin m, b = flipAssignment a i

/-- A two-valued local N-frame charge: parity of the oriented branch bits. -/
def parityLocalCharge {m : Nat} (a : Assignment m) : Bool :=
  parityFn m a

/-- Flipping any one continuation coordinate toggles the parity charge. -/
theorem parityLocalCharge_flip
    {m : Nat} (a : Assignment m) (i : Fin m) :
    parityLocalCharge (flipAssignment a i) = !(parityLocalCharge a) := by
  exact parity_flip a i

/-- Hence parity separates every local hypercube transition. -/
theorem parityLocalCharge_edgeSeparated (m : Nat) :
    EdgeSeparated (HypercubeEdge (m := m))
      (parityLocalCharge (m := m)) := by
  intro a b hab
  obtain ⟨i, rfl⟩ := hab
  rw [parityLocalCharge_flip]
  cases parityLocalCharge a <;> simp

/-- Its complete charge range nevertheless contains only two values. -/
theorem parityLocalCharge_range_card : Fintype.card Bool = 2 := by
  simp

/-- In dimension two, no Boolean-valued charge can preserve all four labels. -/
theorem no_bool_charge_globally_injective_dim_two
    (charge : Assignment 2 -> Bool) :
    ¬ Function.Injective charge := by
  exact small_boundary_not_residual_distinguishing charge (by norm_num)

/-- In particular, the locally perfect parity charge is not globally
label-separating. -/
theorem parityLocalCharge_not_globally_injective_dim_two :
    ¬ Function.Injective (parityLocalCharge : Assignment 2 -> Bool) :=
  no_bool_charge_globally_injective_dim_two parityLocalCharge

/-- The generic promotion from local edge separation to full fooling-label
injectivity is therefore false already on the two-dimensional cube. -/
theorem no_localEdgeSeparation_to_globalInjectivity :
    ¬ (forall charge : Assignment 2 -> Bool,
        EdgeSeparated (HypercubeEdge (m := 2)) charge ->
          Function.Injective charge) := by
  intro H
  exact parityLocalCharge_not_globally_injective_dim_two
    (H parityLocalCharge (parityLocalCharge_edgeSeparated 2))

/-- The local parity action has polynomial range at every width at least two. -/
theorem parityLocalCharge_has_polynomial_range
    (m : Nat) (hm : 2 <= m) :
    Fintype.card Bool <= m ^ 1 := by
  simp
  omega

/-- Combined endpoint: at every width at least two there is a polynomial-range
charge separating every single-bit continuation edge; at width two this same
construction provably fails global label preservation. -/
theorem local_separation_with_small_range_does_not_force_global :
    (EdgeSeparated (HypercubeEdge (m := 2))
        (parityLocalCharge : Assignment 2 -> Bool)) ∧
    (Fintype.card Bool <= 2 ^ 1) ∧
    ¬ Function.Injective (parityLocalCharge : Assignment 2 -> Bool) := by
  exact ⟨parityLocalCharge_edgeSeparated 2,
    parityLocalCharge_has_polynomial_range 2 (by norm_num),
    parityLocalCharge_not_globally_injective_dim_two⟩

end PallLean.Paper93.DeepMath.PathB.NFrameLocalChargeChromaticBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameLocalChargeChromaticBarrier.bipartite_side_is_edgeSeparated
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameLocalChargeChromaticBarrier.parityLocalCharge_edgeSeparated
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameLocalChargeChromaticBarrier.no_localEdgeSeparation_to_globalInjectivity
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameLocalChargeChromaticBarrier.local_separation_with_small_range_does_not_force_global
